{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import ChoreoTokenize (alexScanTokens)
import ChoreoParser
import LocalPretty
import ExampleAlgebra
import Local
import Choreo
import Translate
import Frame
import ProVerif
import ExamplePVT
import Term
import ProVerifPrinter
import ProtocolSetup (protocolSetup)
import qualified SAPIC
import qualified SAPICPrinter
import System.Environment (getArgs)
import System.Exit (exitSuccess)
import System.IO (stdin, hGetContents, hPutStrLn, stderr, hIsTerminalDevice)
import System.Process (system)
import Control.Monad (unless, forM, forM_, when)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Control.Monad.Trans.State as State
import qualified Control.Monad.Trans.State (State)
import qualified Data.Bifunctor as Bifunctor
import Data.List (intercalate, nub, isSuffixOf)
import qualified Data.Char
import Util (cast)
import Text.PrettyPrint (render)

createContext :: ([String], ([(String,[String],[String])],[(String,[String],[String])]), [String], [Agent String String], Map.Map (Agent String String) (Set.Set (Term String String)), Map.Map String [String], [([(String,String)],PVFormula)],InitialChoreo String String)
             -> Context
createContext (types, (pubFuncs, privFuncs), cells, agents, knowledge, events, queries, _) =
    Context {
        types = types,
        privateFunctions = privFuncs,
        publicFunctions = pubFuncs,
        cells = cells,
        agents = agents,
        knowledge = knowledge,
        events = events,
        queries = queries
    }


-- | Pretty print a failure for user-friendly error messages
prettyFailure :: (Show f, Show v) => Failure String f v -> String
prettyFailure Unknown = "Unknown translation error"
prettyFailure (Translate.Other msg) = "Translation error: " ++ msg
prettyFailure (IllDefinedChor contexts) = 
    "Ill-defined choreography section:\n" ++ 
    unlines (zipWith formatContext [1..] contexts)
  where
    formatContext :: (Show f, Show v) => Int -> (Frame String f v, ChoreoUnion f v) -> String
    formatContext n (frame, choreo) = 
        "  Context " ++ show n ++ ":\n" ++
        "    In choreography: " ++ formatChoreoUnion choreo
    
    formatChoreoUnion :: (Show f, Show v) => ChoreoUnion f v -> String
    formatChoreoUnion (CUChoreo choreo) = formatChoreo choreo
    formatChoreoUnion (CUAtomic agent atomic) = show agent ++ ": " ++ formatAtomic atomic
    formatChoreoUnion (CUWrites agent writes) = show agent ++ ": " ++ formatWrites writes
    
    formatChoreo :: (Show f, Show v) => Choreo f v -> String
    formatChoreo End = "End"
    formatChoreo (Send from to msg _) = show from ++ " → " ++ show to
    formatChoreo (Atomic agent _) = show agent ++ ": atomic section"
    
    formatAtomic :: (Show f, Show v) => Atomic f v -> String
    formatAtomic (Nonce v ts _) = "nonce " ++ show v
    formatAtomic (Choreo.Event name terms _) = "event " ++ name ++ "(" ++ intercalate ", " (map show terms) ++ ")"
    formatAtomic (Choice atomics) = "choice [" ++ intercalate " | " (map formatAtomic atomics) ++ "]"
    formatAtomic (Branch t1 t2 _ _) = "if " ++ show t1 ++ " = " ++ show t2
    formatAtomic (Choreo.Read name addr val _) = "read " ++ name ++ "[" ++ show addr ++ "] as " ++ show val
    formatAtomic (Writes w) = formatWrites w
    
    formatWrites :: (Show f, Show v) => Writes f v -> String
    formatWrites (Choreo.Write name addr val _) = "write " ++ name ++ "[" ++ show addr ++ "] := " ++ show val
    formatWrites (Choreo c) = "continue with: " ++ formatChoreo c

prettyFailure (MultiFailure failures) = 
    "Multiple translation errors:\n" ++ 
    unlines (zipWith formatFailure [1..] failures)
  where
    formatFailure n f = "  Error " ++ show n ++ ": " ++ indent "    " (prettyFailure f)
    indent prefix str = unlines [if i == 0 then line else prefix ++ line | (i, line) <- zip [0..] (lines str)]

prettyFailure (RecipeSynthesisFailed contexts) = 
    "Recipe synthesis failed:\n" ++
    "  Could not synthesize the following terms from the frame:\n" ++
    unlines (map formatContext contexts)
  where
    formatContext (frame, term) = 
        "    Term: " ++ renderTerm term ++ "\n" ++
        "    Available in frame:\n" ++ formatFrameEntries frame
    
    formatFrameEntries frame = 
        let entries = Map.toList (Frame.frameForward frame)
        in if null entries 
           then "      (empty frame)"
           else unlines ["      " ++ renderTerm t | (_, t) <- entries]
    
    renderTerm t = stripQuotes $ render (ppTerm (mapf show (mapv show t)))
    
    -- Remove quotes around string literals
    stripQuotes s = filter (/= '"') s

-- | Pretty print translation result
printTranslationResult :: Bool -> Agent String String -> TranslateResult String Func String (a,Local Func String) -> IO ()
printTranslationResult filterNoops agent result = do
    putStrLn $ "\n" ++ replicate 50 '='
    putStrLn $ "Local behavior for agent: " ++ show agent
    putStrLn $ replicate 50 '='
    case result of
        TR (Left err) -> putStrLn $ prettyFailure err
        TR (Right (_,local)) -> do
            let processedLocal = if filterNoops then removeNoopLocal local else local
            putStrLn $ renderLocal show id processedLocal


-- | Parse command line arguments
parseArgs :: [String] -> Either String (Maybe String, Bool, Maybe String, Maybe String, Bool, MemoryModel, Maybe String, Bool)
parseArgs args = go args Nothing False Nothing Nothing False WithAxioms Nothing False
  where
    go [] choreo filter proverif stitch runpv mm sapic sanity = Right (choreo, filter, proverif, stitch, runpv, mm, sapic, sanity)
    go ("--help" : _) _ _ _ _ _ _ _ _ = Left "HELP"
    go ("-h" : _) _ _ _ _ _ _ _ _ = Left "HELP"
    -- go ("--filter" : rest) choreo _ proverif stitch runpv mm sapic sanity = go rest choreo True proverif stitch runpv mm sapic sanity
    go ("--proverif" : rest) choreo filter _ stitch runpv mm sapic sanity = go rest choreo filter (Just []) stitch runpv mm sapic sanity
    go ("--pvout" : filename : rest) choreo filter _ stitch runpv mm sapic sanity = go rest choreo filter (Just filename) stitch runpv mm sapic sanity
    go ("--sapic" : rest) choreo filter proverif stitch runpv mm _ sanity = go rest choreo filter proverif stitch runpv mm (Just []) sanity
    go ("--sapicout" : filename : rest) choreo filter proverif stitch runpv mm _ sanity = go rest choreo filter proverif stitch runpv mm (Just filename) sanity
    go ("--sanity" : rest) choreo filter proverif stitch runpv mm sapic _ = go rest choreo filter proverif stitch runpv mm sapic True
    go ("--stitch" : spec : rest) choreo filter proverif _ runpv mm sapic sanity = go rest choreo filter proverif (Just spec) runpv mm sapic sanity
    go ("--runproverif" : rest) choreo filter proverif stitch _ mm sapic sanity = go rest choreo filter proverif stitch True mm sapic sanity
    go ("--memorymodel" : "withaxioms" : rest) choreo filter proverif stitch runpv _ sapic sanity = go rest choreo filter proverif stitch runpv WithAxioms sapic sanity
    go ("--memorymodel" : "noaxioms"  : rest) choreo filter proverif stitch runpv _ sapic sanity = go rest choreo filter proverif stitch runpv NoAxioms  sapic sanity
    go ("--memorymodel" : model : _) _ _ _ _ _ _ _ _ = Left $ "Invalid memory model: " ++ model ++ ". Use 'withaxioms' or 'noaxioms'."
    go (filename : rest) Nothing filter proverif stitch runpv mm sapic sanity = go rest (Just filename) filter proverif stitch runpv mm sapic sanity
    go _ _ _ _ _ _ _ _ _ = Left "Invalid arguments"


instance NameGenerator (Set String, Int) String where
    fresh = do
        ng <- State.get
        let n' = uncurry findFresh ng
        let s = "l" ++ show n'
        State.put (Set.insert s (fst ng), n' + 1)
        return s
      where
        findFresh ng n =
            if Set.member ("l" ++ show n) ng
            then findFresh ng (n + 1)
            else n
    isFresh ng name = Set.member name (fst ng)
    register ng name = Bifunctor.first (Set.insert name) ng

-- | Empty name generator state.
emptyNG :: (Set String, Int)
emptyNG = (Set.empty, 0)


convertAgent :: Agent String v -> Agent Func v
convertAgent (Trusted s) =
    case stringToFunc s of
        Just s' -> Trusted s'
        _ -> error ("Failed to convert function name in " ++ show s)
convertAgent (Untrusted s) = Untrusted s

-- | Convert a Term String to Term Func using ExampleAlgebra function symbols.
convertTerm :: Show v => Term String v -> Term Func v
convertTerm t =
    case mapfM stringToFunc t of
        Just t' -> t'
        _ -> error ("Failed to convert function name in " ++ show t)

-- | Convert Atomic String to Atomic Func using ExampleAlgebra function symbols.
convertAtomic :: (Show v) => Atomic String v
              -> Atomic Func v
convertAtomic a =
    case mapfMAtomic stringToFunc a of
        Just a' -> a'
        _ -> error ("Failed to convert function name in " ++ show a)

-- | Convert InitialAtomic String to InitialAtomic Func
convertInitialAtomic :: (Show v) => InitialAtomic String v -> InitialAtomic Func v
convertInitialAtomic (INonce v ts a) = INonce v (map convertTerm ts) (convertInitialAtomic a)
convertInitialAtomic (ILet2 v t a) = ILet2 v (convertTerm t) (convertInitialAtomic a)
convertInitialAtomic (IChoice as) = IChoice (map convertInitialAtomic as)
convertInitialAtomic (IEvent name ts a) = IEvent name (map convertTerm ts) (convertInitialAtomic a)
convertInitialAtomic (IBranch t1 t2 a1 a2) = IBranch (convertTerm t1) (convertTerm t2) (convertInitialAtomic a1) (convertInitialAtomic a2)
convertInitialAtomic (IRead name t1 t2 a) = IRead name (convertTerm t1) (convertTerm t2) (convertInitialAtomic a)
convertInitialAtomic (IWrites w) = IWrites (convertInitialWrites w)

-- | Convert InitialWrites String to InitialWrites Func
convertInitialWrites :: (Show v) => InitialWrites String v -> InitialWrites Func v
convertInitialWrites (IWrite name t1 t2 w) = IWrite name (convertTerm t1) (convertTerm t2) (convertInitialWrites w)
convertInitialWrites (IChoreo c) = IChoreo (convertInitialChoreo c)

-- | Convert InitialChoreo String to InitialChoreo Func using ExampleAlgebra function symbols.
convertInitialChoreo :: (Show v) => InitialChoreo String v -> InitialChoreo Func v
convertInitialChoreo (IEnd goals) = IEnd $ convertGoals goals
convertInitialChoreo (ISend a1 a2 t c) = ISend (convertAgent a1) (convertAgent a2) (convertTerm t) (convertInitialChoreo c)
convertInitialChoreo (IAtomic a at) = IAtomic (convertAgent a) $ convertInitialAtomic at
convertInitialChoreo (ILet1 v t c) = ILet1 v (convertTerm t) (convertInitialChoreo c)

-- | Convert Goals String to Goals Func
convertGoals :: (Show v) => Goals String v -> Goals Func v
convertGoals EndGoals = EndGoals
convertGoals (Secret agents t rest) = Secret (map convertAgent agents) (convertTerm t) (convertGoals rest)
convertGoals (WeakAuth a1 a2 t rest) = WeakAuth (convertAgent a1) (convertAgent a2) (convertTerm t) (convertGoals rest)
convertGoals (StrongAuth a1 a2 t rest) = StrongAuth (convertAgent a1) (convertAgent a2) (convertTerm t) (convertGoals rest)

-- | Convert and stringify PVFormula terms
-- First converts String -> Func -> String using algebra, then stringifies with termToPV
stringifyPVFormula :: [Term Func String] -> PVFormula -> PVFormula
stringifyPVFormula agentTerms formula = case formula of
    PVEvent name terms -> PVEvent name (map (termToPV agentTerms . convertTerm) terms)
    PVInjEvent name terms -> PVInjEvent name (map (termToPV agentTerms . convertTerm) terms)
    PVAttacker term -> PVAttacker (termToPV agentTerms $ convertTerm term)
    PVEq t1 t2 -> PVEq (termToPV agentTerms $ convertTerm t1) (termToPV agentTerms $ convertTerm t2)
    PVNeq t1 t2 -> PVNeq (termToPV agentTerms $ convertTerm t1) (termToPV agentTerms $ convertTerm t2)
    PVAnd f1 f2 -> PVAnd (stringifyPVFormula agentTerms f1) (stringifyPVFormula agentTerms f2)
    PVImply f1 f2 -> PVImply (stringifyPVFormula agentTerms f1) (stringifyPVFormula agentTerms f2)

termToLabel :: Term String String -> String
termToLabel term = "l[" ++ termToString term ++ "]"
  where
    termToString (Var v) = v
    termToString (Fun f args) = f ++ "(" ++ intercalate ", " (map termToString args) ++ ")"

-- Parse stitch specification: "file1.choreo:agent1,agent2;file2.choreo:agent3,agent4"
-- Returns [(filename, [agents], isMain)]
-- Special agent name "main" indicates this file provides prelude and goals for final ProVerif
-- Agent name suffix [API] marks the agent as an API with baton synchronization
parseStitchSpec :: String -> Either String [(String, [(String, Bool)], Bool)]
parseStitchSpec spec = mapM parseFileSpec (splitOn ';' (filter (/= ' ') spec))
  where
    splitOn :: Char -> String -> [String]
    splitOn _ [] = []
    splitOn delim str = 
        let (part, rest) = break (== delim) str
        in part : case rest of
            [] -> []
            (_:rest') -> splitOn delim rest'
    
    parseAgentName :: String -> (String, Bool)
    parseAgentName name = 
        if "[API]" `isSuffixOf` name
        then (take (length name - 5) name, True)
        else (name, False)
    
    parseFileSpec :: String -> Either String (String, [(String, Bool)], Bool)
    parseFileSpec fileSpec = case break (== ':') fileSpec of
        (file, ':':agentStr) -> 
            let allNames = splitOn ',' agentStr
                isMain = "main" `elem` allNames
                agentNamesWithAPI = map parseAgentName (filter (/= "main") allNames)
            in Right (file, agentNamesWithAPI, isMain)
        _ -> Left $ "Invalid file specification: " ++ fileSpec

-- | Main program
main :: IO ()
main = do
    args <- getArgs

    -- Parse command line arguments
    (maybeFilename, filterNoops, maybeProverifOutput, maybeStitchSpec, runProverif, memoryModel, maybeSapicOutput, sanityFlag) <- case parseArgs args of
        Left "HELP" -> do
            putStrLn "CCHaskell - Choreography to ProVerif translator"
            putStrLn ""
            putStrLn "Usage: CCHaskell [OPTIONS] [filename]"
            putStrLn "       CCHaskell [OPTIONS] --stitch SPEC"
            putStrLn ""
            putStrLn "Options:"
            putStrLn "  -h, --help                  Show this help message"
            -- putStrLn "  --filter                    Filter no-op operations from output"
            putStrLn "  --proverif                  Generate ProVerif file and write to stdout"
            putStrLn "  --pvout FILENAME            Generate ProVerif file and write to FILENAME"
            putStrLn "  --stitch SPEC               Stitch roles from multiple files (no separate filename needed)"
            putStrLn "                              Format: file1:agent1,agent2;file2:agent3"
            putStrLn "                              Use 'main' to mark main file (provides prelude and goals)"
            putStrLn "                              Use '[API]' suffix to mark an agent as an API"
            putStrLn "  --runproverif               Automatically run proverif on generated file (requires --pvout)"
            putStrLn "  --sapic                     Generate SAPIC+ theory and write to stdout (experimental)"
            putStrLn "  --sapicout FILENAME         Generate SAPIC+ theory and write to FILENAME (experimental)"
            putStrLn "  --sanity                    Emit exists-trace sanity (executability) lemmas alongside the goals"
            putStrLn "  --memorymodel MODEL         Memory model: 'noaxioms' or 'withaxioms' (default)"
            putStrLn "  filename                    Input choreography file (omit if using --stitch or reading from stdin)"
            putStrLn ""
            putStrLn "Examples:"
            putStrLn "  CCHaskell protocol.choreo"
            putStrLn "  CCHaskell --pvout out.pv --runproverif protocol.choreo"
            putStrLn "  CCHaskell --pvout out.pv --stitch \"file1.choreo:main,alice;file2.choreo:tpm[API]\""
            exitSuccess
        Left err -> do
            hPutStrLn stderr $ "Error: " ++ err
            hPutStrLn stderr ""
            hPutStrLn stderr "Usage: CCHaskell [OPTIONS] [filename]"
            hPutStrLn stderr "Try 'CCHaskell --help' for more information."
            fail "Invalid arguments"
        Right result -> return result
    
    -- Determine file specifications and parse files
    (fileSpecs, parsedFiles) <- case maybeStitchSpec of
        Just stitchSpec -> do
            -- Stitch mode: parse specification
            specs <- case parseStitchSpec stitchSpec of
                Left err -> do
                    hPutStrLn stderr $ "Error parsing stitch specification: " ++ err
                    fail "Invalid stitch specification"
                Right specs -> return specs
            
            -- Parse each file
            parsed <- forM specs $ \(filename, agentNamesWithAPI, isMain) -> do
                input <- readFile filename
                let parsed = parseChoreo $ alexScanTokens input
                return (filename, agentNamesWithAPI, isMain, parsed)
            
            return (specs, parsed)
        
        Nothing -> do
            -- Normal mode: treat as single file with all agents
            (filename, input) <- case maybeFilename of
                Nothing -> do
                    isTTY <- hIsTerminalDevice stdin
                    when isTTY $ do
                        hPutStrLn stderr "Error: no input file given and stdin is a terminal."
                        hPutStrLn stderr "Pass a choreography filename, pipe input on stdin, or use --stitch."
                        hPutStrLn stderr "Try 'CCHaskell --help' for more information."
                        fail "No input provided"
                    input <- hGetContents stdin
                    when (all Data.Char.isSpace input) $ do
                        hPutStrLn stderr "Error: stdin produced no input."
                        hPutStrLn stderr "Pass a choreography filename, pipe input on stdin, or use --stitch."
                        fail "Empty input"
                    return ("<stdin>", input)
                Just filename -> do
                    input <- readFile filename
                    return (filename, input)
            
            let parsed = parseChoreo $ alexScanTokens input
                (_, _, _, agents, _, _, _, _) = parsed
                agentNamesWithAPI = map (\a -> (agentToString a, False)) agents
                specs = [(filename, agentNamesWithAPI, True)]
            
            return (specs, [(filename, agentNamesWithAPI, True, parsed)])
    
    -- Extract specified agents from parsed files
    stitchedData <- forM parsedFiles $ \(filename, agentNamesWithAPI, isMain, (types', functions', cells', agents, knowledge', events', queries', ichoreo)) -> do
        let agentNames = map fst agentNamesWithAPI
            requestedAgents = [agent | agent <- agents, agentToString agent `elem` agentNames]
            -- Build API status map
            apiStatusMap = Map.fromList agentNamesWithAPI
            requestedAgentsWithAPI = [(agent, Map.findWithDefault False (agentToString agent) apiStatusMap) | agent <- requestedAgents]
            -- Check if this non-main file has goals in its choreography
            (_, _, goalSet, secrecyGoals) = convertInitialChoreo ichoreo `firstPass` initialFPS
            hasGoals = not (null (fst goalSet) && null (snd goalSet) && null secrecyGoals)
        
        when (length requestedAgents /= length agentNames) $ do
            let foundNames = map agentToString requestedAgents
                missingNames = filter (`notElem` foundNames) agentNames
            hPutStrLn stderr $ "ERROR: agents " ++ show missingNames ++ " not found in " ++ filename
            fail "Specified agents do not exist in choreography file"
        
        -- Error if non-main file has goals
        when (not isMain && hasGoals) $ do
            hPutStrLn stderr $ "ERROR: File " ++ filename ++ " contains security goals but is not marked as 'main'"
            hPutStrLn stderr "Only the main file (marked with 'main') can contain security goals to avoid naming conflicts."
            fail "Non-main file contains security goals"
        
        return (types', functions', cells', requestedAgentsWithAPI, knowledge', events', queries', ichoreo, filename, isMain)
    
    -- Find which file is the main file (must have exactly one)
    let mainFiles = filter (\(_,_,_,_,_,_,_,_,_,isMain) -> isMain) stitchedData
    
    when (null mainFiles) $ do
        hPutStrLn stderr "ERROR: No file marked as 'main'"
        hPutStrLn stderr "In stitch mode, exactly one file must be marked with 'main' to provide prelude and security goals."
        hPutStrLn stderr "Example: --stitch \"file1.choreo:main,alice;file2.choreo:bob\""
        fail "No main file specified"
    
    when (length mainFiles > 1) $ do
        let fileNames = map (\(_,_,_,_,_,_,_,_,fname,_) -> fname) mainFiles
        hPutStrLn stderr $ "ERROR: Multiple files marked with 'main': " ++ show fileNames
        hPutStrLn stderr "Exactly one file must be marked as 'main'."
        fail "Multiple main files specified"
    
    let (mainTypes, mainFunctions, mainCells, _, _, mainEvents, mainQueries, _, mainFile, _) = head mainFiles
    
    -- Combine data: use prelude from main file, but agents and knowledge from all files
    let allPublicFuncs = ("memory_initial_value",[],[]) : fst mainFunctions
        allPrivateFuncs = snd mainFunctions
        allCells = mainCells
        allAgents = concatMap (\(_,_,_,agentsWithAPI,_,_,_,_,_,_) -> map fst agentsWithAPI) stitchedData
        allKnowledge = Map.unions $ map (\(_,_,_,_,k,_,_,_,_,_) -> k) stitchedData
        allEvents = mainEvents
        allQueries = mainQueries
    
    -- Translate each agent from their respective choreography
    translations <- forM stitchedData $ \(_, _, _, agentsWithAPI, knowledge', _, _, ichoreo, filename, _) -> do
        let (choreo, _, goalSet, secrecyGoals) = convertInitialChoreo ichoreo `firstPass` initialFPS
            
            knowledge agent = Map.findWithDefault Set.empty agent knowledge'
            frame agent = Set.foldr (\ t -> Map.insert (termToLabel t) (convertTerm t)) Map.empty (knowledge agent)
            initng agent = foldr (flip register) emptyNG (Map.keys (frame agent))
            
            result agent = translate (frame agent) choreo (initng agent) (convertAgent agent) (exAlg (Set.fromList $ map (\(f,xs,_) -> (f,length xs)) allPublicFuncs)) goalSet
        
        return $ map (\(agent, isAPI) -> (agent, result agent, frame agent, goalSet, secrecyGoals, filename, isAPI)) agentsWithAPI
    
    let allTranslations = concat translations
    
    -- Check if we should generate ProVerif or just print translations
    case maybeProverifOutput of
        Nothing
            -- If only SAPIC was requested, skip the IR dump.
            | Just _ <- maybeSapicOutput -> return ()
            | otherwise -> do
                -- No ProVerif/SAPIC output requested - print translation results
                forM_ allTranslations $ \(agent, result, _, _, _, _, _) ->
                    printTranslationResult filterNoops agent result
        
        Just outputFile -> do
            unless (null outputFile) $ do
                hPutStrLn stderr $ "\n" ++ replicate 50 '='
                hPutStrLn stderr "Generating ProVerif file..."
            
            -- Get all successful translations
            let successfulTranslations = [(agent, local, frame, goalSet, secrecyGoals, isAPI) | 
                    (agent, TR (Right (_,local)), frame, goalSet, secrecyGoals, _, isAPI) <- allTranslations]
                failedTranslations = [(agent, err, file) | 
                    (agent, TR (Left err), _, _, _, file, _) <- allTranslations]
            
            -- Report failures
            unless (null failedTranslations) $ do
                forM_ failedTranslations $ \(agent, err, file) -> do
                    hPutStrLn stderr $ "Error translating " ++ show agent ++ " from " ++ file ++ ": " ++ prettyFailure err
                hPutStrLn stderr "\nERROR: Translation failed for some agents"
                fail "ProVerif generation failed due to translation errors"
            
            unless (null successfulTranslations) $ do
                let (allWeakAuth, allStrongAuth) = foldl (\(w1,s1) (_,_,_,(w2,s2),_,_) -> (w1++w2, s1++s2)) ([],[]) successfulTranslations
                    allSecrecyGoals = nub $ concatMap (\(_,_,_,_,s,_) -> s) successfulTranslations
                    combinedGoalSet = (nub allWeakAuth, nub allStrongAuth)
                
                -- Determine which agents have parameters
                -- Parameters are untrusted agents that appear in this agent's initial knowledge
                let agentParameters = Map.fromList [(agent, getAgentParams agent allKnowledge allAgents) | agent <- allAgents]
                    
                    getAgentParams :: Agent String String -> Map (Agent String String) (Set (Term String String)) -> [Agent String String] -> [String]
                    getAgentParams agent knowledgeMap allAgentsList =
                        let knowledge = Map.findWithDefault Set.empty agent knowledgeMap
                        in nub $ concatMap (extractUntrustedAgentNamesFromTerm allAgentsList) (Set.toList knowledge)
                    
                    extractUntrustedAgentNamesFromTerm :: [Agent String String] -> Term String String -> [String]
                    extractUntrustedAgentNamesFromTerm agentNames (Var v) = 
                        if (Untrusted v) `elem` agentNames then [v] else []
                    extractUntrustedAgentNamesFromTerm agentNames (Fun _ args) = concatMap (extractUntrustedAgentNamesFromTerm agentNames) args
                
                -- Unfold knowledge and stringify
                let agentTerms = concatMap (\agent -> case agent of 
                                    Trusted f -> [Fun (ExampleAlgebra.Other f) [], Var f]
                                    Untrusted v -> [Fun (ExampleAlgebra.Other v) [], Var v]
                                 ) allAgents
                    stringifyTerm = termToPV agentTerms
                    stringifyAgent = \case
                        Trusted f -> Trusted (show f)
                        Untrusted s -> Untrusted s
                    
                    -- Stringify goal sets
                    stringifiedGoalSet =
                        let (weak, strong) = combinedGoalSet
                        in ([(n, stringifyAgent a1, stringifyAgent a2, stringifyTerm t) | (n, a1, a2, t) <- weak],
                            [(n, stringifyAgent a1, stringifyAgent a2, stringifyTerm t) | (n, a1, a2, t) <- strong])
                    stringifiedSecrecyGoals =
                        [(n, map stringifyTerm terms) | (n, terms) <- allSecrecyGoals]
                    
                    -- Stringify queries (convert terms through algebra)
                    stringifiedQueries = [(quantifiers, stringifyPVFormula (Fun (ExampleAlgebra.Other "i") [] : agentTerms) formula) | (quantifiers, formula) <- allQueries]
                    
                    stringifiedTranslations = [(agent, stringifyLocal agentTerms (unfoldLocalKnowledge frame local), isAPI) | 
                        (agent, local, frame, _, _, isAPI) <- successfulTranslations]
                    processes = map (\(agent, local, isAPI) -> (agent, localToProcess  memoryModel isAPI False local, isAPI)) stringifiedTranslations
                
                -- Generate combined ProVerif file
                let userDefinedFunctions = [(name, length inputTypes) | (name, inputTypes, _) <- allPublicFuncs ++ allPrivateFuncs]
                    pvCode = generateCompleteProVerifFileWithQueries 
                                memoryModel
                                protocolSetup 
                                allAgents 
                                processes
                                agentParameters
                                (Map.map Set.toList allKnowledge)
                                allCells
                                allEvents
                                stringifiedQueries
                                stringifiedGoalSet
                                stringifiedSecrecyGoals
                                userDefinedFunctions
                
                -- Write or print output
                if null outputFile
                    then putStrLn pvCode
                    else do
                        writeFile outputFile pvCode
                        hPutStrLn stderr $ "ProVerif file written to " ++ outputFile
                        hPutStrLn stderr $ "\n" ++ replicate 50 '='
                        hPutStrLn stderr "ProVerif generation complete!"
                        
                        -- Run proverif if requested
                        when runProverif $ do
                            hPutStrLn stderr $ "\n" ++ replicate 50 '='
                            hPutStrLn stderr $ "Running proverif on " ++ outputFile ++ "..."
                            hPutStrLn stderr $ replicate 50 '=' ++ "\n"
                            _ <- system $ "proverif " ++ outputFile
                            return ()

    -- Emit SAPIC+ theory if requested. Independent of --proverif: both backends
    -- can be requested in the same invocation.
    case maybeSapicOutput of
        Nothing -> return ()
        Just sapicOutFile -> do
            let successful = [(agent, local, frame, goalSet, secrecyGoals, isAPI) |
                    (agent, TR (Right (_,local)), frame, goalSet, secrecyGoals, _, isAPI) <- allTranslations]
                failures = [(agent, err, file) |
                    (agent, TR (Left err), _, _, _, file, _) <- allTranslations]
            unless (null failures) $ do
                forM_ failures $ \(agent, err, file) ->
                    hPutStrLn stderr $ "Error translating " ++ show agent ++ " from " ++ file ++ ": " ++ prettyFailure err
                hPutStrLn stderr "\nERROR: Translation failed for some agents"
                fail "SAPIC+ generation failed due to translation errors"
            let agentTerms = concatMap (\agent -> case agent of
                                Trusted f -> [Fun (ExampleAlgebra.Other f) [], Var f]
                                Untrusted v -> [Fun (ExampleAlgebra.Other v) [], Var v]
                             ) allAgents
                stringifyLocalString = stringifyLocal agentTerms
                -- Both trusted and untrusted agent names get the $ prefix:
                -- Untrusted agents appear as Var in the IR, Trusted ones as
                -- 0-ary Fun. SAPIC.markAgents handles both cases.
                allAgentNames = Set.fromList $
                    [v | Untrusted v <- allAgents] ++ [f | Trusted f <- allAgents]
                -- Bind the agent identifiers ONCE at the outer level so the
                -- three agent bodies share the same $A/$B/$s within each
                -- session. Per-agent in($X) wrapping (the previous shape)
                -- gave each role its own independent binding, which made
                -- Tamarin's exists-trace search unable to construct any
                -- matching trace and left every all-traces lemma vacuous.
                bindAgents p = foldr (\name -> SAPIC.SIn (Var ('$':name))) p (Set.toList allAgentNames)
                -- API serialization: wrap [API]-flagged agent bodies in a
                -- single global lock <'api'>; ... unlock <'api'>;. Mirrors
                -- ProVerif's api_call_lock private channel, which enforces
                -- at-most-one API call in flight across all sessions.
                apiLockKey = Fun "'api'" []
                wrapApi isAPI body
                    | isAPI     = SAPIC.SLock apiLockKey (SAPIC.appendUnlock apiLockKey body)
                    | otherwise = body
                perAgentSapic = map (\(agent, local, frame, _, _, isAPI) ->
                    let unfolded = unfoldLocalKnowledge frame local
                        s = SAPIC.localToSapic (stringifyLocalString unfolded)
                    in (agent, wrapApi isAPI (SAPIC.markAgents allAgentNames s))) successful
                combinedAgents = foldr1 (\a b -> SAPIC.SPar a b) (map snd perAgentSapic)
                -- Agent corruption process: lets the attacker reveal any
                -- public agent identifier's private secrets. Two parallel
                -- branches: one leaks the asymmetric private key
                -- pv_inv(pv_pk($X)); the other leaks each shared key
                -- sk($X, $Y) -- compromising $X also compromises every
                -- pairwise key it shares with another $Y. Models the
                -- ProVerif "A <> i" honesty clauses in lemma form (see
                -- revealEscapes in SAPICPrinter).
                revealAsymProc =
                    SAPIC.SBang $
                    SAPIC.SIn (Var "$X") $
                    SAPIC.SEvent "Reveal" [Var "$X"] $
                    SAPIC.SOut (Fun "pv_inv" [Fun "pv_pk" [Var "$X"]]) SAPIC.SZero
                revealSkProc =
                    SAPIC.SBang $
                    SAPIC.SIn (Var "$X") $
                    SAPIC.SIn (Var "$Y") $
                    SAPIC.SEvent "Reveal" [Var "$X"] $
                    SAPIC.SOut (Fun "sk" [Var "$X", Var "$Y"]) SAPIC.SZero
                combined =
                    SAPIC.SPar (SAPIC.SBang (bindAgents combinedAgents)) $
                    SAPIC.SPar revealAsymProc revealSkProc
                -- Collect goals across agents (mirrors the ProVerif emit logic).
                (sapicWeak, sapicStrong) =
                    foldl (\(w1,s1) (_,_,_,(w2,s2),_,_) -> (w1++w2, s1++s2)) ([],[]) successful
                sapicSecrecyGoals = nub $ concatMap (\(_,_,_,_,s,_) -> s) successful
                weakAuthNames   = nub [name | (name,_,_,_) <- sapicWeak]
                strongAuthNames = nub [name | (name,_,_,_) <- sapicStrong]
                secrecyArities  = nub [(name, length terms) | (name, terms) <- sapicSecrecyGoals]
                theoryName = "CryptoChoreo"
                sapicUserFuncs = [(name, length inputTypes)
                                 | (name, inputTypes, _) <- allPublicFuncs ++ allPrivateFuncs]
                sapicCode = SAPICPrinter.generateCompleteSapicFile
                                theoryName
                                sanityFlag
                                sapicUserFuncs
                                secrecyArities
                                weakAuthNames
                                strongAuthNames
                                combined
            if null sapicOutFile
                then putStrLn sapicCode
                else do
                    writeFile sapicOutFile sapicCode
                    hPutStrLn stderr $ "SAPIC+ theory written to " ++ sapicOutFile

