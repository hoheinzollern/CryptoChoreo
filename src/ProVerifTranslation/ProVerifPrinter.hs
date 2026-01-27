module ProVerifPrinter where
import Term
import Text.PrettyPrint
import Local
import ExamplePVT
import ExampleAlgebra
import Choreo (GoalSet, Agent(..))
import Data.Map (Map)
import ProVerif
import qualified Data.Map as Map
import qualified Data.List as List
import qualified Data.Set as Set
import Data.Set (Set)
import Data.Char (toUpper)
import Prelude hiding ((<>))

agentToString :: Agent String String -> String
agentToString (Trusted f) = f
agentToString (Untrusted v) = v

ppTerm :: Term String String -> Doc
ppTerm (Var v) = text v
ppTerm (Fun f []) = text f
ppTerm (Fun f args) = text f <> parens (hcat $ punctuate comma (map ppTerm args))

ppPattern :: Term String String -> Doc
ppPattern term = char '=' <> ppTerm term

-- | Check if a process needs parentheses when used in Par
needsParens :: Process -> Bool
needsParens Zero = False
needsParens (Spawn _ _) = False
needsParens (Repeat _) = False
needsParens (Par _ _) = False  -- Par is associative, no parens needed
needsParens _ = True


ppProcess :: MemoryModel -> Process -> Doc
ppProcess mm  Zero = text "0"
ppProcess mm  (Out chan term p) =
    text "out" <> parens (hcat $ punctuate comma [text chan, ppTerm term]) <> semi $$
    ppProcess mm  p
ppProcess mm  (In chan term p) =
    let termDoc = case term of
            -- Special case: api_call_baton should be matched, not bound
            Fun "api_call_baton" [] -> ppPattern term
            -- All other terms: bind with type annotation
            _ -> ppTerm term <> colon <+> text "bitstring"
    in text "in" <> parens (hcat $ punctuate comma [text chan, termDoc]) <> text "[precise]" <> semi $$ -- should be an option 
       ppProcess mm  p
ppProcess mm  (ProVerif.Let var term p) =
    parens (text "let" <+> text var <+> equals <+> ppTerm term <+> text "in" $$
    ppProcess mm  p)
ppProcess mm  (New var p) =
    text "new" <+> text var <> colon <+> text "bitstring" <> semi $$
    ppProcess mm  p
ppProcess mm  (If t1 t2 p1 p2) =
    text "if" <+> ppTerm t1 <+> equals <+> ppTerm t2 <+> text "then" $$
    nest 4 (ppProcess mm  p1) $$
    text "else" $$
    nest 4 (ppProcess mm  p2)
ppProcess mm  (IfTrue t1 t2 p) =
    parens (text "if" <+> ppTerm t1 <+> equals <+> ppTerm t2 <+> text "then" $$
    (ppProcess mm  p))
ppProcess mm  (IfFalse t1 t2 p) =
    parens (text "if" <+> ppTerm t1 <+> text "<>" <+> ppTerm t2 <+> text "then" $$
    (ppProcess mm  p))
ppProcess mm  (Event name terms p) =
    text "event" <+> text name <> parens (hcat $ punctuate comma (map ppTerm terms)) <> semi $$
    ppProcess mm  p
-- No axioms
ppProcess NoAxioms  (Write name addr term p) =
    let cellName = "cell_" ++ name
    in  parens (text "out" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),ppTerm term]) <> text "|" $$
       parens (ppProcess NoAxioms  p))
ppProcess NoAxioms  (UnRead name addr term p) =  -- without axioms, UnRead is just Write
    let cellName = "cell_" ++ name
    in  parens (text "out" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),ppTerm term]) <> text "|" $$
       parens (ppProcess NoAxioms  p))
ppProcess NoAxioms  (Read name var addr p) =
    let cellName = "cell_" ++ name
        varPattern = text var <> colon <+> text "bitstring"
    in  text "out" <> parens (text "ic" <> comma <> ppTerm addr) <> semi $$
        text "in" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),
         parens varPattern]) <> text "[precise]" <> semi $$ -- TODO: this should probably be an option
       ppProcess NoAxioms  p
-- Public addresses
ppProcess WithAxioms  (Write name addr term p) =
    let cellName = "cell_" ++ name
        counterVar = "counter_" ++ name
        eventName = "write_" ++ name
    in text "event" <+> text eventName <> parens (hcat $ punctuate comma
        [ppTerm addr, text counterVar <> text "+" <> text "1", ppTerm term]) <> semi $$
       parens (text "out" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),
         parens (text counterVar <> text "+" <> text "1" <> comma <> ppTerm term)]) <> text "|" $$
       parens (ppProcess WithAxioms  p))
ppProcess WithAxioms  (UnRead name addr term p) =
    let cellName = "cell_" ++ name
        counterVar = "counter_" ++ name
        eventName = "write_" ++ name
    in text "event" <+> text eventName <> parens (hcat $ punctuate comma
        [ppTerm addr, text counterVar, ppTerm term]) <> semi $$
       parens (text "out" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),
         parens (text counterVar <> comma <> ppTerm term)]) <> text "|" $$
       parens (ppProcess WithAxioms  p))
ppProcess WithAxioms  (Read name var addr p) =
    let cellName = "cell_" ++ name
        counterVar = "counter_" ++ name
        varPattern = text var <> colon <+> text "bitstring"
        counterPattern = text counterVar <> colon <+> text "nat"
    in  text "out" <> parens (text "ic" <> comma <> ppTerm addr) <> semi $$
        text "in" <> parens (hcat $ punctuate comma
        [text cellName <> parens (ppTerm addr),
         parens (counterPattern <> comma <> varPattern)]) <> text "[precise]" <> semi $$ --for some reason this helps. TODO: this should probably be an option
       ppProcess WithAxioms  p
ppProcess mm  (InNat p) =
    text "in" <> parens (hcat $ punctuate comma [text inetwork, text "branch" <> colon <+> text "nat"]) <> text "[precise]" <> semi $$ --adding precise here makes sure that once the intruder commits to a path, the other will not be taken
    ppProcess mm  p
ppProcess mm  (InAgents chan agentVars p) =
    text "in" <> parens (hcat $ punctuate comma [text chan, parens (hcat $ punctuate comma (map (\v -> text v <> colon <+> text "agent") agentVars))]) <> semi $$
    ppProcess mm  p
ppProcess mm  (NewAgent var p) =
    text "new" <+> text var <> colon <+> text "agent" <> semi $$
    ppProcess mm  p
ppProcess mm (Get tableName pattern pThen pElse) =
    text "get" <+> text tableName <> parens (ppPattern pattern) <+> text "in" <+> ppProcess mm pThen $$
    text "else" $$
    nest 4 (ppProcess mm pElse)
ppProcess mm (Insert tableName term p) =
    text "insert" <+> text tableName <> parens (ppTerm term) <> semi $$
    ppProcess mm p
ppProcess mm  (Spawn name args) =
    text name <> parens (hcat $ punctuate comma (map text args))
ppProcess mm  (Repeat p) =
    text "!" <> parens (ppProcess mm  p)
ppProcess mm  (Par p1 p2) =
    let pp1 = if needsParens p1 then parens (ppProcess mm  p1) else ppProcess mm  p1
        pp2 = if needsParens p2 then parens (ppProcess mm  p2) else ppProcess mm  p2
    in pp1 <+> text "|" $$
       pp2
ppProcess _ _ = error "ppProcess: unhandled process case"

-- | Render a process to a string
renderProcess :: MemoryModel -> Process -> String
renderProcess mm p = render (ppProcess mm p) ++ "."

-- | Generate a let process definition
renderLetProcess :: MemoryModel -> String -> [String] -> Process -> Doc
renderLetProcess mm name params process =
    text "let" <+> text name <> parens (hcat $ punctuate comma (map (\p -> text p <> colon <+> text "agent") params)) <+> equals $$
    nest 4 (ppProcess mm process) <> text "."

-- | Generate the complete ProVerif file with setup, queries, process definitions, and main process
renderCompleteProVerifFile ::
    MemoryModel ->
    String ->  -- Protocol setup (types, functions, etc.)
    String ->  -- Event declarations (already formatted)
    String ->  -- Queries text (already formatted)
    [(String, [String], Process)] ->  -- List of (processName, params, process)
    Process ->  -- Main process
    String
renderCompleteProVerifFile mm setup eventDecls queries processDefs mainProc =
    let processDefsDoc = vcat $ map (\(name, params, proc) -> renderLetProcess mm name params proc $$ text "") processDefs
        mainProcDoc = text "process" $$ nest 4 (ppProcess mm mainProc)
        eventDeclsDoc = if null eventDecls then text "" else text eventDecls
        queriesDoc = if null queries then text "" else text queries
    in render $
        text setup $$
        text "" $$
        eventDeclsDoc $$
        text "" $$
        queriesDoc $$
        text "" $$
        processDefsDoc $$
        text "" $$
        mainProcDoc

-- | Generate process definitions for all agents
-- Parameters are agents that appear in the agent's initial knowledge
-- API flag indicates whether process should apply API optimizations 
generateAgentProcesses ::
    MemoryModel ->
    [String] ->  -- Declared cells (for generating initializers)
    [(Agent String String, Process, Bool)] ->  -- (agent, process, isAPI)
    Map (Agent String String) [String] ->  -- Agent free variables (parameters needed)
    [(String, [String], Process)]
generateAgentProcesses mm cells agentProcesses agentKnowledge =
    let -- Agent processes: use agents from initial knowledge as parameters
        processDefs = map (\(agent, process, isAPI) ->
            let agentStr = agentToString agent
                -- Get the agents this agent knows from initial knowledge
                params = Map.findWithDefault [] agent agentKnowledge
                -- Wrap API processes with baton acquisition at the start
                wrappedProc = if isAPI
                              then In "api_call_lock" (Fun "api_call_baton" []) process
                              else process
            in ("process" ++ agentStr, params, wrappedProc)
            ) agentProcesses

        -- Spawner processes: for agents with parameters, create spawners
        -- that read the parameters from the channel
        spawnerDefs =
            [(name, [], spawner) |
                (agent, _, _) <- agentProcesses,
                let agentStr = agentToString agent,
                let params = Map.findWithDefault [] agent agentKnowledge,
                not (null params),  -- Only create spawner if there are parameters
                let name = "spawn" ++ agentStr,
                let spawner = agentSpawner agentStr params]

        -- Memory initializer processes: generate for all memory models
        initializerDefs =
            [(initName cell, [], cellInitializerProcess mm cell) | cell <- cells]
            where
                initName cell = "process_" ++ cell ++ "_initializer"
    in processDefs ++ spawnerDefs ++ initializerDefs

generateSecrecyQuery :: String -> [Term String String] -> String
generateSecrecyQuery eventName terms =
    let -- Split into agent terms and secret term (last one is secret)
        agentTerms = if null terms then [] else init terms
        -- Extract agent variables from agent2bitstring(A) patterns
        agentVars = concatMap extractAgentFromBitstring agentTerms
        -- Declare agents as agent type, secret as bitstring with generic name
        varDecls = if null agentVars
            then "b_secret:bitstring; "
            else List.intercalate ", " (map (\v -> v ++ ":agent") agentVars) ++ ", b_secret:bitstring; "
        -- Generate the event parameter list with agent2bitstring for agent vars and b for secret
        eventParams = List.intercalate "," (map ppTermToString agentTerms ++ ["b_secret"])
        -- Generate honesty conditions for agent variables
        honestyConditions = if null agentVars
            then ""
            else List.intercalate " && " (map (\v -> v ++ " <> i") agentVars) ++ " && "
    in "query " ++ varDecls ++
       honestyConditions ++ "attacker(b_secret) && event(" ++ eventName ++ "(" ++ eventParams ++ "))."
  where
    -- Extract agent variable from agent2bitstring(A) term
    extractAgentFromBitstring (Fun "agent2bitstring" [Var v]) = [v]
    extractAgentFromBitstring _ = []
    -- Convert term to string for event parameters
    ppTermToString t = render (ppTerm t)

-- | Generate weak authentication query
-- Events have form: beginEventName(A,B,b) and endEventName(A,B,b)
-- Agent parameters are agent type, term parameter is bitstring
-- Query format: query A:agent, B:agent, b:bitstring; A <> i && B <> i && event(end...(agent2bitstring(A),...)) ==> event(begin...(agent2bitstring(A),...))
generateWeakAuthQuery :: String -> [String] -> Term String String -> String
generateWeakAuthQuery eventName agents term =
    let agentDecls = if null agents
            then "b_auth:bitstring; "
            else List.intercalate ", " (map (\a -> a ++ ":agent") agents) ++ ", b_auth:bitstring; "
        agentParams = if null agents then "b_auth" else List.intercalate "," (map (\a -> "agent2bitstring(" ++ a ++ ")") agents) ++ ",b_auth"
        honestyConditions = if null agents
            then ""
            else List.intercalate " && " (map (\a -> a ++ " <> i") agents) ++ " && "
    in "query " ++ agentDecls ++
       honestyConditions ++ "event(end" ++ eventName ++ "(" ++ agentParams ++ ")) ==> " ++
       "event(begin" ++ eventName ++ "(" ++ agentParams ++ "))."

-- | Generate strong authentication query (with inj-event)
-- Events have form: beginEventName(A,B,b) and endEventName(A,B,b)
-- Agent parameters are agent type, term parameter is bitstring
-- Query format: query A:agent, B:agent, b:bitstring; A <> i && B <> i && inj-event(end...(agent2bitstring(A),...)) ==> inj-event(begin...(agent2bitstring(A),...))
generateStrongAuthQuery :: String -> [String] -> Term String String -> String
generateStrongAuthQuery eventName agents term =
    let agentDecls = if null agents
            then "b_auth:bitstring; "
            else List.intercalate ", " (map (\a -> a ++ ":agent") agents) ++ ", b_auth:bitstring; "
        agentParams = if null agents then "b_auth" else List.intercalate "," (map (\a -> "agent2bitstring(" ++ a ++ ")") agents) ++ ",b_auth"
        honestyConditions = if null agents
            then ""
            else List.intercalate " && " (map (\a -> a ++ " <> i") agents) ++ " && "
    in "query " ++ agentDecls ++
       honestyConditions ++ "inj-event(end" ++ eventName ++ "(" ++ agentParams ++ ")) ==> " ++
       "inj-event(begin" ++ eventName ++ "(" ++ agentParams ++ "))."

-- | Generate all queries from goals
-- The Map contains event names mapped to term lists
generateQueries ::
    GoalSet String String ->  -- (weak auth goals, strong auth goals)
    [(String, [Term String String])] ->  -- Secrecy goals: (eventName, terms)
    String
generateQueries (weakAuths, strongAuths) secrecyGoals =
    let secrecyQueries = map (\(name, terms) -> generateSecrecyQuery name terms) secrecyGoals
        weakAuthQueries = map (\(name, a1, a2, term) ->
            generateWeakAuthQuery name [agentToString a1, agentToString a2] term) weakAuths
        strongAuthQueries = map (\(name, a1, a2, term) ->
            generateStrongAuthQuery name [agentToString a1, agentToString a2] term) strongAuths
        allQueries = secrecyQueries ++ weakAuthQueries ++ strongAuthQueries
    in if null allQueries
       then ""
       else "(* Security queries *)\n" ++ unlines allQueries

-- | Generate event declarations from goals and explicitly declared events
-- Event declarations must appear before queries and processes
generateEventDeclarations ::
    GoalSet String String ->  -- (weak auth goals, strong auth goals)
    [(String, [Term String String])] ->  -- Secrecy goals: (eventName, terms)
    Map String [String] ->  -- Explicitly declared events from Context
    String
generateEventDeclarations (weakAuths, strongAuths) secrecyGoals declaredEvents =
    let -- After stringification, all terms are bitstrings (including agent2bitstring(A))
        secrecyDecls = map (\(name, terms) ->
            let termTypes = replicate (length terms) "bitstring"
            in "event " ++ name ++ "(" ++ List.intercalate "," termTypes ++ ").")
            secrecyGoals
        weakAuthDecls = concatMap (\(name, a1, a2, _) ->
            ["event begin" ++ name ++ "(bitstring,bitstring,bitstring).",
             "event end" ++ name ++ "(bitstring,bitstring,bitstring)."])
            weakAuths
        strongAuthDecls = concatMap (\(name, a1, a2, _) ->
            ["event begin" ++ name ++ "(bitstring,bitstring,bitstring).",
             "event end" ++ name ++ "(bitstring,bitstring,bitstring)."])
            strongAuths
        -- Format explicitly declared events from Context
        declaredEventDecls = ["event " ++ name ++ "(" ++ List.intercalate "," types ++ ")."
                             | (name, types) <- Map.toList declaredEvents]
        allDecls = secrecyDecls ++ weakAuthDecls ++ strongAuthDecls ++ declaredEventDecls
    in if null allDecls
       then ""
       else unlines allDecls

-- | Generate function declarations for user-defined functions
-- Functions with arity 0 are constants, others are functions from bitstrings to bitstring
generateFunctionDeclarations :: [(String, Int)] -> String
generateFunctionDeclarations funcs =
    if null funcs
    then ""
    else unlines [if null f then "" else declareFn f arity | (f, arity) <- funcs] ++ "\n"
  where
    declareFn f 0 = "const " ++ f ++ ": bitstring."
    declareFn f n = "fun " ++ f ++ "(" ++ List.intercalate "," (replicate n "bitstring") ++ "): bitstring."

-- | Generate trusted agent declarations (free constants)
-- For each Trusted agent, generate: free agentName: agent.
generateTrustedAgentDeclarations :: [Agent String String] -> String
generateTrustedAgentDeclarations agents =
    let trustedAgents = [name | Trusted name <- agents]
        decls = map (\name -> "free " ++ name ++ ": agent.") trustedAgents
    in if null decls
       then ""
       else unlines decls ++ "\n"

-- | Generate cell declarations for each declared cell
-- For each cell, generate:
--   fun cell_name(bitstring): channel [private].
--   event write_name(bitstring,nat,bitstring).
--   axiom addr: bitstring, i: nat, val1: bitstring, val2: bitstring;
--       event(write_name(addr,i,val1)) && event(write_name(addr,i,val2)) ==> val1 = val2.
generateCellDeclarations :: MemoryModel -> [String] -> String
generateCellDeclarations mm cells
  | null cells = ""
  | mm == NoAxioms = unlines (concatMap generateCellDeclNoAxioms cells) ++ "\n"
  | mm == WithAxioms = unlines (concatMap generateCellDeclWithAxioms cells) ++ "\n"
  | otherwise = error "unknown memory model"
  where
      generateCellDeclWithAxioms name
        = ["fun cell_" ++ name ++ "(bitstring): channel [private].",
           "event write_" ++ name ++ "(bitstring,nat,bitstring).",
           "axiom addr: bitstring, i: nat, val1: bitstring, val2: bitstring;",
           "    event(write_"
             ++
               name
                 ++
                   "(addr,i,val1)) && event(write_"
                     ++ name ++ "(addr,i,val2)) ==> val1 = val2.",
           "", "table " ++ name ++ "_initializer_table(bitstring)."]
      generateCellDeclNoAxioms name
        = ["fun cell_" ++ name ++ "(bitstring): channel [private].", "",
           "table " ++ name ++ "_initializer_table(bitstring)."]

-- | Render a PVFormula to ProVerif syntax
renderPVFormula :: PVFormula -> String
renderPVFormula (PVEvent name terms) =
    "event(" ++ name ++ "(" ++ List.intercalate "," (map (render . ppTerm) terms) ++ "))"
renderPVFormula (PVInjEvent name terms) =
    "inj-event(" ++ name ++ "(" ++ List.intercalate "," (map (render . ppTerm) terms) ++ "))"
renderPVFormula (PVAttacker term) =
    "attacker(" ++ render (ppTerm term) ++ ")"
renderPVFormula (PVEq t1 t2) =
    render (ppTerm t1) ++ " = " ++ render (ppTerm t2)
renderPVFormula (PVNeq t1 t2) =
    render (ppTerm t1) ++ " <> " ++ render (ppTerm t2)
renderPVFormula (PVAnd f1 f2) =
    renderPVFormula f1 ++ " && " ++ renderPVFormula f2
renderPVFormula (PVImply f1 f2) =
    renderPVFormula f1 ++ " ==> " ++ renderPVFormula f2

-- | Render a query with quantifiers to ProVerif syntax
-- Query format: query var1:type1, var2:type2; formula.
renderQuery :: ([(String, String)], PVFormula) -> String
renderQuery (quantifiers, formula) =
    let varDecls = List.intercalate ", " [var ++ ":" ++ typ | (var, typ) <- quantifiers]
        separator = if null varDecls then "" else varDecls ++ "; "
    in "query " ++ separator ++ renderPVFormula formula ++ "."

-- | Render a list of queries
renderQueries :: [([(String, String)], PVFormula)] -> String
renderQueries queries = List.intercalate "\n" (map renderQuery queries)

-- | Generate complete ProVerif file with security queries
-- Secrecy goals should be (eventName, terms) tuples
generateCompleteProVerifFileWithQueries ::
    MemoryModel ->
    String ->  -- Protocol setup text
    [Agent String String] ->  -- All agents (Trusted/Untrusted)
    [(Agent String String, Process, Bool)] ->  -- (agent, agentProcess, isAPI) tuples
    Map (Agent String String) [String] ->  -- Map from agent to list of known agent names
    Map (Agent String String) [Term String String] ->  -- Map from agent to list of known terms
    [String] ->  -- Declared cells from Context
    Map String [String] ->  -- Explicitly declared events from Context
    [([(String, String)], PVFormula)] ->  -- Manual queries from choreography
    GoalSet String String ->  -- Goal set from translation
    [(String, [Term String String])] ->  -- Secrecy goals: (eventName, terms)
    [(String, Int)] ->  -- User-defined function symbols with their arities
    String
generateCompleteProVerifFileWithQueries mm setup allAgents agentProcesses agentParameters agentKnowledge declaredCells declaredEvents manualQueries goalSet secrecyGoals userDefinedFuncs =
    let trustedDecls = generateTrustedAgentDeclarations allAgents
        funcDecls = generateFunctionDeclarations userDefinedFuncs
        cellDecls = generateCellDeclarations mm declaredCells
        setupWithDecls = setup ++ "\n" ++ trustedDecls ++ funcDecls ++ cellDecls
        processDefs = generateAgentProcesses mm declaredCells agentProcesses agentParameters
        main = mainProcessWithInitializers declaredCells allAgents agentKnowledge agentParameters
        eventDecls = generateEventDeclarations goalSet secrecyGoals declaredEvents
        -- Generate queries from goals
        goalQueries = generateQueries goalSet secrecyGoals
        -- Render manual queries
        manualQueriesStr = if null manualQueries then "" else renderQueries manualQueries
        -- Combine both types of queries
        allQueries = if null manualQueriesStr
                     then goalQueries
                     else if null goalQueries
                          then manualQueriesStr
                          else goalQueries ++ "\n" ++ manualQueriesStr
    in renderCompleteProVerifFile mm setupWithDecls eventDecls allQueries processDefs main