{-# LANGUAGE LambdaCase #-}
module ProVerif where
import Term
import qualified Text.PrettyPrint as PP
import Local
import ExamplePVT
import ExampleAlgebra
import Choreo (Agent(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Char

network = "c"
inetwork = "ic"
wildcard = "_"
branch = "branch"
intruder = "i"
cell = "cell"
counter = "counter"


data Process
    -- local process
    = Out String (Term String String) Process
    | In String (Term String String) Process
    | Let String (Term String String) Process
    | New String Process
    | If (Term String String) (Term String String) Process Process
    | IfTrue (Term String String) (Term String String) Process
    | IfFalse (Term String String) (Term String String) Process
    | InNat Process -- Receive a nat value from the intruder into the "branch" variable
    | Event String [Term String String] Process
    | Zero
    | Write String (Term String String) (Term String String) Process
    | Read String String (Term String String) Process
    | UnRead String (Term String String) (Term String String) Process -- Write a value back to a cell, with the promise that it is the same you took out
    | Get String (Term String String) Process Process  -- Get table pattern else
    | Insert String (Term String String) Process  -- Insert into table
    -- orchestration process
    | Spawn String [String] -- spawn process by name and list of agent
    | InAgents String [String] Process  -- take a list of agent names from the network
    | NewAgent String Process
    | Repeat Process
    | Par Process Process

data PVFormula
    = PVEvent String [Term String String]
    | PVInjEvent String [Term String String]
    | PVAttacker (Term String String)
    | PVEq (Term String String) (Term String String)
    | PVNeq (Term String String) (Term String String)
    | PVAnd PVFormula PVFormula
    | PVImply PVFormula PVFormula
    deriving (Show,Eq)



data Context = Context {
    types :: [String],
    privateFunctions :: [(String,[String],[String])],
    publicFunctions :: [(String,[String],[String])],
    cells :: [String],
    agents :: [Agent String String],
    knowledge :: Map (Agent String String) (Set (Term String String)),
    events :: Map String [String],
    queries :: [([(String,String)],PVFormula)]
}


data MemoryModel
    = WithAxioms
    | NoAxioms
    deriving (Eq, Show)

localToProcess :: MemoryModel -> Bool -> Bool -> Local String String -> Process
localToProcess mm isAPI stateChange LEnd = releaseIfAPI isAPI stateChange
localToProcess mm isAPI stateChange (LReceive x l) = In network (Var x) (localToProcess mm isAPI stateChange l)
localToProcess mm isAPI _ (LSend t l) = Out network t (localToProcess mm isAPI True l)
localToProcess mm isAPI stateChange (LAtomic a) = latomicToProcess mm isAPI stateChange Map.empty a

releaseIfAPI :: Bool -> Bool -> Process
releaseIfAPI True True = Out "api_call_lock" (Fun "api_call_baton" []) Zero
releaseIfAPI _ _ = Zero

latomicToProcess :: MemoryModel -> Bool -> Bool -> Map String (String, Term String String) -> LAtomic String String -> Process
latomicToProcess mm isAPI stateChange readmap (LNonce x a) = New x (latomicToProcess mm isAPI stateChange readmap a)
latomicToProcess mm isAPI stateChange readmap (LLet x t a) = ProVerif.Let x t (latomicToProcess mm isAPI stateChange readmap a)
latomicToProcess mm isAPI _ readmap (LEvent name terms a) = Event name terms (latomicToProcess mm isAPI True readmap a)
latomicToProcess mm isAPI stateChange readmap (LChoice atomics) =
    InNat $
    snd (foldl (\ (n,p) a ->
            (n + 1,p . If (Var branch) (Fun (show n) []) (latomicToProcess mm isAPI stateChange readmap a))) (0,id) atomics)
        (releaseIfAPI isAPI stateChange)
latomicToProcess mm isAPI stateChange readmap (LBranch t1 t2 a1 a2) = If t1 t2 (latomicToProcess mm isAPI stateChange readmap a1) (latomicToProcess mm isAPI stateChange readmap a2)
latomicToProcess mm isAPI stateChange readmap (LRead name v t a) =
    Read name v t $
    latomicToProcess mm isAPI stateChange (Map.insert name (v,t) readmap) a
latomicToProcess mm isAPI stateChange readmap (LWrites w) =
    let (writemap, process) = lwritesToProcess mm isAPI stateChange readmap Map.empty w
        missing = Map.difference writemap readmap in
    Map.foldrWithKey (`Read` wildcard) process missing

lwritesToProcess :: MemoryModel -> Bool -> Bool -> Map String (String, Term String String) -> Map String (Term String String) -> LWrites String String -> (Map String (Term String String), Process)
lwritesToProcess mm isAPI stateChange readmap writeMap (LWrite name addr value w) =
    Bifunctor.second (Write name addr value) (lwritesToProcess mm isAPI True readmap (Map.insert name addr writeMap) w)
lwritesToProcess mm isAPI stateChange readmap writeMap (Local l) =
    let missing = if isAPI && not stateChange && not (futureStateChange l) then Map.empty else Map.difference readmap writeMap in
    (writeMap, Map.foldrWithKey (\name (v,t) -> UnRead name t (Var v)) (localToProcess mm isAPI stateChange l) missing)

futureStateChange :: Local String String -> Bool
futureStateChange LEnd = False
futureStateChange (LSend _ _) = True
futureStateChange (LReceive _ l) = futureStateChange l
futureStateChange (LAtomic a) = futureStateChangeAtomic a

futureStateChangeAtomic :: LAtomic String String -> Bool
futureStateChangeAtomic (LNonce _ a) = futureStateChangeAtomic a
futureStateChangeAtomic (LLet _ _ a) = futureStateChangeAtomic a
futureStateChangeAtomic (LEvent _ _ a) = True
futureStateChangeAtomic (LChoice atomics) = any futureStateChangeAtomic atomics
futureStateChangeAtomic (LBranch _ _ a1 a2) = futureStateChangeAtomic a1 || futureStateChangeAtomic a2
futureStateChangeAtomic (LRead _ _ _ a) = futureStateChangeAtomic a
futureStateChangeAtomic (LWrites w) = futureStateChangeWrites w

futureStateChangeWrites :: LWrites String String -> Bool
futureStateChangeWrites (LWrite _ _ _ w) = True
futureStateChangeWrites (Local l) = futureStateChange l

agentSpawner :: String -> [String] -> Process
agentSpawner agent params =
    InAgents inetwork params $
    Spawn ("process" ++ agent) params

-- | Generate main process with memory initializers
mainProcessWithInitializers :: [String] -> [Agent String String] -> Map (Agent String String) [Term String String] -> Map (Agent String String) [String] -> Process
mainProcessWithInitializers cells agents agentKnowledge agentParameters =
    let baseMain = mainProcess agents agentKnowledge agentParameters
    in foldl (\p cell -> Par p (Repeat $ Spawn ("process_" ++ cell ++ "_initializer") [])) baseMain cells

-- | Generate initializer process for a cell using table pattern
cellInitializerProcess :: MemoryModel -> String -> Process
cellInitializerProcess mm cell =
    let tableName = cell ++ "_initializer_table"
        cellName = "cell_" ++ cell
        eventName = "write_" ++ cell
        counterZero = Fun "0" []
        memValue = Fun "memory_initial_value" []
        -- For WithAxioms: output (counter, value), for NoAxioms: just value
        outputTerm = if mm == WithAxioms
                     then Fun "" [counterZero, memValue]
                     else memValue
    in In "ic" (Var "addr") $
       Get tableName (Var "addr") Zero $  -- get table(=addr) in 0 else
       (if mm == WithAxioms then Event eventName [Var "addr", counterZero, memValue] else id) $
       Insert tableName (Var "addr") $
       Out (cellName ++ "(addr)") outputTerm Zero

initialKnowledgeProcess :: String -> [String] -> [Term String String] -> Process
initialKnowledgeProcess originator agents knowledge =
    InAgents inetwork (filter (originator /=) agents) $
    Out inetwork (Fun "" (map (substitute originator (Var intruder)) knowledge)) Zero

initialKnowledgeProcesses :: [Agent String String] -> Map (Agent String String) [Term String String] -> Map (Agent String String) [String] -> Process -> Process
initialKnowledgeProcesses agents agentKnowledge agentParameters p =
    foldr (\case  Trusted _ -> id ; Untrusted v -> Par $ Repeat $ initialKnowledgeProcess v (Map.findWithDefault [] (Untrusted v) agentParameters) (Map.findWithDefault [] (Untrusted v) agentKnowledge)) p agents

mainProcess :: [Agent String String] -> Map (Agent String String) [Term String String] -> Map (Agent String String) [String] -> Process
mainProcess agents agentKnowledge agentParameters =
    Par (Repeat $ NewAgent "a" $ Out inetwork (Var "a") Zero) $
    Par (Out "api_call_lock" (Fun "api_call_baton" []) Zero) $
    initialKnowledgeProcesses agents agentKnowledge agentParameters $
    spawnagents agents
    where
        spawnagents [] = Zero
        spawnagents [a] = agentProcess a
        spawnagents (a : as) =
            Par (agentProcess a) $
            spawnagents as
        -- Use spawners for agents with parameters, direct calls for agents without
        agentProcess a =
            let agentStr = case a of
                    Trusted f -> f
                    Untrusted v -> v
                params = Map.findWithDefault [] a agentParameters
            in if null params
               -- No params: call directly
               then Repeat $ Spawn ("process" ++ agentStr) []
               -- Has params: use spawner
               else Repeat $ Spawn ("spawn" ++ agentStr) []

