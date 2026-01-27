{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Choreo where
import Term
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Util


data Agent f v
    = Trusted f
    | Untrusted v
    deriving (Show,Ord,Eq)

fvag :: Agent f a -> Set a
fvag (Untrusted v) = Set.singleton v
fvag (Trusted _) = Set.empty

instance Castable (Agent f v) (Term f v) where
    cast (Trusted f) = Fun f []
    cast (Untrusted v) = Var v
    uncast (Fun f []) = Trusted f
    uncast (Var v) = Untrusted v
    uncast _ = error "Cannot uncast Term to Agent"

mapfAgent :: Monad m => (f -> m g) -> Agent f v -> m (Agent g v)
mapfAgent f (Trusted g) = do
    g' <- f g
    return (Trusted g')
mapfAgent _ (Untrusted v) = return (Untrusted v)




data Choreo f v
    = End
    | Send (Agent f v) (Agent f v) (Term f v) (Choreo f v)
    | Atomic (Agent f v) (Atomic f v)
    deriving (Show,Eq)

data Atomic f v
    = Nonce v [Term f v] (Atomic f v)
    | Choice [Atomic f v]
    | Event String [Term f v] (Atomic f v)
    | Read String (Term f v) (Term f v) (Atomic f v)
    | Branch (Term f v) (Term f v) (Atomic f v) (Atomic f v)
    | Writes (Writes f v)
    deriving (Show,Eq)

data Writes f v 
    = Write String (Term f v) (Term f v) (Writes f v) 
    | Choreo (Choreo f v)
    deriving (Show,Eq)

data ChoreoUnion f v
    = CUChoreo (Choreo f v)
    | CUAtomic (Agent f v) (Atomic f v)
    | CUWrites (Agent f v) (Writes f v)
    deriving (Show,Eq)

toChoreo :: ChoreoUnion f v -> Choreo f v
toChoreo (CUChoreo c) = c
toChoreo (CUAtomic a at) = Atomic a at
toChoreo (CUWrites a w) = Atomic a (Writes w)

toAtomic :: ChoreoUnion f v -> Atomic f v
toAtomic (CUChoreo c) = Writes (Choreo c)
toAtomic (CUAtomic _ at) = at
toAtomic (CUWrites _ w) = Writes w

toWrites :: ChoreoUnion f v -> Writes f v
toWrites (CUChoreo c) = Choreo c
toWrites (CUAtomic a at) = Choreo (Atomic a at)
toWrites (CUWrites _ w) = w


data InitialChoreo f v
    = IEnd (Goals f v)
    | ISend (Agent f v) (Agent f v) (Term f v) (InitialChoreo f v)
    | ILet1 v (Term f v) (InitialChoreo f v)
    | IAtomic (Agent f v) (InitialAtomic f v)
    deriving (Show,Eq)

data InitialAtomic f v
    = INonce v [Term f v] (InitialAtomic f v)
    | ILet2 v (Term f v) (InitialAtomic f v)
    | IChoice [InitialAtomic f v]
    | IEvent String [Term f v] (InitialAtomic f v)
    | IBranch (Term f v) (Term f v) (InitialAtomic f v) (InitialAtomic f v)
    | IRead String (Term f v) (Term f v) (InitialAtomic f v)
    | IWrites (InitialWrites f v)
    deriving (Show,Eq)

data InitialWrites f v 
    = IWrite String (Term f v) (Term f v) (InitialWrites f v) 
    | IChoreo (InitialChoreo f v)
    deriving (Show,Eq)

data Goals f v
    = EndGoals
    | Secret [Agent f v] (Term f v) (Goals f v)
    | WeakAuth (Agent f v) (Agent f v) (Term f v) (Goals f v) -- injective authenticity. first authenticates to second / second authenticates first
    | StrongAuth (Agent f v) (Agent f v) (Term f v) (Goals f v) -- non-injective authenticity
    deriving (Show,Eq)

-- list of weak auths x list of strong auths
type GoalSet f v = ([(String, Agent f v, Agent f v, Term f v)],[(String, Agent f v, Agent f v, Term f v)])


emptyGoals :: GoalSet f v
emptyGoals = ([],[])
addWeak :: String -> Agent f v -> Agent f v -> Term f v -> GoalSet f v -> GoalSet f v
addWeak name a1 a2 t (ws,ss) = ((name,a1,a2,t) : ws,ss)
addStrong :: String -> Agent f v -> Agent f v -> Term f v -> GoalSet f v -> GoalSet f v
addStrong name a1 a2 t (ws,ss) = (ws,(name,a1,a2,t) : ss)
unionGoals :: GoalSet f v -> GoalSet f v -> GoalSet f v
unionGoals (ws1,ss1) (ws2,ss2) = (ws1 ++ ws2,ss1 ++ ss2)

applyFst' :: (t -> a) -> (t, b, c, d) -> (a, b, c, d)
applyFst' f (x,y,z,w) = (f x,y,z,w)

data FirstPassState f v = FPS {
    weakCount :: Int,
    strongCount :: Int,
    secretCount :: Int,
    lets :: Map v (Term f v)
    }

initialFPS :: FirstPassState f v
initialFPS = FPS 0 0 0 Map.empty

setCountFPS :: FirstPassState f v -> (Int, Int, Int) -> FirstPassState f v
setCountFPS fps (i,j,k) = fps {weakCount = i, strongCount = j, secretCount = k}
getCountFPS :: FirstPassState f v -> (Int, Int, Int)
getCountFPS fps = (weakCount fps, strongCount fps, secretCount fps)

applyFPS :: Ord v => FirstPassState f v -> Term f v -> Term f v
applyFPS fps = substituteMap (lets fps)

insertFPS :: Ord v => v -> Term f v -> FirstPassState f v -> FirstPassState f v
insertFPS v t fps = fps {lets = Map.insert v t (lets fps)}

getGoals :: Ord v => FirstPassState f v -> Goals f v -> (Choreo f v, (Int, Int, Int), GoalSet f v, [(String, [Term f v])])
getGoals fps = getGoals' id fps ([],[]) []
    where
    getGoals' choreo fps gs sgs EndGoals = (choreo End,getCountFPS fps,gs,sgs)
    getGoals' choreo fps  gs sgs (Secret as t g) =
        let (i,j,k) = getCountFPS fps in
        let eventName = "secret" ++ show i
            t' = applyFPS fps t
            args = map cast as ++ [t'] in
        getGoals' (choreo . secretFolder eventName (map cast as) t' as) (setCountFPS fps (i+1,j,k)) gs ((eventName,args):sgs) g
        where
            secretFolder _ _ _ [] = id
            secretFolder eventName agents t (a : as') = Atomic a . Event eventName (agents ++ [t]) . Writes . Choreo . secretFolder eventName agents t as'
    getGoals' choreo fps gs sgs (WeakAuth a1 a2 t g) =
        let (i,j,k) = getCountFPS fps in
        let t' = applyFPS fps t in
        let eventName = "weakauth" ++ show j in
        getGoals' (choreo . Atomic a2 . Event ("end" ++ eventName) [cast a1, cast a2, t'] . Writes . Choreo) (setCountFPS fps (i,j+1,k)) (addWeak eventName a1 a2 t' gs) sgs g
    getGoals' choreo fps gs sgs (StrongAuth a1 a2 t g) =
        let (i,j,k) = getCountFPS fps in
        let t' = applyFPS fps t in
        let eventName = "strongauth" ++ show k in
        getGoals' (choreo . Atomic a2 . Event ("end" ++ eventName) [cast a1, cast a2, t'] . Writes . Choreo) (setCountFPS fps (i,j,k+1)) (addStrong eventName a1 a2 t' gs) sgs g

firstPass :: Ord v =>
    InitialChoreo f v -> FirstPassState f v -> (Choreo f v, (Int,Int,Int), GoalSet f v, [(String,[Term f v])])
firstPass (IEnd gs) fps = getGoals fps gs
firstPass (ISend a1 a2 t c) fps = applyFst' (Send a1 a2 (applyFPS fps t)) (firstPass c fps)
firstPass (IAtomic a at) fps = applyFst' (Atomic a) (firstPassAtomic at fps)
firstPass (ILet1 v t c) fps =
    let t' = applyFPS fps t
        fps' = insertFPS v t' fps
    in firstPass c fps'

firstPassAtomic :: Ord v =>
    InitialAtomic f v -> FirstPassState f v -> (Atomic f v, (Int,Int,Int), GoalSet f v, [(String,[Term f v])])
firstPassAtomic (INonce v ts c) fps = applyFst' (Nonce v ts) (firstPassAtomic c fps)
firstPassAtomic (IChoice cs) fps =
    let f (fps',cs,gs,sgs) c = (let (c',ijk,gs',sgs') = firstPassAtomic c fps' in (setCountFPS fps' ijk,c':cs,unionGoals gs' gs,sgs ++ sgs'))
        (fps',cs'',gs',sgs') = foldl f (fps,[],emptyGoals,[]) cs
        cs' = reverse cs''
    in (Choice cs',getCountFPS fps',gs', sgs')
firstPassAtomic (IEvent name ts c) fps =
    let (c',ijk,gs',sgs') = firstPassAtomic c fps
        ts' = map (applyFPS fps) ts
    in (Event name ts' c', ijk, gs', sgs')
firstPassAtomic (IRead name t1 t2 c) fps = applyFst' (Read name (applyFPS fps t1) (applyFPS fps t2)) (firstPassAtomic c fps)
firstPassAtomic (IBranch t1 t2 c1 c2) fps =
    let (c1', ijk1, gs1, sgs1) = firstPassAtomic c1 fps
        (c2', ijk2, gs2, sgs2) = firstPassAtomic c2 (setCountFPS fps ijk1)
    in (Branch (applyFPS fps t1) (applyFPS fps t2) c1' c2', ijk2, unionGoals gs1 gs2, sgs1 ++ sgs2)
firstPassAtomic (ILet2 v t a) fps =
    let t' = applyFPS fps t
        fps' = insertFPS v t' fps
    in firstPassAtomic a fps'
firstPassAtomic (IWrites w) fps = applyFst' Writes (firstPassWrites w fps)

firstPassWrites :: Ord v =>
    InitialWrites f v -> FirstPassState f v -> (Writes f v, (Int,Int,Int), GoalSet f v, [(String,[Term f v])])
firstPassWrites (IChoreo c) fps = applyFst' Choreo (firstPass c fps)
firstPassWrites (IWrite name t1 t2 c) fps = applyFst' (Write name (applyFPS fps t1) (applyFPS fps t2)) (firstPassWrites c fps)


fvgs :: Ord v => GoalSet f v -> Set v
fvgs (ws,ss) = foldr (Set.union . (\(_,a1,a2,t) -> Set.unions [fvag a1, fvag a2, fvt t])) Set.empty (ws ++ ss)

fvc :: Ord v => Choreo f v -> Set v
fvc End = Set.empty
fvc (Send a1 a2 t c) = Set.unions [fvag a1, fvag a2, fvt t, fvc c]
fvc (Atomic a at) = Set.union (fvag a) $ fva at

fva :: Ord v => Atomic f v -> Set v 
fva (Nonce v ts c) = Set.delete v (Set.unions (fva c : map fvt ts))
fva (Event _ ts c) = Set.unions (fva c : map fvt ts)
fva (Choice cs) = foldr (Set.union . fva) Set.empty cs
fva (Read _ t1 t2 c) = Set.unions [fvt t1, fvt t2, fva c]
fva (Branch t1 t2 c1 c2) = Set.unions [fvt t1, fvt t2, fva c1, fva c2]
fva (Writes w) = fvw w

fvw :: Ord v => Writes f v -> Set v
fvw (Write _ t1 t2 c) = Set.unions [fvt t1, fvt t2, fvw c]
fvw (Choreo c) = fvc c

mapfMGoalSet :: Monad m => (f -> m g) -> GoalSet f v -> m (GoalSet g v)
mapfMGoalSet f (ws,ss) = do
    ws' <- mapM convertWeak ws
    ss' <- mapM convertStrong ss
    return (ws', ss')
  where
    convertWeak (name,a1,a2,t) = do
        a1' <- mapfAgent f a1
        a2' <- mapfAgent f a2
        t' <- mapfM f t
        return (name,a1',a2',t')
    convertStrong (name,a1,a2,t) = do
        a1' <- mapfAgent f a1
        a2' <- mapfAgent f a2
        t' <- mapfM f t
        return (name,a1',a2',t')

mapfMChoreo :: Monad m => (f -> m g) -> Choreo f v -> m (Choreo g v)
mapfMChoreo _ End = return End
mapfMChoreo f (Send a1 a2 t c) = do
    a1' <- mapfAgent f a1
    a2' <- mapfAgent f a2
    t' <- mapfM f t
    c' <- mapfMChoreo f c
    return (Send a1' a2' t' c')
mapfMChoreo f (Atomic a at) = do
    a' <- mapfAgent f a
    at' <- mapfMAtomic f at
    return (Atomic a' at')

mapfMAtomic :: Monad m => (f -> m g) -> Atomic f v -> m (Atomic g v)
mapfMAtomic f (Nonce v ts c) = do
    c' <- mapfMAtomic f c
    ts' <- traverse (mapfM f) ts
    return (Nonce v ts' c')
mapfMAtomic f (Event name t c) = do
    t' <- traverse (mapfM f) t
    c' <- mapfMAtomic f c
    return (Event name t' c')
mapfMAtomic f (Choice cs) = do
    cs' <- mapM (mapfMAtomic f) cs
    return (Choice cs')
mapfMAtomic f (Branch t1 t2 c1 c2) = do
    t1' <- mapfM f t1
    t2' <- mapfM f t2
    c1' <- mapfMAtomic f c1
    c2' <- mapfMAtomic f c2
    return (Branch t1' t2' c1' c2')
mapfMAtomic f (Read name t1 t2 c) = do
    t1' <- mapfM f t1
    t2' <- mapfM f t2
    c' <- mapfMAtomic f c
    return (Read name t1' t2' c')
mapfMAtomic f (Writes w) = do
    w' <- mapfMWrites f w
    return (Writes w')

mapfMWrites :: Monad m => (f -> m g) -> Writes f v -> m (Writes g v)
mapfMWrites f (Write name t1 t2 c) = do
    t1' <- mapfM f t1
    t2' <- mapfM f t2
    c' <- mapfMWrites f c
    return (Write name t1' t2' c')
mapfMWrites f (Choreo c) = do
    c' <- mapfMChoreo f c
    return (Choreo c')


getEventNames :: Choreo f v -> Set String
getEventNames End = Set.empty
getEventNames (Send _ _ _ cont) =
    getEventNames cont
getEventNames (Atomic _ atomic) =
    getEventNamesAtomic atomic

getEventNamesAtomic :: Atomic f v -> Set String
getEventNamesAtomic (Nonce _ _ cont) = getEventNamesAtomic cont
getEventNamesAtomic (Choice choices) =
    Set.unions (map getEventNamesAtomic choices)
getEventNamesAtomic (Branch _ _ cont1 cont2) =
    Set.union (getEventNamesAtomic cont1) (getEventNamesAtomic cont2)
getEventNamesAtomic (Event name _ cont) =
    Set.insert name (getEventNamesAtomic cont)
getEventNamesAtomic (Read _ _ _ cont) = getEventNamesAtomic cont
getEventNamesAtomic (Writes w) = getEventNamesWrites w

getEventNamesWrites :: Writes f v -> Set String
getEventNamesWrites (Write _ _ _ cont) = getEventNamesWrites cont
getEventNamesWrites (Choreo choreo) = getEventNames choreo

-- getEventNames :: Choreo f v -> Set String
-- getEventNames End = Set.empty
-- getEventNames (Send _ _ choices) =
--     Set.unions (map (getEventNames . snd) choices)
-- getEventNames (Nonce _ _ _ cont) =
--     getEventNames cont
-- getEventNames (Lock _ atomic) =
--     getEventNamesAtomic atomic
-- getEventNames (Event _ name _ cont) =
--     Set.insert name (getEventNames cont)
-- getEventNames (Choice _ cont) = Set.unions (map getEventNames cont)

-- getEventNamesAtomic :: Atomic f v (Choreo f v) -> Set String
-- getEventNamesAtomic (Read _ _ cont) = getEventNamesAtomic cont
-- getEventNamesAtomic (Write _ _ cont) = getEventNamesAtomic cont
-- getEventNamesAtomic (Branch _ _ cont1 cont2) =
--     getEventNamesAtomic cont1 `Set.union` getEventNamesAtomic cont2
-- getEventNamesAtomic (Unlock choreo) = getEventNames choreo
-- getEventNamesAtomic (Let _ _ cont) = getEventNamesAtomic cont
-- getEventNamesAtomic (Event' _ _ cont) = getEventNamesAtomic cont
-- Get active agents in choreography
-- getAgents :: (Ord f, Ord v) => Choreo f v -> Set (Agent f v)
-- getAgents End = Set.empty
-- getAgents (Send a1 a2 choices) =
--     Set.insert a1 $ Set.insert a2 $
--     Set.unions (map (getAgents . snd) choices)
-- getAgents (Nonce a _ _ cont) =
--     Set.insert a (getAgents cont)
-- getAgents (Event a _ _ cont) =
--     Set.insert a (getAgents cont)
-- getAgents (Lock a atomic) =
--     Set.insert a (getAgentsAtomic getAgents atomic)
-- getAgents (Choice a choices) =
--     Set.insert a $ Set.unions (map getAgents choices)


-- getAgentsInitial :: (Ord f, Ord v) => InitialChoreo f v -> Set (Agent f v)
-- getAgentsInitial (IEnd goals) = getAgentsGoals goals
-- getAgentsInitial (ISend a1 a2 choices) =
--     Set.insert a1 $ Set.insert a2 $
--     Set.unions (map (getAgentsInitial . snd) choices)
-- getAgentsInitial (INonce a _ _ cont) =
--     Set.insert a (getAgentsInitial cont)
-- getAgentsInitial (ILock a atomic) =
--     Set.insert a (getAgentsAtomic getAgentsInitial atomic)
-- getAgentsInitial (IChoice a choices) =
--     Set.insert a $ Set.unions (map getAgentsInitial choices)
-- getAgentsInitial (IEvent a _ _ cont) =
--     Set.insert a (getAgentsInitial cont)
-- getAgentsInitial (ILet1 _ _ cont) =
--     getAgentsInitial cont

-- getAgentsGoals :: (Ord f, Ord v) => Goals f v -> Set (Agent f v)
-- getAgentsGoals EndGoals = Set.empty
-- getAgentsGoals (Secret agents _ rest) =
--     Set.fromList agents `Set.union` getAgentsGoals rest
-- getAgentsGoals (WeakAuth a1 a2 _ rest) =
--     Set.fromList [a1, a2] `Set.union` getAgentsGoals rest
-- getAgentsGoals (StrongAuth a1 a2 _ rest) =
--     Set.fromList [a1, a2] `Set.union` getAgentsGoals rest

-- getAgentsAtomic :: (Ord f, Ord v) => (c -> Set (Agent f v)) -> Atomic f v c -> Set (Agent f v)
-- getAgentsAtomic f (Read _ _ cont) = getAgentsAtomic f cont
-- getAgentsAtomic f (Write _ _ cont) = getAgentsAtomic f cont
-- getAgentsAtomic f (Branch _ _ cont1 cont2) =
--     getAgentsAtomic f cont1 `Set.union` getAgentsAtomic f cont2
-- getAgentsAtomic f (Unlock choreo) = f choreo
-- getAgentsAtomic f (Let _ _ cont) = getAgentsAtomic f cont
-- getAgentsAtomic f (Event' _ _ cont) = getAgentsAtomic f cont


-- -- Collect function symbols from Choreo with their arities
-- -- Returns a Map from function symbol to its arity (using first occurrence if used with multiple arities)
-- collectFunctionSymbols :: Ord f => Choreo f v -> Map f Int
-- collectFunctionSymbols End = Map.empty
-- collectFunctionSymbols (Send a1 a2 choices) =
--     collectFunctionSymbolsAgent a1 `Map.union`
--     collectFunctionSymbolsAgent a2 `Map.union`
--     Map.unions (map (\(t, ic) -> collectFunctionSymbolsTerm t `Map.union` collectFunctionSymbols ic) choices)
-- collectFunctionSymbols (Nonce a _ ts cont) =
--     collectFunctionSymbolsAgent a `Map.union` Map.unions (map collectFunctionSymbolsTerm ts) `Map.union` collectFunctionSymbols cont
-- collectFunctionSymbols (Lock a atomic) =
--     collectFunctionSymbolsAgent a `Map.union` collectFunctionSymbolsAtomic atomic
-- collectFunctionSymbols (Choice a choices) =
--     collectFunctionSymbolsAgent a `Map.union` Map.unions (map collectFunctionSymbols choices)
-- collectFunctionSymbols (Event a _ terms cont) =
--     collectFunctionSymbolsAgent a `Map.union`
--     Map.unions (map collectFunctionSymbolsTerm terms) `Map.union`
--     collectFunctionSymbols cont

-- collectFunctionSymbolsAgent :: Ord f => Agent f v -> Map f Int
-- collectFunctionSymbolsAgent (Trusted f) = Map.singleton f 0
-- collectFunctionSymbolsAgent (Untrusted _) = Map.empty

-- collectFunctionSymbolsTerm :: Ord f => Term f v -> Map f Int
-- collectFunctionSymbolsTerm (Var _) = Map.empty
-- collectFunctionSymbolsTerm (Fun f args) =
--     Map.insert f (length args) (Map.unions (map collectFunctionSymbolsTerm args))

-- collectFunctionSymbolsAtomic :: Ord f => Atomic f v (Choreo f v) -> Map f Int
-- collectFunctionSymbolsAtomic (Read t1 t2 cont) =
--     collectFunctionSymbolsTerm t1 `Map.union`
--     collectFunctionSymbolsTerm t2 `Map.union`
--     collectFunctionSymbolsAtomic cont
-- collectFunctionSymbolsAtomic (Write t1 t2 cont) =
--     collectFunctionSymbolsTerm t1 `Map.union`
--     collectFunctionSymbolsTerm t2 `Map.union`
--     collectFunctionSymbolsAtomic cont
-- collectFunctionSymbolsAtomic (Branch t1 t2 cont1 cont2) =
--     collectFunctionSymbolsTerm t1 `Map.union`
--     collectFunctionSymbolsTerm t2 `Map.union`
--     collectFunctionSymbolsAtomic cont1 `Map.union`
--     collectFunctionSymbolsAtomic cont2
-- collectFunctionSymbolsAtomic (Let _ t cont) =
--     collectFunctionSymbolsTerm t `Map.union`
--     collectFunctionSymbolsAtomic cont
-- collectFunctionSymbolsAtomic (Event' _ terms cont) =
--     Map.unions (map collectFunctionSymbolsTerm terms) `Map.union`
--     collectFunctionSymbolsAtomic cont
-- collectFunctionSymbolsAtomic (Unlock choreo) = collectFunctionSymbols choreo

