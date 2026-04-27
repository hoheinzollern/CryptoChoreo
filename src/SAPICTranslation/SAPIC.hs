{-# LANGUAGE LambdaCase #-}
module SAPIC where
import Term
import Local
import Data.Set (Set)
import qualified Data.Set as Set

-- | SAPIC+ process algebra (Tamarin-flavored, stateful pi calculus).
data SapicProcess
    = SZero
    | SOut (Term String String) SapicProcess
    | SIn  (Term String String) SapicProcess
    | SNew String SapicProcess
    | SLet String (Term String String) SapicProcess
    | SEvent String [Term String String] SapicProcess
    | SIf  (Term String String) (Term String String) SapicProcess SapicProcess
    | SChoice [SapicProcess]
    | SPar SapicProcess SapicProcess
    | SBang SapicProcess
    | SLookup (Term String String) String SapicProcess SapicProcess
    | SInsert (Term String String) (Term String String) SapicProcess
    | SLock   (Term String String) SapicProcess
    | SUnlock (Term String String) SapicProcess
    deriving (Show, Eq)

-- | Translate a Local IR program into a SAPIC+ process.
localToSapic :: Local String String -> SapicProcess
localToSapic LEnd = SZero
localToSapic (LSend t l) = SOut t (localToSapic l)
localToSapic (LReceive v l) = SIn (Var v) (localToSapic l)
-- Each top-level atomic block starts with an empty lock set; locks
-- accumulate as we traverse LRead nodes and are all released when we
-- hit the LWrites/Local boundary that exits the atomic block.
localToSapic (LAtomic a) = atomicToSapic Set.empty a

-- | A lock identifier: a (cell, address) pair. Used in a Set to know
-- which locks are currently held in the surrounding atomic block.
type LockKey = (String, Term String String)

atomicToSapic :: Set LockKey -> LAtomic String String -> SapicProcess
atomicToSapic ls (LNonce v a)          = SNew v (atomicToSapic ls a)
atomicToSapic ls (LLet v t a)          = SLet v t (atomicToSapic ls a)
atomicToSapic ls (LEvent name ts a)    = SEvent name ts (atomicToSapic ls a)
atomicToSapic ls (LBranch t1 t2 a1 a2) = SIf t1 t2 (atomicToSapic ls a1) (atomicToSapic ls a2)
atomicToSapic ls (LChoice as)          = SChoice (map (atomicToSapic ls) as)
-- | Cell read. Acquire a lock on (cell, addr) iff
--   (a) we don't already hold one for this key in the surrounding
--       atomic block, and
--   (b) the syntactic continuation reaches an LWrite for the same
--       key (i.e., this is a read-modify-write critical section --
--       a pure read needs no lock since SAPIC+ lookup is concurrent
--       safe).
-- Read body: lookup with else branch initializing from
-- memory_initial_value (so the first reader doesn't hit a dead end).
atomicToSapic ls (LRead cell v addr a) =
    let key       = cellKey cell addr
        ck        = (cell, addr)
        held      = Set.member ck ls
        needsLock = not held && containsWriteFor cell addr a
        ls'       = if needsLock then Set.insert ck ls else ls
        cont      = atomicToSapic ls' a
        initVal   = Fun "memory_initial_value" []
        initPath  = SLet v initVal (SInsert key (Var v) cont)
        readBody  = SLookup key v cont initPath
    in if needsLock then SLock key readBody else readBody
atomicToSapic ls (LWrites w)           = writesToSapic ls w

-- | Translate a sequence of writes followed by a Local continuation.
-- Each LWrite emits insert <'cell', addr>, value. When we hit the
-- Local boundary (exit of the atomic block) we release every lock
-- accumulated during the block.
writesToSapic :: Set LockKey -> LWrites String String -> SapicProcess
writesToSapic ls (LWrite cell addr value w) =
    SInsert (cellKey cell addr) value (writesToSapic ls w)
writesToSapic ls (Local l) =
    foldr (\(c, a) p -> SUnlock (cellKey c a) p) (localToSapic l) (Set.toList ls)

-- | Build the SAPIC+ table key for a (cell, address) pair as the pair
-- term <'cell', addr>. The cell name is wrapped in single quotes to
-- become a Tamarin public-name constant; the printer renders Fun ""
-- as the pair constructor < ... >.
cellKey :: String -> Term String String -> Term String String
cellKey cell addr = Fun "" [Fun ("'" ++ cell ++ "'") [], addr]

-- | True iff the LAtomic contains an LWrite to the given (cell, addr)
-- key somewhere in its syntactic continuation. Used to decide whether
-- an LRead opens a read-modify-write critical section that needs a
-- lock, or is a pure read that doesn't.
containsWriteFor :: String -> Term String String -> LAtomic String String -> Bool
containsWriteFor cell addr = go
  where
    go (LNonce _ a)        = go a
    go (LLet _ _ a)        = go a
    go (LEvent _ _ a)      = go a
    go (LChoice as)        = any go as
    go (LBranch _ _ a1 a2) = go a1 || go a2
    go (LRead _ _ _ a)     = go a
    go (LWrites w)         = goW w

    goW (LWrite c addr' _ rest)
      | c == cell && addr' == addr = True
      | otherwise                  = goW rest
    goW (Local _) = False

-- | Append `unlock key;` immediately before every SZero leaf in the
-- process. Used to release the API serialization baton at every point
-- the wrapped agent's body terminates. Idempotent for multiple calls.
appendUnlock :: Term String String -> SapicProcess -> SapicProcess
appendUnlock key = go
  where
    go SZero               = SUnlock key SZero
    go (SOut t p)          = SOut t (go p)
    go (SIn t p)           = SIn  t (go p)
    go (SNew x p)          = SNew x (go p)
    go (SLet x t p)        = SLet x t (go p)
    go (SEvent name ts p)  = SEvent name ts (go p)
    go (SIf t1 t2 p q)     = SIf t1 t2 (go p) (go q)
    go (SChoice ps)        = SChoice (map go ps)
    go (SPar p q)          = SPar (go p) (go q)
    go (SBang p)           = SBang (go p)
    go (SLookup t x p q)   = SLookup t x (go p) (go q)
    go (SInsert t1 t2 p)   = SInsert t1 t2 (go p)
    go (SLock t p)         = SLock   t (go p)
    go (SUnlock t p)       = SUnlock t (go p)

-- | Mark every Var that names an agent in the given set with a leading
-- '$' so that SAPIC+ treats it as a public agent identifier (otherwise
-- the well-formedness checker rejects the unbound agent name).
markAgents :: Set String -> SapicProcess -> SapicProcess
markAgents agents = go
  where
    go SZero               = SZero
    go (SOut t p)          = SOut (mt t) (go p)
    go (SIn t p)           = SIn  (mt t) (go p)
    go (SNew x p)          = SNew x (go p)
    go (SLet x t p)        = SLet x (mt t) (go p)
    go (SEvent name ts p)  = SEvent name (map mt ts) (go p)
    go (SIf t1 t2 p q)     = SIf (mt t1) (mt t2) (go p) (go q)
    go (SChoice ps)        = SChoice (map go ps)
    go (SPar p q)          = SPar (go p) (go q)
    go (SBang p)           = SBang (go p)
    go (SLookup t x p q)   = SLookup (mt t) x (go p) (go q)
    go (SInsert t1 t2 p)   = SInsert (mt t1) (mt t2) (go p)
    go (SLock t p)         = SLock   (mt t) (go p)
    go (SUnlock t p)       = SUnlock (mt t) (go p)

    mt (Var v)
      | Set.member v agents = Var ('$' : v)
      | otherwise           = Var v
    -- Trusted agents appear in the IR as 0-ary Fun (e.g., Fun "s" []);
    -- promote them to public agent variables ($s) the same way.
    mt (Fun f [])
      | Set.member f agents = Var ('$' : f)
      | otherwise           = Fun f []
    mt (Fun f args)         = Fun f (map mt args)
