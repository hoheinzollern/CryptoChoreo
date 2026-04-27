{-# LANGUAGE LambdaCase #-}
module SAPIC where
import Term
import Local
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

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
-- memory_initial_value. The else branch uses a *renamed* variable
-- (v ++ "_init") because Tamarin's well-formedness check rejects
-- binding the same name twice statically -- even when the bindings
-- are in mutually-exclusive lookup branches. The continuation is
-- duplicated and substituted accordingly.
atomicToSapic ls (LRead cell v addr a) =
    let key       = cellKey cell addr
        ck        = (cell, addr)
        held      = Set.member ck ls
        needsLock = not held && containsWriteFor cell addr a
        ls'       = if needsLock then Set.insert ck ls else ls
        cont      = atomicToSapic ls' a
        -- Alpha-rename ALL binders in the duplicated copy (then
        -- additionally rename v -> v_init for the init-path lookup).
        contInitBase = alphaRenameBinders "_init" cont
        contInit     = renameVar v (v ++ "_init") contInitBase
        initVal      = Fun "memory_initial_value" []
        initPath     = SLet (v ++ "_init") initVal (SInsert key (Var (v ++ "_init")) contInit)
        readBody     = SLookup key v cont initPath
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

-- | Rename free uses of Var oldName to Var newName everywhere in a
-- process. Only the supplied name is rewritten; other binders are
-- left alone. Used for the LRead's lookup-bound variable so the
-- else-branch's `let v = memory_initial_value` doesn't collide with
-- the lookup's `as v`.
renameVar :: String -> String -> SapicProcess -> SapicProcess
renameVar old new = renameVars (Map.singleton old new)

-- | Apply a renaming map to every Var in a process AND to every
-- locally-introduced binder (SNew/SLet/SLookup/SIn-Var). Used to
-- alpha-rename a process subtree being duplicated between mutually-
-- exclusive lookup branches: Tamarin's well-formedness check rejects
-- syntactically duplicate binders even in disjoint branches.
renameVars :: Map String String -> SapicProcess -> SapicProcess
renameVars m = go
  where
    rn x = Map.findWithDefault x x m
    go SZero               = SZero
    go (SOut t p)          = SOut (rt t) (go p)
    go (SIn t p)           = SIn  (rt t) (go p)
    go (SNew x p)          = SNew (rn x) (go p)
    go (SLet x t p)        = SLet (rn x) (rt t) (go p)
    go (SEvent name ts p)  = SEvent name (map rt ts) (go p)
    go (SIf t1 t2 p q)     = SIf (rt t1) (rt t2) (go p) (go q)
    go (SChoice ps)        = SChoice (map go ps)
    go (SPar p q)          = SPar (go p) (go q)
    go (SBang p)           = SBang (go p)
    go (SLookup t x p q)   = SLookup (rt t) (rn x) (go p) (go q)
    go (SInsert t1 t2 p)   = SInsert (rt t1) (rt t2) (go p)
    go (SLock t p)         = SLock   (rt t) (go p)
    go (SUnlock t p)       = SUnlock (rt t) (go p)

    rt (Var v) = Var (rn v)
    rt (Fun f args) = Fun f (map rt args)

-- | Collect the set of names introduced by binders in a process.
boundNames :: SapicProcess -> Set String
boundNames = go
  where
    go SZero               = Set.empty
    go (SOut _ p)          = go p
    go (SIn t p)           = Set.union (varsIn t) (go p)
    go (SNew x p)          = Set.insert x (go p)
    go (SLet x _ p)        = Set.insert x (go p)
    go (SEvent _ _ p)      = go p
    go (SIf _ _ p q)       = Set.union (go p) (go q)
    go (SChoice ps)        = Set.unions (map go ps)
    go (SPar p q)          = Set.union (go p) (go q)
    go (SBang p)           = go p
    go (SLookup _ x p q)   = Set.insert x (Set.union (go p) (go q))
    go (SInsert _ _ p)     = go p
    go (SLock _ p)         = go p
    go (SUnlock _ p)       = go p

    -- Variables that an `in(pattern)` binds: any Var inside the term.
    varsIn (Var v) = Set.singleton v
    varsIn (Fun _ args) = Set.unions (map varsIn args)

-- | Alpha-rename every locally-introduced binder in a process by
-- appending a suffix. Used to duplicate the LRead continuation into
-- the lookup else-branch without binding the same name twice.
alphaRenameBinders :: String -> SapicProcess -> SapicProcess
alphaRenameBinders suffix p =
    let renamed = Map.fromSet (++ suffix) (boundNames p)
    in renameVars renamed p

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
