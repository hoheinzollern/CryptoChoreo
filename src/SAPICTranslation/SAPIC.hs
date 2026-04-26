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
-- Cell reads/writes are not yet supported: they raise a runtime error
-- pointing at the construct that still needs to be implemented.
localToSapic :: Local String String -> SapicProcess
localToSapic LEnd = SZero
localToSapic (LSend t l) = SOut t (localToSapic l)
localToSapic (LReceive v l) = SIn (Var v) (localToSapic l)
localToSapic (LAtomic a) = atomicToSapic a

atomicToSapic :: LAtomic String String -> SapicProcess
atomicToSapic (LNonce v a)            = SNew v (atomicToSapic a)
atomicToSapic (LLet v t a)            = SLet v t (atomicToSapic a)
atomicToSapic (LEvent name ts a)      = SEvent name ts (atomicToSapic a)
atomicToSapic (LBranch t1 t2 a1 a2)   = SIf t1 t2 (atomicToSapic a1) (atomicToSapic a2)
atomicToSapic (LChoice as)            = SChoice (map atomicToSapic as)
atomicToSapic (LRead{})               = error "SAPIC.atomicToSapic: cell reads (LRead) not yet implemented"
atomicToSapic (LWrites w)             = writesToSapic w

writesToSapic :: LWrites String String -> SapicProcess
writesToSapic (LWrite{})  = error "SAPIC.writesToSapic: cell writes (LWrite) not yet implemented"
writesToSapic (Local l)   = localToSapic l

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
