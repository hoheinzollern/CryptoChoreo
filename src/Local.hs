module Local where
import Term
import Data.Set (Set)
import qualified Data.Set as Set

data Local f v
    = LEnd
    | LSend (Term f v) (Local f v)
    | LReceive v (Local f v)
    | LAtomic (LAtomic f v)
    deriving (Show,Eq)

data LAtomic f v
    = LNonce v (LAtomic f v)
    | LLet v (Term f v) (LAtomic f v)
    | LEvent String [Term f v] (LAtomic f v)
    | LChoice [LAtomic f v]
    | LBranch (Term f v) (Term f v) (LAtomic f v) (LAtomic f v)
    | LRead String v (Term f v) (LAtomic f v)
    | LWrites (LWrites f v)
    deriving (Show,Eq)

data LWrites f v
    = LWrite String (Term f v) (Term f v) (LWrites f v)
    | Local (Local f v)
    deriving (Show,Eq)

data LocalUnion f v 
    = LULocal (Local f v)
    | LUAtomic (LAtomic f v)
    | LUWrites (LWrites f v)
    deriving (Show,Eq)

toLocal :: LocalUnion f v -> Local f v
toLocal (LULocal l) = l
toLocal (LUAtomic a) = LAtomic a
toLocal (LUWrites w) = LAtomic (LWrites w)

toLAtomic :: LocalUnion f v -> LAtomic f v
toLAtomic (LULocal l) = LWrites (Local l)
toLAtomic (LUAtomic a) = a
toLAtomic (LUWrites w) = LWrites w

toLWrites :: LocalUnion f v -> LWrites f v
toLWrites (LULocal l) = Local l
toLWrites (LUAtomic a) = Local (LAtomic a)
toLWrites (LUWrites w) = w

fvl :: Ord v => Local f v -> Set v
fvl LEnd = Set.empty
fvl (LSend t l) = Set.union (fvt t) (fvl l)
fvl (LReceive v l) = Set.delete v (fvl l)
fvl (LAtomic a) = fvla a

fvla :: Ord v => LAtomic f v -> Set v
fvla (LBranch t1 t2 c1 c2) = Set.unions [fvt t1, fvt t2, fvla c1, fvla c2]
fvla (LNonce v l) = Set.delete v (fvla l)
fvla (LLet v t l) = Set.union (fvt t) (Set.delete v (fvla l))
fvla (LEvent _ ts l) = Set.unions (fvla l : map fvt ts)
fvla (LChoice ls) = foldr (Set.union . fvla) Set.empty ls
fvla (LRead _ v t2 c) = Set.unions [fvt t2, Set.delete v (fvla c)]
fvla (LWrites w) = fvlw w

fvlw :: Ord v => LWrites f v -> Set v
fvlw (LWrite _ t1 t2 c) = Set.unions [fvt t1, fvt t2, fvlw c]
fvlw (Local l) = fvl l

removeNoopLocal :: (Eq f, Eq v) => Local f v -> Local f v
removeNoopLocal LEnd = LEnd
removeNoopLocal (LSend t l) = LSend t (removeNoopLocal l)
removeNoopLocal (LReceive v l) = LReceive v (removeNoopLocal l)
removeNoopLocal (LAtomic a) =
    case removeNoopLAtomic a of
        LWrites (Local l) -> l
        a' -> LAtomic a'

removeNoopLAtomic :: (Eq f, Eq v) => LAtomic f v -> LAtomic f v
removeNoopLAtomic (LNonce v l) = LNonce v (removeNoopLAtomic l)
removeNoopLAtomic (LLet v t l) = LLet v t (removeNoopLAtomic l)
removeNoopLAtomic (LEvent name ts l) = LEvent name ts (removeNoopLAtomic l)
removeNoopLAtomic (LChoice ls) =
    case filter (/= LWrites (Local LEnd)) $ map removeNoopLAtomic ls of
        [] -> LWrites (Local LEnd)
        [l] -> l
        ls' -> LChoice ls'
removeNoopLAtomic (LBranch t1 t2 l1 l2) =
    case (removeNoopLAtomic l1, removeNoopLAtomic l2) of
        (l1', l2') -> if l1' == l2' then l1' else LBranch t1 t2 l1' l2'
removeNoopLAtomic (LRead name t1 t2 l) = LRead name t1 t2 (removeNoopLAtomic l)
removeNoopLAtomic (LWrites w) = LWrites (removeNoopLWrites w)

removeNoopLWrites :: (Eq f, Eq v) => LWrites f v -> LWrites f v
removeNoopLWrites (LWrite name t1 t2 l) = LWrite name t1 t2 (removeNoopLWrites l)
removeNoopLWrites (Local l) = Local (removeNoopLocal l)
