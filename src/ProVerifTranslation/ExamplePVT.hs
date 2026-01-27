module ExamplePVT where
import Term
import qualified Text.PrettyPrint as PP
import Local
import ExampleAlgebra
import qualified Data.Bifunctor as Bifunctor
import Data.Map (Map)
import qualified Data.Map as Map
import Choreo (Agent(..))

a2bs = "agent2bitstring"
skey2bs = "skey2bitstring"
pubkey2bs = "pubkey2bitstring"
privkey2bs = "privkey2bitstring"


termToSK agents (Fun SK [t1,t2])
    | t1 `elem` agents && t2 `elem` agents = Fun (show SK) [agentTermToPV t1, agentTermToPV t2]
termToSK agents t = Fun "skdf" [termToPV agents t]

termToPubKey agents (Fun PK [t])
    | t `elem` agents = Fun (show PK) [agentTermToPV t]
termToPubKey agents (Fun Pubk [t]) = Fun (show Pubk) [termToPrivkey agents t]
termToPubKey agents t = Fun "kdf" [termToPV agents t]

termToPrivkey agents (Fun Inv [t]) = Fun (show Inv) [termToPubKey agents t]
termToPrivkey agents t = Fun "invkdf" [termToPV agents t]

agentTermToPV (Var x) = Var x
agentTermToPV (Fun (Other f) []) = Fun f []

-- convert to a proverif term of type bitstring
termToPV agents t
    | t `elem` agents = Fun a2bs [agentTermToPV t]
termToPV agents (Var x) = Var x
termToPV agents (Fun Pair [t1,t2]) = Fun "" [termToPV agents t1,termToPV agents t2]
termToPV agents (Fun SK [t1,t2])
    | t1 `elem` agents && t2 `elem` agents = Fun skey2bs [Fun (show SK) [agentTermToPV t1,agentTermToPV t2]]
termToPV agents (Fun PK [t])
    | t `elem` agents = Fun pubkey2bs [Fun (show PK) [agentTermToPV t]]
termToPV agents (Fun Inv [t]) = Fun privkey2bs [Fun (show Inv) [termToPubKey agents t]]
termToPV agents (Fun Pubk [t]) = Fun pubkey2bs [Fun (show Pubk) [termToPrivkey agents t]]
termToPV agents (Fun VInv [t]) = Fun (show VInv) [termToPrivkey agents t]
termToPV agents (Fun f [t,k])
    | f `elem` [Scrypt,DScrypt,VScrypt] =
        Fun (show f) [termToPV agents t,termToSK agents k]
termToPV agents (Fun f [t,k])
    | f `elem` [Crypt,Open,VSign] =
        Fun (show f) [termToPV agents t,termToPubKey agents k]
termToPV agents (Fun f [t,k])
    | f `elem` [Sign,DCrypt,VCrypt] =
        Fun (show f) [termToPV agents t,termToPrivkey agents k]
termToPV agents (Fun f ts) = Fun (show f) (map (termToPV agents) ts)


stringifyLocal agents LEnd = LEnd
stringifyLocal agents (LReceive v l) = LReceive v (stringifyLocal agents l)
stringifyLocal agents (LSend t l) = LSend (termToPV agents t) (stringifyLocal agents l)
stringifyLocal agents (LAtomic a) = LAtomic (stringifyLAtomic agents a)

stringifyLAtomic agents (LNonce v a) = LNonce v (stringifyLAtomic agents a)
stringifyLAtomic agents (LLet v t a) = LLet v (termToPV agents t) (stringifyLAtomic agents a)
stringifyLAtomic agents (LEvent name ts a) = LEvent name (map (termToPV agents) ts) (stringifyLAtomic agents a)
stringifyLAtomic agents (LChoice atomics) = LChoice (map (stringifyLAtomic agents) atomics)
stringifyLAtomic agents (LBranch t1 t2 a1 a2) =
    LBranch (termToPV agents t1) (termToPV agents t2) (stringifyLAtomic agents a1) (stringifyLAtomic agents a2)
stringifyLAtomic agents (LRead name v t2 a) =
    LRead name v (termToPV agents t2) (stringifyLAtomic agents a)
stringifyLAtomic agents (LWrites w) = LWrites (stringifyLWrites agents w)

stringifyLWrites agents (LWrite name t1 t2 w) =
    LWrite name (termToPV agents t1) (termToPV agents t2) (stringifyLWrites agents w)
stringifyLWrites agents (Local l) = Local (stringifyLocal agents l)

-- | Unfold initial knowledge in Local behavior before stringification
-- This ensures terms are substituted at the Func level, not after termToPV conversion
unfoldLocalKnowledge :: Map String (Term Func String) -> Local Func String -> Local Func String
unfoldLocalKnowledge knowledgeMap = unfoldLocal
  where
    unfoldTerm :: Term Func String -> Term Func String
    unfoldTerm (Var v) = case Map.lookup v knowledgeMap of
        Just term -> unfoldTerm term
        Nothing -> Var v
    unfoldTerm (Fun f args) = Fun f (map unfoldTerm args)
    
    unfoldLocal :: Local Func String -> Local Func String
    unfoldLocal LEnd = LEnd
    unfoldLocal (LReceive v l) = LReceive v (unfoldLocal l)
    unfoldLocal (LSend t l) = LSend (unfoldTerm t) (unfoldLocal l)
    unfoldLocal (LAtomic a) = LAtomic (unfoldLAtomic a)
    
    unfoldLAtomic :: LAtomic Func String -> LAtomic Func String
    unfoldLAtomic (LNonce v a) = LNonce v (unfoldLAtomic a)
    unfoldLAtomic (LLet v t a) = LLet v (unfoldTerm t) (unfoldLAtomic a)
    unfoldLAtomic (LEvent name ts a) = LEvent name (map unfoldTerm ts) (unfoldLAtomic a)
    unfoldLAtomic (LChoice atomics) = LChoice (map unfoldLAtomic atomics)
    unfoldLAtomic (LBranch t1 t2 a1 a2) = LBranch (unfoldTerm t1) (unfoldTerm t2) (unfoldLAtomic a1) (unfoldLAtomic a2)
    unfoldLAtomic (LRead name v t2 a) = LRead name v (unfoldTerm t2) (unfoldLAtomic a)
    unfoldLAtomic (LWrites w) = LWrites (unfoldLWrites w)
    
    unfoldLWrites :: LWrites Func String -> LWrites Func String
    unfoldLWrites (LWrite name t1 t2 w) = LWrite name (unfoldTerm t1) (unfoldTerm t2) (unfoldLWrites w)
    unfoldLWrites (Local l) = Local (unfoldLocal l)