{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
module Algebraic where
import Util
import Term
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map

class (Ord v, Show v, Read v) => VarLike v

instance VarLike String

data (Ord f) => Algebra f = Algebra {
    -- Match destructors with constructors
    reduces :: forall v. VarLike v => Term f v -> Maybe (Term f v),

    -- The set of public functions
    public :: f -> Int -> Bool,

    -- constructor-destructor part:
    -- Destructor Lookup. Left if the applicable destructor is decryption and right if it is projection
    -- Returns both verifier and destructors
    dl :: Map f (Either f [f]),
    -- Verifier Lookup. Left if key is needed to verify, right if not
    vl :: Map f (Either f f),
    -- Key Relation. For a given decryption operator, map encryption keys to decryption keys
    kr :: forall v. VarLike v => Map f (Term f v -> Maybe (Term f v)),

    -- return the set of ways to represent the given term as an f-term
    topdec :: forall v. VarLike v => f -> Term f v -> Set [Term f v],
    -- for an operator f return all g such that f(t1,...,tn) = g(s1,...,sn) for some t1,...,tn,s1,...,sn
    synonyms :: f -> Set f,
    -- Constant symbol meaning successful verification
    tt :: f
}

topSynonyms :: Ord a => Algebra a -> Term a v -> Set a
topSynonyms _ (Var _) = Set.empty
topSynonyms alg (Fun f _) = synonyms alg f

tru :: Ord f => Algebra f -> Term f v
tru alg = Fun (tt alg) []

reduce :: (VarLike v, Ord f) => Algebra f -> Term f v -> Term f v
reduce _ (Var v) = Var v
reduce alg (Fun f ts) =
  let ts' = map (reduce alg) ts
   in case reduces alg (Fun f ts') of
        Just t -> t
        Nothing -> Fun f ts'

-- the equational validity problem:
aeq :: (VarLike v, Ord f) => Algebra f -> Term f v -> Term f v -> Bool
aeq alg t1 t2 =
  --trace (show t1 ++ " = " ++ show t2) $
  aeq' alg (reduce alg t1, reduce alg t2)
  where
  aeq' _ (Var x, Var y) = x == y
  aeq' alg (Fun f ts, t) =
    any (all (aeq' alg) . zip ts) (topdec alg f t)
  aeq' _ _ = False

explode :: (Ord f, VarLike v) => Algebra f -> Term f v -> Set (Term f v)
explode _ (Var x) = Set.singleton (Var x)
explode alg (Fun f ts) = 
  (\ g -> (Set.map (Fun g) . expandSetList . map (explode alg)) =<<< topdec alg g (Fun f ts)) =<<< synonyms alg f
