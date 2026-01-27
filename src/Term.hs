{-# LANGUAGE MultiParamTypeClasses #-}
module Term where
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Void
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State


data Term f v
    = Var v
    | Fun f [Term f v]
    deriving (Eq,Ord)


termSize :: Term f v -> Int
termSize (Var _) = 1 :: Int 
termSize (Fun _ ts) = 1 + sum (map termSize ts)

instance (Show f, Show v) => Show (Term f v) where
    show (Var v) = show v
    show (Fun f []) = show f ++ "()"
    show (Fun f args) = show f ++ "(" ++ intercalate ", " (map show args) ++ ")"
      where
        intercalate _ [] = ""
        intercalate _ [x] = x
        intercalate sep (x:xs) = x ++ sep ++ intercalate sep xs




type GTerm f = Term f Void

fvt :: Ord v => Term f v -> Set v
fvt (Var v) = Set.singleton v
fvt (Fun _ ts) = foldr (Set.union . fvt) Set.empty ts

substitute :: Eq v => v -> Term f v -> Term f v -> Term f v
substitute x t (Var y) = if x == y then t else Var y
substitute x t (Fun f ts) = Fun f (map (substitute x t) ts)

substituteMap :: Ord v => Map v (Term f v) -> Term f v -> Term f v
substituteMap m (Var x)
  | Just t <- Map.lookup x m = t 
  | otherwise = Var x
substituteMap m (Fun f ts) = Fun f (map (substituteMap m) ts)

mapv :: (u -> v) -> Term f u -> Term f v
mapv f (Var x) = Var (f x)
mapv f (Fun g ts) = Fun g (map (mapv f) ts)

mapf :: (f -> g) -> Term f v -> Term g v
mapf _ (Var x) = Var x
mapf f (Fun g ts) = Fun (f g) (map (mapf f) ts)

mapfM :: Monad m => (f -> m g) -> Term f v -> m (Term g v) 
mapfM _ (Var x) = return $ Var x
mapfM f (Fun g ts) = do 
  g' <- f g
  ts' <- mapM (mapfM f) ts
  return $ Fun g' ts'

class NameGenerator ng name where
    isFresh :: Eq name => ng -> name -> Bool
    fresh :: Eq name => State ng name
    register :: Eq name => ng -> name -> ng