{-# LANGUAGE LambdaCase #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Util where

import qualified Data.Bifunctor as Bifunctor
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Map (Map)
import qualified Data.Map as Map

-- =============================================================================
-- SET UTILITIES
-- =============================================================================

-- | Convert Maybe Set to Set, returning empty set for Nothing
setFromMaybe :: Maybe (Set a) -> Set a
setFromMaybe (Just a) = a
setFromMaybe Nothing = Set.empty

-- | Insert element into Maybe Set, creating singleton if Nothing
insertMaybe :: Ord a => a -> Maybe (Set a) -> Set a
insertMaybe a = Set.insert a . setFromMaybe

-- | Monadic bind for Sets - apply function to each element and union results
(=<<<) :: Ord b => (a -> Set b) -> Set a -> Set b
f =<<< s = Set.foldl' (\acc x -> Set.union acc (f x)) Set.empty s

-- | Find first successful result from applying function to Set elements
($<) :: Ord b => (a -> Maybe b) -> Set a -> Maybe b
f $< s = Set.foldr (\ x -> (\case Just y -> Just y; Nothing -> f x)) Nothing s

-- | Stateful monadic bind for Sets
(=<<<<) :: Ord b => (a -> State s (Set b)) -> State s (Set a) -> State s (Set b)
f =<<<< sm = State.state (\ s ->
    let (as,s') = State.runState sm s
    in Set.foldl' (\ (bs,s) a ->
        let (bs',s') = State.runState (f a) s
        in (Set.union bs' bs,s')) (Set.empty,s') as
  )

-- | Apply stateful function to Set elements
($<<<<) :: Ord b => (a -> State s (Set b)) -> Set a -> State s (Set b)
f $<<<< s = f =<<<< return s

-- | Cartesian product of two Sets with combining function
crossSets :: Ord c => (a -> b -> c) -> Set a -> Set b -> Set c
crossSets f s1 s2 = (\ x -> Set.map (f x) s2) =<<< s1

-- | Cartesian product of list of Sets to Set of lists
expandSetList :: Ord a => [Set a] -> Set [a]
expandSetList = foldr (crossSets (:)) (Set.singleton [])

-- not actually intersections, as intersections [] should be the universal set. More like "elements common to all sets"
intersections :: Ord a => [Set a] -> Set a
intersections [] = Set.empty
intersections (s : ss) = foldr Set.intersection s ss

-- =============================================================================
-- MONAD UTILITIES
-- =============================================================================

-- | Convert a Maybe containing a monadic action to a monadic Maybe
monadSwap :: Monad m => Maybe (m a) -> m (Maybe a)
monadSwap Nothing = return Nothing
monadSwap (Just s) = fmap Just s

-- | Conditional constructor - return Just if predicate holds, Nothing otherwise
ensure :: (a -> Bool) -> a -> Maybe a
ensure p a = if p a then Just a else Nothing

-- | Apply monadic function to Maybe value
(?<<) :: Monad m => (a -> m b) -> Maybe a -> m (Maybe b)
f ?<< m = monadSwap $ fmap f m

-- | Convert an Either containing a monadic action in the Right case to a monadic Either
eitherSwap :: Monad m => Either a (m b) -> m (Either a b)
eitherSwap (Left l) = return (Left l)
eitherSwap (Right s) = fmap Right s

-- | Convert Either to Maybe, keeping only Right values
rightToMaybe :: Either a b -> Maybe b
rightToMaybe (Right r) = Just r
rightToMaybe _ = Nothing

-- | Convert Either to Maybe, keeping only Left values
leftToMaybe :: Either a b -> Maybe a
leftToMaybe (Left l) = Just l
leftToMaybe _ = Nothing

-- =============================================================================
-- LIST AND MATRIX UTILITIES
-- =============================================================================

allSame :: Eq a => [a] -> Bool
allSame [] = True
allSame (x : xs) = all (== x) xs

-- | Extract a row from a matrix (list of lists), returning the first element of each list
-- and the remaining matrix
extractRow :: [[a]] -> Maybe ([a], [[a]])
extractRow [] = Just ([],[])
extractRow ((x : xs) : xss) = fmap (Bifunctor.bimap (x :) (xs :)) (extractRow xss)
extractRow _ = Nothing

-- | Check if all lists in a list of lists are empty
fullExtraction :: [[a]] -> Bool
fullExtraction [] = True
fullExtraction ([] : xss) = fullExtraction xss
fullExtraction _ = False

-- | Transpose a matrix (list of lists), returning Nothing if the matrix is jagged
transpose :: [[a]] -> Maybe [[a]]
transpose [] = Nothing
transpose xss =
  case extractRow xss of
    Just (xs,xss') -> fmap (xs :) (transpose xss')
    Nothing -> if fullExtraction xss then Just [] else Nothing

-- =============================================================================
-- EITHER UTILITIES
-- =============================================================================

-- | Combine two Either values using a binary function, combining Left values with Semigroup
combineLeft :: Semigroup x => (a -> b -> c) -> Either x a -> Either x b -> Either x c
combineLeft _ (Left a) (Left b) = Left (a <> b)
combineLeft f (Right a) (Right b) = Right (f a b)
combineLeft _ (Left a) _ = Left a
combineLeft _ _ (Left a) = Left a

-- | Combine a list of Either values, collecting all successful values or combining failures
collectEither :: Semigroup x => [Either x a] -> Either x [a]
collectEither = foldr (combineLeft (:)) (Right [])

-- | Traverse a list and collect only the Right values as Maybe
successList :: [Either a b] -> Maybe [b]
successList = traverse rightToMaybe

-- | Partition a list using a function that returns Maybe Bool
-- Returns Left with the first element that returned Nothing, or Right with the partition
partitionMaybe :: (a -> Maybe Bool) -> [a] -> Either a ([a], [a])
partitionMaybe _ [] = Right ([],[])
partitionMaybe f (x : xs) =
  case f x of
    Just True -> fmap (Bifunctor.first (x :)) (partitionMaybe f xs)
    Just False -> fmap (Bifunctor.second (x :)) (partitionMaybe f xs)
    Nothing -> Left x

-- | Apply a Maybe function to an Either value
combineMaybe :: Maybe (a -> b) -> Either e a -> Either String (Either e b)
combineMaybe (Just f) (Right b) = Right (Right (f b))
combineMaybe Nothing (Right _) = Left "combineMaybe fail - function to apply was nothing"
combineMaybe _ (Left x) = Right (Left x)

-- defaults to right for the empty list
matchAll :: [Either a b] -> Maybe (Either [a] [b])
matchAll [Left l] = Just (Left [l])
matchAll [] = Just (Right [])
matchAll (e : es) =
  case e of
    Left l ->
      case matchAll es of
        Just (Left ls) -> Just (Left (l : ls))
        Just (Right _) -> Nothing
        Nothing -> Nothing
    Right r ->
      case matchAll es of
        Just (Right rs) -> Just (Right (r : rs))
        Just (Left _) -> Nothing
        Nothing -> Nothing

fromLeft :: [Char] -> Either a b -> a
fromLeft _ (Left l) = l
fromLeft s (Right _) = error ("expected Left value in fromLeft: " ++ s)

fromRight :: [Char] -> Either a b -> b
fromRight _ (Right r) = r
fromRight s (Left _) = error ("expected Right value in fromRight: " ++ s)

-- =============================================================================
-- GENERAL UTILITIES
-- =============================================================================

-- | Type alias for inverse map (bidirectional mapping)
type InvMap k a = (Map k a, Map a (Set k))

-- | Operator for executing state computation and returning final state
infixr 6 +>
(+>) :: State s a -> s -> s
(+>) = State.execState

-- | Apply function to Left value, leave Right unchanged
fmapl :: (a -> c) -> Either a b -> Either c b
fmapl f (Left l) = Left (f l)
fmapl _ (Right r) = Right r

-- | Insert element into Set stored in Map, creating singleton Set if key doesn't exist
insertSetMap :: Ord k => Ord a => k -> a -> Map k (Set a) -> Map k (Set a)
insertSetMap k a = Map.alter (return . insertMaybe a) k

insertSetSetMap :: Ord k => Ord a => k -> Set a -> Map k (Set a) -> Map k (Set a)
insertSetSetMap k a = Map.alter (\case Nothing -> Just a; Just b -> Just (Set.union a b)) k

chain :: [a -> a] -> a -> a
chain = foldr (.) id

-- =============================================================================
-- SEARCH AND CONTROL FLOW UTILITIES
-- =============================================================================

-- | Find first Just result from applying function to list elements
findJust :: Foldable t => (a -> Maybe b) -> t a -> Maybe b
findJust f = foldr (\ a b -> case f a of Nothing -> b; x -> x) Nothing

-- | Try stateful computations in parallel, return first success or fallback
forkFind :: [State s (Maybe r)] -> State s r -> State s r
forkFind [] r = r
forkFind (st : sts) r = State.state (\ s ->
    let (mr,s') = State.runState st s in
      case mr of
        Just r' -> (r',s')
        Nothing -> State.runState (forkFind sts r) s
  )

-- | Try stateful computations sequentially, return first success or fallback
seqFind :: [State s (Maybe r)] -> State s r -> State s r
seqFind [] r = r
seqFind (st : sts) r = State.state (\ s ->
    let (mr,s') = State.runState st s in
      case mr of
        Just r' -> (r',s')
        Nothing -> State.runState (seqFind sts r) s'
  )

-- | Try stateful computations sequentially, return first success or fallback (Maybe version)
seqFind' :: [State s (Maybe r)] -> State s (Maybe r) -> State s (Maybe r)
seqFind' [] r = r
seqFind' (st : sts) r = State.state (\ s ->
    let (mr,s') = State.runState st s in
      case mr of
        Just r' -> (Just r',s')
        Nothing -> State.runState (seqFind' sts r) s'
  )

anyM :: (Monad m, Foldable t) => (a -> m Bool) -> t a -> m Bool
anyM p = foldr (\ x acc -> do
    b <- p x
    if b then return True else acc) (return False)

-- =============================================================================
-- STATE UTILITIES
-- =============================================================================

-- | Apply state computation to each element in list of states
stateSequence :: State s r -> State [s] [r]
stateSequence f = do
  ss <- State.get
  case ss of
    [] -> return []
    (s : ss') -> do
      let (r,s') = State.runState f s
      let (rs,ss'') = State.runState (stateSequence f) ss'
      State.put (s' : ss'')
      return (r : rs)

-- | Try computation on each state until one succeeds
tryUntil :: State s (Maybe r) -> State [s] (Maybe r)
tryUntil f = do
  ss <- State.get
  case ss of
    [] -> return Nothing
    (s : ss') ->
      let (r,s') = State.runState f s in
        case r of
          Nothing ->
            let (r',ss'') = State.runState (tryUntil f) ss' in do
              State.put (s' : ss'')
              return r'
          x -> do
            State.put (s' : ss')
            return x

-- | Variant of tryUntil with accumulator state
tryUntil' :: State (s1,s2) (Maybe r) -> State (s1,[s2]) (Maybe r)
tryUntil' f = do
  (acc,ss) <- State.get
  case ss of
    [] -> return Nothing
    (s : ss') ->
      let (r,(acc',s')) = State.runState f (acc,s) in
        case r of
          Nothing ->
            let (r',(acc'',ss'')) = State.runState (tryUntil' f) (acc',ss') in do
              State.put (acc'',s' : ss'')
              return r'
          x -> do
            State.put (acc',s' : ss')
            return x

-- | Map state computation to different state type
smap :: (a -> b) -> (a -> b -> a) -> State b r -> State a r
smap f g s = do
  a <- State.get
  let b = f a
  let (r,b') = State.runState s b
  State.put (g a b')
  return r

-- | Map state computation to first component of tuple
smapFst :: State a r -> State (a, b) r
smapFst = smap fst (\ (_,b) a -> (a,b))

-- | Map state computation to second component of tuple  
smapSnd :: State b r -> State (a, b) r
smapSnd = smap snd (\ (a,_) b -> (a,b))

-- | Execute state computation conditionally, return default value otherwise
executeIf :: (s -> Bool) -> State s r -> r -> State s r
executeIf f s r = do
  s' <- State.get
  if f s' then s else return r

-- | Sequential composition of state computations, keeping second result
(>.>) :: State s a -> State s b -> State s b
s1 >.> s2 = do
  s <- State.get
  let s' = State.execState s1 s
      (r,s'') = State.runState s2 s'
  State.put s''
  return r



-- =============================================================================
-- CAST
-- =============================================================================

class Castable a b where
  cast :: a -> b
  uncast :: b -> a

-- Identity instance for when both types are the same
instance Castable String String where
  cast = id
  uncast = id