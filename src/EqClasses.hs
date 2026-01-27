module EqClasses where

import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Foldable (find)
import Util

-- =============================================================================
-- EQUIVALENCE CLASSES
-- =============================================================================

-- | Data structure for maintaining equivalence classes
data EqClasses a = EC {
  maxColour :: Int,           -- ^ Next available color/ID
  cMap :: Map a Int,          -- ^ Map from elements to their equivalence class ID
  cInvMap :: Map Int (Set a)  -- ^ Map from equivalence class ID to its elements
}

instance Show a => Show (EqClasses a) where 
  show ec = show (cInvMap ec)

-- | Empty equivalence class structure
emptyEC :: EqClasses a
emptyEC = EC 0 Map.empty Map.empty

-- | Get next available color/ID and increment counter
sucC :: State (EqClasses a) Int
sucC = do
  EC mc cmap cinvmap <- State.get
  State.put (EC (mc + 1) cmap cinvmap)
  return mc

-- | Insert element with specific equivalence class ID
insertECIndexed :: Ord a => a -> Int -> State (EqClasses a) ()
insertECIndexed a i = do
  EC mc cmap cinvmap <- State.get
  State.put (EC mc (Map.insert a i cmap) (insertSetMap i a cinvmap))
  return ()

-- | Insert element with fresh equivalence class ID
insertECFresh :: Ord a => a -> State (EqClasses a) Int
insertECFresh a = do
  i <- sucC
  insertECIndexed a i
  return i

-- | Find or create equivalence class ID for element
findColourEC :: Ord a => a -> State (EqClasses a) Int
findColourEC a = do
  ec <- State.get
  case Map.lookup a (cMap ec) of
    Nothing -> insertECFresh a
    Just i -> return i

-- | Set two elements as equal, returns the equivalence class ID
-- If b was already equal to something, that will be forgotten
setEq :: Ord a => a -> a -> State (EqClasses a) Int
setEq a b = do
  ec <- State.get
  case (Map.lookup a (cMap ec), Map.lookup b (cMap ec)) of
    (Just i,_) -> do
      insertECIndexed b i
      return i
    (Nothing,Just i) -> do
      insertECIndexed a i
      return i
    (Nothing,Nothing) -> do
      i <- sucC
      insertECIndexed a i
      insertECIndexed b i
      return i

-- | Check if two elements are in the same equivalence class
isEq :: Ord a => EqClasses a -> a -> a -> Bool
isEq _ a b 
  | a == b = True
isEq ec a b =
  case (Map.lookup a (cMap ec), Map.lookup b (cMap ec)) of
    (Just i,Just j) -> i == j
    _ -> False

-- | Find all elements equivalent to the given element
findEqs :: Ord a => EqClasses a -> a -> Set a
findEqs ec a =
  case Map.lookup a (cMap ec) of
    Just i ->
      case Map.lookup i (cInvMap ec) of
        Just s -> s
        Nothing -> error "inconsistent eq class - this shouldn't happen"
    Nothing -> Set.singleton a

-- | Remove duplicates from set according to equivalence classes
setEqModulo :: Ord a => EqClasses a -> Set a -> Set a
setEqModulo ec = snd . Set.foldr (\ a (seen,s) ->
    case Map.lookup a (cMap ec) of
      Just i -> if Set.member i seen then (seen,s) else (Set.insert i seen,Set.insert a s)
      Nothing -> (seen,Set.insert a s)
  ) (Set.empty,Set.empty)

-- | Get all elements in equivalence classes
toList :: EqClasses a -> [a]
toList = Map.keys . cMap

-- | Get one representative from each equivalence class
toListModulo :: EqClasses a -> [a]
toListModulo = map Set.findMin . Map.elems . cInvMap

-- | Insert element using equivalence relation
-- Assumes that all equivalences between existing elements are already covered
insertECRel :: Ord a => (a -> a -> Bool) -> a -> State (EqClasses a) Int
insertECRel r a = do
  ec <- State.get
  case find (r a) (toListModulo ec) of
    Just b -> setEq a b
    Nothing -> insertECFresh a

-- =============================================================================
-- EQUIVALENCE CLASS MAPS
-- =============================================================================

-- | Map structure with equivalence classes as keys
data ECMap k v = ECM {
  ecECM :: EqClasses k,       -- ^ Equivalence classes for keys
  mapECM :: Map Int (Set v),  -- ^ Map from equivalence class ID to values
  relECM :: k -> k -> Bool    -- ^ Equivalence relation for keys
}

-- | Update equivalence classes in ECMap
ecUpdate :: ECMap k v -> EqClasses k -> ECMap k v
ecUpdate ecm ec = ECM ec (mapECM ecm) (relECM ecm)

-- | Update map in ECMap
mapUpdate :: ECMap k v -> Map Int (Set v) -> ECMap k v
mapUpdate ecm m = ECM (ecECM ecm) m (relECM ecm)

-- | Create empty ECMap with given equivalence relation
emptyECMap :: (k -> k -> Bool) -> ECMap k v
emptyECMap = ECM emptyEC Map.empty

-- | Insert key-value pair into ECMap
insertECMap :: (Ord k, Ord v) => k -> v -> State (ECMap k v) ()
insertECMap k v = do
  ecm <- State.get
  i <- smap ecECM ecUpdate (insertECRel (relECM ecm) k)
  smap mapECM mapUpdate (State.modify $ insertSetMap i v)

-- | Lookup values for key in ECMap
lookupECMap :: Ord k => k -> State (ECMap k v) (Set v)
lookupECMap k = do
  ecm <- State.get
  i <- smap ecECM ecUpdate (insertECRel (relECM ecm) k)
  setFromMaybe . Map.lookup i . mapECM <$> State.get
