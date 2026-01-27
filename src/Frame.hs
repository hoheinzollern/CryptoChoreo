{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
module Frame where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Map (Map)
import qualified Data.Map as Map
import Term
import Util
import EqClasses
import qualified Control.Monad.Trans.State as State
import Algebraic


data Frame l f v = Frame {
    pending :: Set l,
    hold :: Set l,
    frameForward :: Map l (Term f v),  -- Map from labels to terms
    frameInverse :: ECMap (Term f v) l  -- Efficient (ish) lookup of labels, taking algebraic equality into account
}

updatePending :: Frame l f v -> Set l -> Frame l f v
updatePending frame p = Frame p (hold frame) (frameForward frame) (frameInverse frame)
updateHold :: Frame l f v -> Set l -> Frame l f v
updateHold frame h = Frame (pending frame) h (frameForward frame) (frameInverse frame)
updateForward :: Frame l f v -> Map l (Term f v) -> Frame l f v
updateForward frame f = Frame (pending frame) (hold frame) f (frameInverse frame)
updateInverse :: Frame l f v -> ECMap (Term f v) l -> Frame l f v
updateInverse frame = Frame (pending frame) (hold frame) (frameForward frame)

runPending :: State.State (Set l) r -> State.State (Frame l f v) r
runPending = smap pending updatePending
runHold :: State.State (Set l) r -> State.State (Frame l f v) r
runHold = smap hold updateHold
runForward :: State.State (Map l (Term f v)) r -> State.State (Frame l f v) r
runForward = smap frameForward updateForward
runInverse :: State.State (ECMap (Term f v) l) r -> State.State (Frame l f v) r
runInverse = smap frameInverse updateInverse

empty :: (VarLike v, Ord f) => Algebra f -> Frame l f v
empty alg = Frame Set.empty Set.empty Map.empty (emptyECMap (aeq alg))

insert :: (Ord l, Ord v, Ord f) => l -> Term f v -> State.State (Frame l f v) ()
insert l t = do
    frame <- State.get
    runPending (State.put $ Set.unions [Set.singleton l, pending frame, hold frame])
    runHold (State.put Set.empty)
    runForward (State.modify (Map.insert l t))
    runInverse (insertECMap t l)
    return ()


lookup :: Ord k => k -> Frame k f v -> Maybe (Term f v)
lookup l frame = Map.lookup l (frameForward frame)

toMap :: Frame l f v -> Map l (Term f v)
toMap = frameForward


instance (Show l, Show f, Show v) => Show (Frame l f v) where
    show f = show $ toMap f

fromMap :: (VarLike v, Ord f, Ord l) => Algebra f -> Map l (Term f v) -> Frame l f v
fromMap alg = (`State.execState` empty alg) . traverse (uncurry insert) . Map.toList

lookupTerm :: (Ord v, Ord f) => Term f v -> State.State (Frame l f v) (Set l)
lookupTerm t = runInverse $ lookupECMap t

getPending :: State.State (Frame l f v) (Maybe l)
getPending = do
    Frame p h f i <- State.get
    if null p
    then return Nothing
    else do
        let (l,p') = Set.deleteFindMin p
        State.put (Frame p' h f i)
        return $ Just l

insertHold :: (Monad m, Ord l) => l -> State.StateT (Frame l f v) m ()
insertHold l = do
    Frame p h f i <- State.get
    State.put (Frame p (Set.insert l h) f i)
    return ()

deleteFromQueue :: (Monad m, Ord l) => l -> State.StateT (Frame l f v) m ()
deleteFromQueue l = do
    Frame p h f i <- State.get
    State.put (Frame (Set.delete l p) (Set.delete l h) f i)
    return ()


-- | Apply a frame to a term (substitute labels with their values)
applyFrame :: (Ord l) => Frame l f v -> Term f l -> Maybe (Term f v)
applyFrame = applyMap . toMap


applyMap :: (Ord l) => Map l (Term f v) -> Term f l -> Maybe (Term f v)
applyMap m (Var l) = Map.lookup l m
applyMap m (Fun f ts) = Fun f <$> traverse (applyMap m) ts

frameEq :: (VarLike v, Ord l, Ord f) => Algebra f -> Frame l f v -> Term f l -> Term f l -> Maybe Bool
frameEq alg frame t1 t2 =
    let mt1 = Frame.applyFrame frame t1
        mt2 =  Frame.applyFrame frame t2
        r = fmap (aeq alg) mt1 <*> mt2
    in r --trace (show mt1 ++ " = " ++ show mt2 ++ "? " ++ show r) r

