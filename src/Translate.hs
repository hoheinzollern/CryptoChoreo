{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Translate where

import Choreo
import qualified Data.Bifunctor as Bifunctor
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Local
import Term
import Frame (Frame)
import qualified Frame
import Algebraic
import qualified Data.List as List
import Control.Monad.Trans.State (State)
import qualified Control.Monad.Trans.State as State
import Control.Monad ((<=<), replicateM, zipWithM, foldM)
import Util
import EqClasses
import TranslateState
import Data.Maybe (fromMaybe)
import Data.List (unzip4)

-- | Translation failure types with error context.
--
data Failure l f v
  = Unknown
  | Other String
  | IllDefinedChor [(Frame l f v, ChoreoUnion f v)]
  | MultiFailure [Failure l f v]
  | RecipeSynthesisFailed [(Frame l f v, Term f v)]
  deriving (Show)


-- | Extract list of failures from a multifailure, or wrap a failure in a list
multiLift :: Failure l f v -> [Failure l f v]
multiLift (MultiFailure fs) = fs
multiLift x = [x]

removeEmptyMF :: Failure l f v -> Failure l f v
removeEmptyMF (MultiFailure fs) =
  case filter (not . isEmptyFailure) (map removeEmptyMF fs) of
    [] -> MultiFailure []
    [x] -> x
    xs -> MultiFailure xs
  where isEmptyFailure (MultiFailure []) = True
        isEmptyFailure _ = False
removeEmptyMF x = x

-- | Semigroup instance for combining failures.
--
-- Multiple failures are automatically wrapped in 'MultiFailure' to preserve
-- all error information during translation.
instance Semigroup (Failure l f v) where
  (<>) :: Failure l f v -> Failure l f v -> Failure l f v
  x <> y = MultiFailure (multiLift x ++ multiLift y)

-- | Type alias for translation results.
--
-- All translation functions return this type, capturing either a failure
-- with context or a successful result.
newtype TranslateResult l f v res = TR (Either (Failure l f v) res)

instance Castable (TranslateResult l f v res) (Either (Failure l f v) res) where
  cast (TR r) = r
  uncast = TR

instance Applicative (TranslateResult l f v) where
  pure x = TR (Right x)
  TR f <*> TR x = TR $ case f of
    Left errF -> case x of
      Left errX -> Left (errF <> errX)
      Right _ -> Left errF
    Right func -> case x of
      Left errX -> Left errX
      Right val ->
        Right (func val)

instance Functor (TranslateResult l f v) where
  fmap f (TR r) = TR $ case r of
    Left err -> Left err
    Right val -> Right (f val)

instance Monad (TranslateResult l f v) where
  return = pure
  TR r >>= f = TR $ case r of
    Left err -> Left err
    Right val ->
      case f val of
        TR (Left errF) -> Left errF
        TR (Right valF) ->
          Right valF


combineLeftTR :: (a -> b -> c) -> TranslateResult l f v a -> TranslateResult l f v b -> TranslateResult l f v c
combineLeftTR f t1 t2 =
  fmap (uncurry f) (t1 >>= \m1 -> t2 >>= \m2 -> return (m1, m2))


translate :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  Map l (Term f v) -> Choreo f v ->
  nameGenerator -> Agent f v -> Algebra f -> GoalSet f v ->
    TranslateResult l f v (TranslateState l f v nameGenerator, Local f l)
translate initialKnowledge program ng ag alg goalSet =
  let tstate =  TState [(Frame.fromMap alg initialKnowledge,CUChoreo program)] emptyEC Set.empty ng ag alg goalSet Set.empty in
  let (l,s) = State.runState (fmap (TR . fmapl removeEmptyMF . cast) analysis) tstate in
  fmap ((s,) . toLocal) l

  -- start translation by analysis and remove empty atomic sections after analysis



noFrames :: State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
noFrames = do
  st <- State.get
  if null (frames st) then return (Just (TR $ Left $ IllDefinedChor [])) else return Nothing

returnIllDefined :: State (TranslateState l f v nameGenerator) (TranslateResult l f v (LocalUnion f l))
returnIllDefined = TR . Left . IllDefinedChor . frames <$> State.get

translate' ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (TranslateResult l f v (LocalUnion f l))
translate' =
  forkFind [
    noFrames, returnDone,
    matchOne otherSend, matchOne otherAtomic,
    allMySends, allMyReceive, allMyAtomic,
    allMyNonce, allMyChoice, allMyEvent, allMyRead, allMyBranch, allMyWrites,
    allMyWrite, allMyChoreo
    ] returnIllDefined

matchOne' ::
  (ChoreoUnion f v -> Maybe [ChoreoUnion f v]) ->
  [(Frame l f v, ChoreoUnion f v)] ->
  Maybe [(Frame l f v, ChoreoUnion f v)]
matchOne' _ [] = Nothing
matchOne' matcher ((f, c) : fcs) =
  case matcher c of
    Just cs -> Just (map (f,) cs ++ fcs)
    Nothing -> fmap ((f, c) :) (matchOne' matcher fcs)

matchOne ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  (Agent f v -> ChoreoUnion f v -> Maybe [ChoreoUnion f v]) ->
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
matchOne matcher = do
  st <- State.get
  case matchOne' (matcher (ag st)) (frames st) of
    Just fcs -> do
      updateFrames fcs
      fmap Just translate'
    Nothing -> return Nothing

-- | Check if all choreographies in the list are 'End'.
isDone :: [(Frame l f v, ChoreoUnion f v)] -> Bool
isDone [] = True
isDone ((_, CUChoreo End) : fcs) = isDone fcs
isDone ((_, CUAtomic _ (Writes (Choreo End))) : fcs) =  isDone fcs
isDone ((_, CUWrites _ (Choreo End)) : fcs) =  isDone fcs
isDone _ = False

returnDone :: State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
returnDone = do
  st <- State.get
  return $ if isDone (frames st) then Just (TR $ Right (LULocal LEnd)) else Nothing

otherSend ::
  (Eq f, Eq v) =>
  Agent f v ->
  ChoreoUnion f v ->
  Maybe [ChoreoUnion f v]
otherSend a (CUChoreo (Send a1 a2 _ c))
  | a1 /= a && a2 /= a = Just [CUChoreo c]
otherSend _ _ = Nothing

otherLockSplit :: Atomic f v -> [Choreo f v]
otherLockSplit (Read _ _ _ a) = otherLockSplit a
otherLockSplit (Branch _ _ a1 a2) = otherLockSplit a1 ++ otherLockSplit a2
otherLockSplit (Event _ _ a) = otherLockSplit a
otherLockSplit (Nonce _ _ a) = otherLockSplit a
otherLockSplit (Choice as) = concatMap otherLockSplit as
otherLockSplit (Writes w) = otherLockWritesSplit w

otherLockWritesSplit :: Writes f v -> [Choreo f v]
otherLockWritesSplit (Write _ _ _ w) = otherLockWritesSplit w
otherLockWritesSplit (Choreo c) = [c]

otherAtomic ::
  (Eq f, Eq v) =>
  Agent f v ->
  ChoreoUnion f v ->
  Maybe [ChoreoUnion f v]
otherAtomic a (CUChoreo (Atomic a' at))
  | a' /= a = Just (map CUChoreo (otherLockSplit at))
otherAtomic _ _ = Nothing



-- =============================nonce-generation recipes====================================


forceRecipe ::
  (VarLike l, Ord f, VarLike v, Show f, NameGenerator nameGenerator l) =>
  Term f v -> State (TranslateState l f v nameGenerator) (Maybe (Term f l))
forceRecipe t = do
  tstate <- State.get
  let fs = map fst (frames tstate)
  let inverter frame = Map.foldrWithKey (\ l -> \case Var x -> insertSetMap x l ; _ -> id) Map.empty (Frame.toMap frame)
  let synthesizer = mapv . flip (Map.findWithDefault (error "key not found in force recipe")) . inverter
  let rs = map (`synthesizer` t) fs
  return (unsetify <$> foldM tryUnify (head rs) (tail rs))

tryUnify :: (Ord v, Eq f) => Term f (Set v) -> Term f (Set v) -> Maybe (Term f (Set v))
tryUnify (Var s1) (Var s2) = Just $ Var (Set.intersection s1 s2)
tryUnify (Fun f1 ts1) (Fun f2 ts2)
  | f1 == f2 && length ts1 == length ts2 = Fun f1 <$> zipWithM tryUnify ts1 ts2
  | otherwise = Nothing
tryUnify _ _ = Nothing

unsetify :: Term f (Set v) -> Term f v
unsetify (Var s) =
  case Set.toList s of
    x : _ -> Var x
    _ -> error "unsetify: empty set"
unsetify (Fun f ts) = Fun f (map unsetify ts)

-- =========================================================================================

synthesizeRecipe ::
  (VarLike l, Ord f, VarLike v) =>
  Algebra f -> EqClasses (Term f l) -> [Frame l f v] -> [Term f v] -> TranslateResult l f v (Term f l)
synthesizeRecipe alg checks fs ts =
  case synthesise alg checks $ zip fs ts of
    Just t -> TR $ Right t
    Nothing -> TR $ Left (RecipeSynthesisFailed (zip fs ts))


synthesizeRecipes ::
  (VarLike l, Ord f, VarLike v) =>
  Algebra f -> EqClasses (Term f l) -> [Frame l f v] -> [[Term f v]] -> TranslateResult l f v [Term f l]
synthesizeRecipes alg checks fs =
  mapM (synthesizeRecipe alg checks fs)


orderTermsAndMakeRecipes ::
  (VarLike l, Ord f, VarLike v) =>
  Algebra f -> EqClasses (Term f l) -> [Frame l f v] -> [[Term f v]] ->
    TranslateResult l f v [Term f l]
orderTermsAndMakeRecipes alg checks fs =
  synthesizeRecipes alg checks fs <=< ((\case Just t -> TR $ Right t; Nothing -> TR $ Left (Other  "failed to transpose a matrix")) . transpose)


-- | Extract term-choreography pairs from send operations by the target agent.
mySend :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (Term f v, Choreo f v)
mySend a (CUChoreo (Send a1 _ t c))
  | a == a1 = Just (t,c)
mySend _ _ = Nothing

allMySends :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMySends = do
  tstate <- State.get
  let (fs, choreographies) = unzip (frames tstate)
      maybeSendData = mapM (mySend (ag tstate)) choreographies
  case maybeSendData of
    Nothing -> return Nothing  -- Not all choreographies are sends by this agent
    Just sendDataList -> do
      tstate <- State.get
      let ts = map fst sendDataList
      let cs = map snd sendDataList
      let r = synthesizeRecipe (alg tstate) (checks tstate) fs ts
      updateFrames (zip fs (map CUChoreo cs))
      tr <- translate'
      return $ Just $  (\recipe -> fmap (\lu -> LULocal (LSend recipe $ toLocal lu)) tr) =<< r


splitOn ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  Term f l -> Term f l ->
    State (TranslateState l f v nameGenerator) (TranslateResult l f v (LocalUnion f l))
splitOn r1 r2 = do
  tstate <- State.get
  -- trace (show r1 ++ "," ++ show r2 ++ show (checks tstate)) $
  --   trace (show (derivableEq (alg tstate) (checks tstate) r1 r2)) $
  case partitionMaybe (\ (f,_) -> Frame.frameEq (alg tstate) f r1 r2) (frames tstate) of
    Right (fcs1,fcs2) -> do
      let tr1 = State.evalState analysis (tstate {frames = fcs1,checks = State.execState (setEq r1 r2) (checks tstate)})
      let tr2 = State.evalState analysis (tstate {frames = fcs2})
      return $ combineLeftTR (\ lu1 lu2 -> LUAtomic $ LBranch r1 r2 (toLAtomic lu1) (toLAtomic lu2)) tr1 tr2
    Left (f,_) ->
      return (TR $ Left (Other (
        "Unable to apply Frame (" ++ show (Frame.toMap f) ++ ") to one of (" ++ show r1 ++ ") or (" ++ show r2 ++ ")")))

-- trace (show $ State.execState (setEq r1 r2) (checks tstate)) $ 
analysis :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
    State (TranslateState l f v nameGenerator) (TranslateResult l f v (LocalUnion f l))
analysis = do
  tstate <- State.get
  if null (frames tstate)
  then return (TR $ Right (LULocal LEnd))
  else do
    check <- verifierStep -- first, can we apply a verifier?
    case check of
      Nothing -> do
        massignments <- analysisStep -- second, can we analyse a term?
        case massignments of
          Just lrs ->
            let f = foldr (\ (l,r) f' -> LLet l r . f') id lrs
            in fmap (LUAtomic . f . toLAtomic) <$> analysis
          Nothing -> do
            check <- checkStep -- third, can we split on a check?
            case check of
              Just (r1,r2) -> splitOn r1 r2
              Nothing -> makeStartEvents
      Just (r1,r2) -> splitOn r1 r2


makeStartEvents :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
    State (TranslateState l f v nameGenerator) (TranslateResult l f v (LocalUnion f l))
makeStartEvents = do
  goals <- getGoalSet
  let flattened = uncurry (++) goals
  if null flattened
  then translate'
  else do
    tstate <- State.get
    fmap LUAtomic <$> findStartEvent (ag tstate) flattened
    where
    findStartEvent ::
      (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
      Agent f v ->
      [(String, Agent f v, Agent f v, Term f v)] ->
        State (TranslateState l f v nameGenerator) (TranslateResult l f v (LAtomic f l))
    findStartEvent _ [] = fmap (fmap toLAtomic) translate'
    findStartEvent a ((eventName,a1,a2,t) : es)
      | a1 == a = do
        tstate <- State.get
        let fs = map fst $ frames tstate
        let rs = do
              ra1 <- synthesise (alg tstate) (checks tstate) $ zip fs (replicate (length fs) (cast a1))
              ra2 <- synthesise (alg tstate) (checks tstate) $ zip fs (replicate (length fs) (cast a2))
              rt <- synthesise (alg tstate) (checks tstate) $ zip fs (replicate (length fs) t)
              return (ra1,ra2,rt)
        case rs of
          Nothing -> findStartEvent a es
          Just (ra1,ra2,rt) -> do
            State.put (tstate {startSet = Set.insert eventName (startSet tstate)})
            fmap (LEvent ("begin" ++ eventName) [ra1,ra2,rt]) <$> findStartEvent a es
    findStartEvent a (_ : es) = findStartEvent a es

myReceive :: (Ord l, Ord f, Ord v) =>
  Agent f v -> l -> Frame l f v -> ChoreoUnion f v ->
    Maybe (Frame l f v, Choreo f v)
myReceive a freshLabel frame (CUChoreo (Send _ a2 t c))
  | a == a2 = Just (Frame.insert freshLabel t +> frame,c)
myReceive _ _ _ _ = Nothing

allMyReceive :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
    State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyReceive = do
  freshLabel <- runNameGenerator fresh
  tstate <- State.get
  let maybeReceiveData = traverse (uncurry (myReceive (ag tstate) freshLabel)) (frames tstate)
  case maybeReceiveData of
    Nothing -> return Nothing
    Just fcs -> do
      updateFrames (map (Bifunctor.second CUChoreo) fcs)
      Just . fmap (LULocal . LReceive freshLabel . toLocal) <$> analysis


myAtomic :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (Atomic f v)
myAtomic a (CUChoreo (Atomic a' at))
  | a == a' = Just at
myAtomic _ _ = Nothing

allMyAtomic :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
    State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyAtomic = do
  tstate <- State.get
  let maybeAtomicData = traverse (myAtomic (ag tstate) . snd) (frames tstate)
  case maybeAtomicData of
    Nothing -> return Nothing
    Just atms -> do
      updateFrames (zip (map fst (frames tstate)) (map (CUAtomic (ag tstate)) atms))
      Just <$> analysis


myBranch :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (Term f v, Term f v, Atomic f v, Atomic f v)
myBranch a (CUAtomic a' (Branch b1 b2 a1 a2))
  | a == a' = Just (b1, b2, a1, a2)
myBranch _ _ = Nothing

myRead :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe ((String,Term f v, Term f v), Atomic f v)
myRead a (CUAtomic a' (Read s t1 t2 at))
  | a == a' = Just ((s,t1,t2),at)
myRead _ _ = Nothing

myNonce ::
  (Eq f, Eq v) =>
  Agent f v ->
  ChoreoUnion f v ->
  Maybe (v, [Term f v], Atomic f v)
myNonce a (CUAtomic a' (Nonce v ts c))
  | a == a' = Just (v, ts, c)
myNonce _ _ = Nothing

myEvent :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (String, [Term f v], Atomic f v)
myEvent a (CUAtomic a' (Event name ts c))
  | a == a' = Just (name, ts, c)
myEvent _ _ = Nothing

myChoice ::
  (Eq f, Eq v) =>
  Agent f v ->
  ChoreoUnion f v ->
  Maybe [Atomic f v]
myChoice a (CUAtomic a' (Choice choices))
  | a == a' = Just choices
myChoice _ _ = Nothing

myWrites ::
  (Eq f, Eq v) =>
  Agent f v ->
  ChoreoUnion f v ->
  Maybe (Writes f v)
myWrites a (CUAtomic a' (Writes w))
  | a == a' = Just w
myWrites _ _ = Nothing

allNoncesMatch ::
  (Eq f, Eq v) =>
  [Maybe (v,[Term f v], Atomic f v)] ->
  Maybe (v, [Term f v], [Atomic f v])
allNoncesMatch [Just (x, ts, c)] = Just (x, ts, [c])
allNoncesMatch (Just (x, ts1, c1) : Just (y, ts2, c2) : xs)
  | x == y && ts1 == ts2 = fmap (Bifunctor.second (c1 :)) (allNoncesMatch (Just (y, ts2, c2) : xs))
allNoncesMatch _ = Nothing

allMyNonce ::
  (VarLike l, Ord f, VarLike v, Show f, NameGenerator nameGenerator l) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyNonce = do
  tstate <- State.get
  let nonces = map (myNonce (ag tstate) . snd) (frames tstate)
  case allNoncesMatch nonces of
    Nothing -> return Nothing
    Just (variable, terms, continuations) -> do
      freshLabel <- runNameGenerator fresh
      _ <- runOnAllFrames (smapFst $ Frame.insert freshLabel (Var variable))
      recipesM <- mapM forceRecipe terms
      let recipes = fromMaybe (error "forceRecipe failed") $ sequence recipesM
      let n = length terms
      freshLabels <- replicateM n (runNameGenerator fresh)
      let insertions = zipWith Frame.insert freshLabels terms
      mapM_ (runOnAllFrames . smapFst) insertions
      tstate' <- State.get
      updateFrames (zip (map fst (frames tstate')) (map (CUAtomic (ag tstate')) continuations))
      let assignments = chain $ zipWith LLet freshLabels recipes
      Just . fmap (LUAtomic . LNonce freshLabel . assignments . toLAtomic) <$> makeStartEvents


allMyChoice :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyChoice = do
  tstate <- State.get
  let (fs, choreographies) = unzip (frames tstate)
      maybeChoices = mapM (myChoice (ag tstate)) choreographies
  case maybeChoices of
    Nothing -> return Nothing  -- Not all choreographies are choices by this agent
    Just choicesList -> do
      case transpose choicesList of
        Nothing -> return (Just (TR $ Left (IllDefinedChor (frames tstate)) ))  -- Inconsistent continuation structure
        Just transposedContinuations -> do
          let frameContinuationPairs = map (zip fs . map (CUAtomic (ag tstate))) transposedContinuations
              monadList = map (\ fcs -> do updateFrames fcs; translate') frameContinuationPairs
          tstate <- State.get
          let translateResult = map (`State.evalState` tstate) monadList
          return $ Just (fmap (LUAtomic . LChoice . map toLAtomic) (sequence translateResult))

allMyEvent :: (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
    State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyEvent = do
  tstate <- State.get
  case traverse (myEvent (ag tstate) . snd) (frames tstate) of
    Just ntscs -> do
      let fs = map fst $ frames tstate
      let (names, ts, cs) = unzip3 ntscs
      -- All event names should be the same, take the first one
      if all (== head names) names
      then do
        let eventName = head names
        updateFrames (zip fs (map (CUAtomic (ag tstate)) cs))
        tr' <- translate'
        let tr = do
              rs <- orderTermsAndMakeRecipes (alg tstate) (checks tstate) fs ts
              LEvent eventName rs . toLAtomic <$> tr'
        return $ Just $ fmap LUAtomic tr
      else return (Just (TR $ Left (IllDefinedChor (frames tstate))))
    _ -> return Nothing

allMyBranch ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyBranch = do
  tstate <- State.get
  case traverse (myBranch (ag tstate) . snd) (frames tstate) of
    Nothing -> return Nothing  -- Not all are branches
    Just branchData -> do
      let (condition1Terms, condition2Terms, trueBranches, falseBranches) = List.unzip4 branchData
          fs = map fst (frames tstate)
          condition1Result = synthesizeRecipe (alg tstate) (checks tstate) fs condition1Terms
          condition2Result = synthesizeRecipe (alg tstate) (checks tstate) fs condition2Terms
      case combineLeftTR (,) condition1Result condition2Result of
        TR (Right (condition1Recipe, condition2Recipe)) -> do
          let trueFcs = zip fs $ map (CUAtomic (ag tstate)) trueBranches
              falseFcs = zip fs $ map (CUAtomic (ag tstate)) falseBranches
          let trueResult = toLAtomic <$> State.evalState translate' (tstate {frames = trueFcs})
          let falseResult = toLAtomic <$> State.evalState translate' (tstate {frames = falseFcs})

          case combineLeftTR (,) trueResult falseResult of
            TR (Right (trueContinuation, falseContinuation)) ->
              return $ Just (TR $ Right (LUAtomic $ LBranch condition1Recipe condition2Recipe trueContinuation falseContinuation))
            TR (Left err) -> return $ Just (TR $ Left err)
        TR (Left err) -> return $ Just (TR $ Left err)

allMyRead ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyRead  = do
  freshLabel <- runNameGenerator fresh
  tstate <- State.get
  case traverse (myRead (ag tstate) . snd) (frames tstate) of
    Nothing -> return Nothing  -- Not all are reads
    Just readData -> do
      let (variableTermPairs, continuations) = unzip readData
          (names,variables, terms) = unzip3 variableTermPairs
          fs = map fst (frames tstate)
          termResult = synthesizeRecipe (alg tstate) (checks tstate) fs terms
      if not (allSame names)
      then return (Just (TR $ Left (IllDefinedChor (frames tstate))))
      else
        case termResult of
          TR (Right recipe) -> do
            let updatedFrames = zipWith (\frame term -> Frame.insert freshLabel term +> frame) fs variables
                fcs = zip updatedFrames (map (CUAtomic (ag tstate)) continuations)
            updateFrames fcs
            Just . fmap (LUAtomic . LRead (head names) freshLabel recipe . toLAtomic) <$> analysis
          TR (Left err) -> return $ Just (TR $ Left err)

allMyWrites ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyWrites = do
  tstate <- State.get
  case traverse (myWrites (ag tstate) . snd) (frames tstate) of
    Nothing -> return Nothing
    Just choreos -> do
      let fcs = zip (map fst (frames tstate)) (map (CUWrites (ag tstate)) choreos)
      updateFrames fcs
      fmap Just translate'

myWrite :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (String, Term f v, Term f v, Writes f v)
myWrite a (CUWrites a' (Write s t1 t2 w))
  | a == a' = Just (s,t1,t2,w)
myWrite _ _ = Nothing

myChoreo :: (Eq f, Eq v) => Agent f v -> ChoreoUnion f v -> Maybe (Choreo f v)
myChoreo a (CUWrites a' (Choreo c))
  | a == a' = Just c
myChoreo _ _ = Nothing

allMyWrite ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyWrite = do
  tstate <- State.get
  case traverse (myWrite (ag tstate) . snd) (frames tstate) of
    Nothing -> return Nothing  -- Not all are writes
    Just writeData -> do
      let (names, addressTerms, valueTerms, continuations) = unzip4 writeData
          fs = map fst (frames tstate)
          addressResult = synthesizeRecipe (alg tstate) (checks tstate) fs addressTerms
          valueResult = synthesizeRecipe (alg tstate) (checks tstate) fs valueTerms
      if not (allSame names)
      then return (Just (TR $ Left (IllDefinedChor (frames tstate))))
      else
        case combineLeftTR (,) addressResult valueResult of
          TR (Right (addressRecipe, valueRecipe)) -> do
            updateFrames (zip fs (map (CUWrites (ag tstate)) continuations))
            Just . fmap (LUWrites . LWrite (head names) addressRecipe valueRecipe . toLWrites) <$> translate'
          TR (Left err) -> return $ Just (TR $ Left err)

allMyChoreo ::
  (VarLike l, Ord f, VarLike v, NameGenerator nameGenerator l, Show f) =>
  State (TranslateState l f v nameGenerator) (Maybe (TranslateResult l f v (LocalUnion f l)))
allMyChoreo = do
  tstate <- State.get
  case traverse (myChoreo (ag tstate) . snd) (frames tstate) of
    Nothing -> return Nothing  -- Not all are choreographies
    Just choreos -> do
      let fcs = zip (map fst (frames tstate)) (map CUChoreo choreos)
      updateFrames fcs
      fmap Just translate'