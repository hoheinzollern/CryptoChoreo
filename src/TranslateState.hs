{-# LANGUAGE TupleSections #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TranslateState where
import Frame
import Term
import Util
import EqClasses
import Choreo
import Algebraic
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Set (Set)
import Data.Map (Map)
import qualified Control.Monad.Trans.State as State
import Control.Monad.Trans.State (State)
import Data.List (sortOn)
import Data.Foldable
import qualified Data.Bifunctor as Bifunctor

data TranslateState l f v nameGenerator = TState {
    frames :: [(Frame l f v, ChoreoUnion f v)],
    checks :: EqClasses (Term f l),
    nocheck :: Set l, -- labels that are fully described by smaller terms in the frame, and therefore should not be used in checks
    ng :: nameGenerator,
    ag :: Agent f v,
    alg :: Algebra f,
    goalSet :: GoalSet f v, -- all goals in the entire choreography (also other branches)
    startSet :: Set String -- set of generated start events
}

runFrames fs = do
    ts <- State.get
    let (r,fr') = State.runState fs (frames ts)
    State.put (ts {frames = fr'})
    return r

runOnAllFrames fs = runFrames (stateSequence fs)

runChecks cs = do
    ts <- State.get
    let (r,cr') = State.runState cs (checks ts)
    State.put (ts {checks = cr'})
    return r

runNocheck cs = do
    ts <- State.get
    let (r,cr') = State.runState cs (nocheck ts)
    State.put (ts {nocheck = cr'})
    return r

runNameGenerator ngs = do
    ts <- State.get
    let (r,ng') = State.runState ngs (ng ts)
    State.put (ts {ng = ng'})
    return r


updateFrames fs = runFrames (State.put fs)
updateGoals gs = State.get >>= \ ts -> State.put (ts {goalSet = gs})
switchFrames ts fs' = ts {frames = fs'}

updateChecks cs = runChecks (State.put cs)


constructApply :: (VarLike l, Ord f,VarLike v) =>
    Algebra f -> EqClasses (Term f l) -> f -> [Term f v] -> State (ECMap (Term f v) l) (Set (Term f l))
constructApply alg checks f ts
    | public alg f (length ts) = do
        ts' <- traverse (construct alg checks) ts
        return (Set.map (Fun f) (expandSetList ts'))
constructApply _ _ _ _ = return Set.empty


construct :: (VarLike l, Ord f,VarLike v) =>
    Algebra f -> EqClasses (Term f l) -> Term f v -> State (ECMap (Term f v) l) (Set (Term f l))
construct alg checks t = do
    labels <- Set.map Var <$> lookupECMap t
    let fs = topSynonyms alg t -- functions that can produce t
    constructed <- (\ f -> constructApply alg checks f $<<<< topdec alg f t) $<<<< fs
    return $ setEqModulo checks $ Set.union labels constructed


directSubterms :: (VarLike v, VarLike l, Ord f) =>
    Algebra f -> EqClasses (Term f l) -> l -> Either f [f] -> Term f v -> State (Frame l f v) (Maybe (Maybe (Maybe (Term f l)),[Term f l]))
directSubterms alg checks l dests (Fun f ts) = do
    -- Which destructors apply to f?
    case dests of
        Right ds -> -- projection(s)
            return $ Just (Nothing,map (\ d -> Fun d [Var l]) ds)
        Left d -> tryDecryption d -- decryption 
    where 
        tryDecryption d =
            case reverse ts of -- Is the encryption guarded by a key?
            [] -> return Nothing -- No
            (k : rts) -> do -- Yes
                let ts' = reverse rts
                let k' = Map.lookup d (kr alg) >>= ($ k) -- decryption key
                k'r' <- (Frame.runInverse . construct alg checks) ?<< k' -- recipes for that key
                let k'rm = Set.lookupMin =<< k'r'
                kr' <- Frame.runInverse $ construct alg checks k -- can we reproduce the encryption key?
                let krm = Set.lookupMin kr'
                case k'rm of
                    Nothing -> return Nothing
                    Just k'r -> return $ Just (Just krm, [Fun d [Var l, k'r]])
directSubterms _ _ _ _ _ = return Nothing

analysisStep' :: (VarLike l,VarLike v, Ord f, NameGenerator ng l, Show f) => Algebra f -> EqClasses (Term f l) ->
    State (ng,Frame l f v) (Maybe (l,f,Maybe (Term f l),[(l,Term f l)]))
analysisStep' alg checks = do
    ml <- smapSnd Frame.getPending  -- get unanalysed label
    (_,frame) <- State.get
    let mt = (`Frame.lookup` frame) =<< ml -- get term for that label
    case fmap (,) ml <*> mt of
        Nothing -> return Nothing
        Just (l,t) -> do
            let fs = topSynonyms alg t -- functions that can produce t
            let fts = (\ f -> Set.map (f,) (topdec alg f t)) =<<< fs -- possible ways of representing t
            seqFind' 
                (map (analysisStep'' l) (Set.toList fts)) -- try to analyse each representation
                (smapSnd (Frame.insertHold l) >> analysisStep' alg checks) -- continue with another label if none worked
    where
        analysisStep'' l (f,ts) =
            case Map.lookup f (dl alg) of -- Do any destructors apply to f?
                Nothing -> return Nothing
                Just dests -> do
                    subterms <- smapSnd $ directSubterms alg checks l dests (Fun f ts)
                    case subterms of -- Can we apply the destructor?
                        Nothing -> return Nothing
                        Just (mk,rs) -> do 
                            let lrsS = foldr (\ r s -> fresh >>= (\l -> fmap ((l,r):) s)) (return []) rs
                            (ng,_) <- State.get
                            let (lrs,ng') = State.runState lrsS ng
                            let reconstructed =
                                    case mk of
                                        Just Nothing -> Nothing
                                        Nothing -> Just (Fun f (map (Var . fst) lrs))
                                        Just (Just kr) -> Just (Fun f (map (Var . fst) lrs ++ [kr]))
                            smapFst $ State.put ng'
                            return (Just (l,f,reconstructed,lrs))

runNGFrames fs = do
    ts <- State.get
    let (r,(ng',fr')) = State.runState fs (ng ts,map fst (frames ts))
    State.put (ts {ng = ng', frames = zip fr' (map snd (frames ts))})
    return r

isAnalysed :: (VarLike v, Ord f, Ord l) => Algebra f -> Frame l f v -> Term f l -> Bool
isAnalysed alg frame r =
    case reduces alg =<< applyFrame frame r of 
        Just _ -> True 
        Nothing -> False 

analysisStep :: (VarLike l,VarLike v, Ord f, NameGenerator ng l, Show f) =>
    State (TranslateState l f v ng) (Maybe [(l,Term f l)])
analysisStep = do
    tstate <- State.get
    manalysis <- runNGFrames (tryUntil' (analysisStep' (alg tstate) (checks tstate)))
    case manalysis of
        Nothing -> return Nothing
        Just (l,f,mr,lrs) -> do
            runNocheck (case mr of Nothing -> return (); Just _ -> State.modify (Set.insert l)) -- mark label as nocheck if we have a recipe to reconstruct it
                -- actually, we could probably just remove it from the frame in this case
            let queueDeletor = executeIf (\frame -> null lrs || isAnalysed (alg tstate) frame (snd $ head lrs)) (Frame.deleteFromQueue l) () 
                termAdder (l,r) = do
                    frame <- State.get
                    case Frame.applyFrame frame r of
                        Just t -> Frame.insert l (reduce (alg tstate) t)
                        Nothing -> error "Unable to apply a frame during analysis. This shouldn't happen"
            _ <- runOnAllFrames (smapFst (queueDeletor >.> traverse termAdder lrs))

            return (Just lrs)


findCheck :: (Ord f, VarLike l,VarLike v, Show f) =>
    Algebra f -> Set l -> EqClasses (Term f l) ->
    State (Frame l f v) (Maybe (l,Term f l))
findCheck alg nocheck checks = do 
    frame <- State.get 
    findCheck' (sortOn termSize (Map.elems (Frame.toMap frame))) -- look at each term in the frame, smallest first
    where
        findCheck' [] = return Nothing
        findCheck' (t : ts) = do 
            ls' <- runInverse $ lookupECMap t  -- all the labels refering to that term
            us <- runInverse $ construct alg checks t -- get all the recipes for that term
            case Set.toList (Set.difference ls' nocheck) of -- remove the labels marked as nocheck
                l : ls -> do -- pick a label refering to the term (which one doesn't matter)
                    -- find a recipe that is 1) not marked as nocheck 2) not implied equal to the label by the existing checks
                    let u = find (\ r -> (case r of Var l' -> (not (Set.member l' nocheck) &&); _ -> id) $ not $ isEq checks (Var l) r) us
                    case u of
                        Nothing -> findCheck' ts
                        Just u' -> return $ Just (l,u')
                _ -> findCheck' ts

findVerifier :: (Ord f, VarLike l,VarLike v, Show f) =>
    Algebra f -> EqClasses (Term f l) ->
    State (Frame l f v) (Maybe (Term f l))
findVerifier alg checks = do 
    frame <- State.get 
    let vs = map (runInverse . hasVerifier) (Map.toList $ Frame.toMap frame)
    seqFind' vs (return Nothing)
    where 
        hasVerifier (l,Fun f ts) 
            | Just v <- Map.lookup f (vl alg) = -- there is a verifier for f
                case v of
                Right v -> -- and no key is required
                    return $ ensure (not . isEq checks (tru alg)) (Fun v [Var l])
                Left d -> -- and key is required
                    -- Is the encryption guarded by a key?
                    case reverse ts of
                    [] -> return Nothing -- No
                    (k : _) -> do -- Yes
                        let k' = Map.lookup d (kr alg) >>= ($ k) -- decryption key
                        kr' <- construct alg checks ?<< k'
                        let kr = Set.lookupMin =<< kr' -- recipe for that key
                        case kr of 
                            Nothing -> return Nothing 
                            Just kr -> return $ ensure (not . isEq checks (tru alg)) (Fun d [Var l, kr]) -- return verifier information, unless the verification is implied equal to true
        hasVerifier _ = return Nothing


checkStep :: (Ord f, VarLike l,VarLike v, NameGenerator ng l, Show f) =>
    State (TranslateState l f v ng) (Maybe (Term f l,Term f l))
checkStep = do
    tstate <- State.get
    v <- runFrames (tryUntil $ smapFst $ findCheck (alg tstate) (nocheck tstate) (checks tstate))
    case v of
        Just (l,r) -> return (Just (Var l,r))
        Nothing -> return Nothing

verifierStep :: (Ord f, VarLike l,VarLike v, NameGenerator ng l, Show f) =>
    State (TranslateState l f v ng) (Maybe (Term f l,Term f l))
verifierStep = do
    tstate <- State.get
    v <- runFrames (tryUntil $ smapFst $ findVerifier (alg tstate) (checks tstate))
    case v of
        Just r -> return (Just (r,tru (alg tstate)))
        Nothing -> return Nothing

getGoalSet :: State (TranslateState l f v ng) (GoalSet f v)
getGoalSet = do
    tstate <- State.get
    let choreos = map snd (frames tstate)
    let eventNames = Set.unions $ map names choreos -- all names of end events we might reach
    let filterer (n,_,_,_) = not (Set.member n (startSet tstate)) && Set.member ("end" ++ n) eventNames
    let goals = Bifunctor.bimap (filter filterer) (filter filterer) $ goalSet tstate
    -- trace ("eventNames: " ++ show (eventNames)) $
    --     trace ("getGoalSet: " ++ show (map (\ (n,_,_,_) -> n) (uncurry (++) goals))) $
    return goals
    where 
        names (CUChoreo c) = getEventNames c
        names (CUAtomic _ a) = getEventNamesAtomic a
        names (CUWrites _ w) = getEventNamesWrites w

-- assumes fully checked and analysed 
-- forgets any learned derivations
synthesise :: (VarLike l, VarLike v, Ord f) => Algebra f -> EqClasses (Term f l) -> [(Frame l f v, Term f v)] -> Maybe (Term f l)
synthesise alg checks ((f,t) : fts) = do
    r <- Set.lookupMin $ State.evalState (construct alg checks t) (Frame.frameInverse f)
    let b = all (\ (f,t) -> applyFrame f r == Just t) fts in
        if b then Just r else Nothing
synthesise _ _ _ = Nothing
