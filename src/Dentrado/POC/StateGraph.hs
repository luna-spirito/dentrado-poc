module Dentrado.POC.StateGraph where

import Control.Algebra
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.State.Church (StateC, evalState, execState, runState)
import qualified Control.Effect.Empty as E
import Control.Effect.Reader (ask)
import Control.Effect.State (State (..), get, modify, put)
import Data.Constraint (Dict (..))
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Gear
import Dentrado.POC.Memory (AppForce (..), AppIO, AppIOC, Container, InferContainerT, InferValT (..), Res, Ser, alloc, fetch, sendAI, ReduceC)
import Dentrado.POC.Types (EventId (..), SiteAccessLevel, StateGraphEntry (..), fromEmpty)
import RIO hiding (ask, runReader)
import qualified RIO.Map as Map
import qualified RIO.Partial as P
import qualified RIO.Set as Set
import Data.Bitraversable (bimapM)
import RIO.List (sortBy)

{-
StateGraph (temporary? name) is a O(n^2) sledgehammer, powerful enough to emulate any* stateful tranformations within Dentrado.
The core idea behind the StateGraph is presented in /stategraph.png in the root of the repository.

StateGraph conserves the state history for a group of objects, and how state of each one affected the state of another.
State updates are performed by incoming events, which are interpreted in some way by the StateGraph.
Whenever some past state of any object is rewritten, StateGraph re-evaluates the state of the updated object
and all objects depending on it from the point of change to the present day.
-}

{- | `StateGraph k v` stores state timeline for each `k`, where timeline is a relation between the point in time and the state.
StateGraph also stores whenever the state of some object by key `k` is accessed by some other object to track all the dependencies.
-}
newtype StateGraph k v = StateGraph {unStateGraph ∷ RT.Map Res k (RT.SetR EventId, RT.MapR EventId v)}

class Same a where -- TODO: POC: temporary. A crutch to ensure short-circuiting when update doesn't need to be propagated.
  same ∷ a → a → Bool

instance Same SiteAccessLevel where
  same = (==)

instance (Same v) ⇒ Same (StateGraphEntry v) where
  same StateGraphEntrySampled StateGraphEntrySampled = True
  same (StateGraphEntryModified x) (StateGraphEntryModified y) = x `same` y
  same _ _ = False

newtype QueryC k v m a = QueryC {unQueryC ∷ StateC (Set k) (ReaderC (StateGraph k v) m) a}
  deriving (Functor, Applicative, Monad)

newtype UpdateC k v m a = UpdateC {unUpdateC ∷ StateC (Set k, Map k (AppIOC v)) (ReaderC (EventId, StateGraph k v) m) a}
  deriving (Functor, Applicative, Monad)

data StateGraphDeps ctx m where
  StateGraphDepsNil ∷ StateGraphDeps ctx AppIOC
  StateGraphDepsCons ∷
    (InferValT k, InferValT v, Typeable k, Ord k, RT.IsRadixKey k, Ser v) ⇒
    Asm ctx (StateGraph k v) →
    StateGraphDeps ctx m →
    StateGraphDeps ctx (QueryC k v m)

depsApplicativeProof ∷ StateGraphDeps ctx m → Dict (Applicative m)
depsApplicativeProof = \case
  StateGraphDepsNil → Dict
  StateGraphDepsCons _ _ → Dict

newtype DepsCache a = DepsCache {unDepsCache ∷ a} -- newtype to simplify inference

data RunWithDeps m ctx
  = ∀ depsAccessed depsCache.
    (InferValT depsCache) ⇒
    RunWithDeps
      !(Asm ctx (EventId → ∀ a. m a → AppIOC (a, depsAccessed), depsCache → AppIOC (Set EventId)))
      !(EventId → depsAccessed → depsAccessed → depsCache → AppIOC depsCache)
      !depsAccessed
      !depsCache

-- TODO: Same check!

-- | The core function: constructs new StateGraph.
mkStateGraph ∷
  ∀ ctx c event k v handlerM.
  (InferValT k, InferValT v, Ser event, InferValT event, InferContainerT c, Container c, RT.IsRadixKey k, Ser v, Typeable k, Ord k, Same v) ⇒
  -- | Events. They form the base of the stategraph.
  Asm ctx (RT.Map c EventId event) →
  -- | Every StateGraph is event-based, and works by interpreting events. Handler function for the event must be provided, along
  -- with list of other StateGraph's that act as dependencies for this one and could be queried.
  (StateGraphDeps ctx handlerM, event → UpdateC k v handlerM ()) →
  Asm ctx (StateGraph k v)
mkStateGraph evsA (depsA, hdl) =
  let
    affectedReads ∷ (Ser a) ⇒ EventId → (RT.SetR EventId, RT.MapR EventId a) → StateC (Set EventId) AppIOC ()
    affectedReads evId (reads, writes) = do
      let lbound = RT.RBRestricted False $ RT.toRadixKey evId
      upto <- join <$> RT.runNonDetMin (RT.lookup' (RT.selNonDetRanged (lbound, RT.RBUnrestricted)) writes)
      let rbound = case upto of
            Just (RT.FinalPath xs, _) -> RT.RBRestricted True xs
            _ -> RT.RBUnrestricted
      void $ RT.forNonDet_ (P.fromJust <$> RT.lookupKV (RT.selNonDetRanged (lbound, rbound)) reads)
        \(affId, _) -> modify (Set.insert affId)
    {-# SCC affectedReads #-}

    mkRunWithDeps ∷ StateGraphDeps ctx m → RunWithDeps m ctx
    mkRunWithDeps = \case
      StateGraphDepsNil → RunWithDeps (pure (const $ fmap (,()), \_ → pure Set.empty)) (\_ _ _ _ → pure ()) () ()
      StateGraphDepsCons @k2 dep deps
        | RunWithDeps otherRunA otherUpd otherEmptyAccessed otherCache0 ← mkRunWithDeps deps
        , Dict ← depsApplicativeProof deps →
            RunWithDeps @_ @_ @(Set k2, _) @(RT.MapR k2 (RT.SetR EventId), _)
              ( ( \(old, new) (otherRun, otherAffM) →
                    ( \evId (QueryC act) →
                        fmap (\((a, b), c) → (b, (a, c))) $ otherRun evId $ runReader (StateGraph new) $ runState (curry pure) Set.empty act
                    , \(cache, otherCache) → do
                        otherAff <- otherAffM otherCache
                        execState otherAff do
                          changedKeys <- RT.toListM =<< RT.diffId @_ @_ @Res AppForce old new
                          for changedKeys \(k, RT.fromMapDiffE (RT.empty, RT.empty) -> (snd -> oldTimeline, snd -> newTimeline)) -> do
                            cacheT ← fromMaybe RT.empty <$> RT.lookup (RT.selEq k) cache
                            updatedEvs ← RT.diffId AppForce oldTimeline newTimeline >>= RT.toListM @Res
                            for updatedEvs \(evId, _) →
                              affectedReads
                                evId
                                (cacheT, newTimeline)
                    )
                )
                  <$> buffered RT.empty (unStateGraph <$> dep)
                  <*> otherRunA
              )
              ( \evId (acc1, otherAcc1) (acc2, otherAcc2) (cache0, otherCache) →
                  (,)
                    <$> execState cache0 do
                      for_ (acc1 `Set.difference` acc2) \unwitness →
                        get @(RT.MapR k2 (RT.SetR EventId))
                          >>= RT.update
                            (alloc <=< traverse (RT.delete (RT.selEq evId)) <=< fetch)
                            (RT.selEq unwitness)
                          >>= put
                      for_ (acc2 `Set.difference` acc1) \witness →
                        get @(RT.MapR k2 (RT.SetR EventId))
                          >>= RT.update
                            (alloc <=< traverse (RT.insert (RT.selEq evId) ()) <=< fetch)
                            (RT.selEq witness)
                          >>= put
                    <*> otherUpd evId otherAcc1 otherAcc2 otherCache
              )
              (Set.empty, otherEmptyAccessed)
              (RT.empty, otherCache0)

    whilePop ∷ (Has (State (Set a)) sig m) ⇒ (a → m ()) → m ()
    whilePop f = do
      h0 ← get
      case Set.minView h0 of
        Nothing → pure ()
        Just (next, h) → put h *> f next *> whilePop f

    process ∷
      ∀ depsCache depsAccessed.
      (RT.Map c EventId event, RT.Map c EventId event) →
      (EventId → ∀ a. handlerM a → AppIOC (a, depsAccessed)) →
      (EventId → depsAccessed → depsAccessed → depsCache → AppIOC depsCache) →
      depsAccessed →
      StateC
        (RT.MapR k (RT.SetR EventId, RT.MapR EventId v))
        ( StateC
            (DepsCache depsCache)
            (StateC (Set EventId) AppIOC)
        )
        ()
    process (oldEvs, newEvs) runWithDeps updDepsCache emptyDepsAccessed =
      whilePop @EventId \evId → do
        let markChanged timeline = affectedReads evId timeline

        Dict ← pure $ depsApplicativeProof depsA
        prevStateGraph ← get @(RT.MapR k _)
        let runStateGraphUpdate (UpdateC a) =
              runReader (evId, StateGraph prevStateGraph)
                $ execState (Set.empty, Map.empty) a
            hdlEvFrom evSet = do
              evM ← RT.lookup (RT.selEq evId) evSet
              res ← for evM \ev →
                sendAI $ runWithDeps evId $ runStateGraphUpdate $ hdl ev
              pure $ fromMaybe ((Set.empty, Map.empty), emptyDepsAccessed) res
        ((oldReads, oldWrites), oldDeps) ← hdlEvFrom oldEvs
        ((newReads, newWrites), newDeps) ← hdlEvFrom newEvs

        let
          updater :: forall sig2 m2. Has (State (RT.MapR k (RT.SetR EventId, RT.MapR EventId v)) :+: AppIO) sig2 m2 ⇒
            (Maybe (RT.SetR EventId, RT.MapR EventId v) -> ReduceC m2 (RT.SetR EventId, RT.MapR EventId v)) -> k -> m2 ()
          updater cont delFromK =
              get @(RT.MapR k (RT.SetR EventId, RT.MapR EventId v))
              >>= RT.update
                ( \oldDelFromM →
                    alloc . Just =<< cont =<< fetch oldDelFromM
                )
                (RT.selEq delFromK)
              >>= put
          {-# INLINE updater #-}
        
        -- Delete reads
        for_ (Set.toList (oldReads `Set.difference` newReads)) $
          updater $ bimapM (RT.delete (RT.selEq evId)) pure . P.fromJust

        -- Create reads
        for_ (Set.toList (newReads `Set.difference` oldReads)) $
          updater $ bimapM (RT.insert (RT.selEq evId) ()) pure . fromMaybe (RT.empty, RT.empty)

        -- Remove deleted writes
        let fullyDeleted = oldWrites `Map.difference` newWrites
        for_ (Map.keys fullyDeleted) $
          updater \(P.fromJust -> timeline) -> do
            lift $ lift $ lift $ markChanged timeline
            bimapM pure (RT.delete $ RT.selEq evId) timeline

        -- Update entries
        for_ (Map.toList $ newWrites `Map.difference` fullyDeleted) \(updateFromK, newValM) → do
          newVal ← sendAI newValM
          -- TODO: temporary implementation
          let updateIfNeeded oldUpdateFrom oldValM = do
                oldVal ← fetch oldValM
                if maybe False (`same` newVal) oldVal
                  then E.empty
                  else do
                    lift
                      $ lift
                      $ lift
                      $ lift
                      $ lift
                      $ markChanged oldUpdateFrom
                    alloc $ Just newVal
          fromEmpty () $ updater
            (\(fromMaybe (RT.empty, RT.empty) → (oldUpdateReads, oldUpdateWrites)) →
              (oldUpdateReads,) <$> RT.update (updateIfNeeded (oldUpdateReads, oldUpdateWrites)) (RT.selEq evId) oldUpdateWrites)
            updateFromK

        -- deps
        put . DepsCache =<< sendAI . updDepsCache evId oldDeps newDeps . unDepsCache =<< get
    {-# SCC process #-}
   in
    mkRunWithDeps depsA & \(RunWithDeps runWithDepsA updDepsCache emptyDepsAccessed initDepsCache) →
      asmCached (initDepsCache, RT.empty)
        $ ( \(runWithDeps, queueDF) (oldEvs, newEvs) (depsCache0, mainCache0) → do
              queueD ← queueDF depsCache0
              queueE ← Set.fromList . fmap fst <$> (RT.toListM @Res =<< RT.diffId AppForce oldEvs newEvs)
              (depsCache, mainCache) ←
                evalState (queueE <> queueD)
                  $ runState (curry pure) (DepsCache depsCache0)
                  $ execState mainCache0
                  $ process (oldEvs, newEvs) runWithDeps updDepsCache emptyDepsAccessed
              pure (StateGraph mainCache, (unDepsCache depsCache, mainCache))
          )
        <$> runWithDepsA
        <*> buffered RT.empty evsA

data GetNowEventId m a where
  GetNowEventId ∷ GetNowEventId m EventId

data Query k v m a where
  Query ∷ k → Query k v m (Maybe v)

query ∷ (Has (Query k v) sig m) ⇒ k → m (Maybe v)
query = send . Query
{-# INLINE query #-}

data Update k v m a where
  Update ∷ k → AppIOC v → Update k v m ()

update ∷ (Has (Update k v) sig m) ⇒ k → AppIOC v → m ()
update k = send . Update k
{-# INLINE update #-}

hdlQuery ∷ (Has AppIO sig m, Ser v, Typeable k, RT.IsRadixKey k) ⇒ EventId → k → StateGraph k v → m (Maybe v)
hdlQuery nowEvId k (StateGraph queriedSG) = 
  RT.lookup (RT.selEq k) queriedSG >>= \case
    Nothing -> pure Nothing
    Just (_, queriedTimeline) ->
      let prevRange = (RT.RBUnrestricted, RT.RBRestricted False $ RT.toRadixKey nowEvId) in
      RT.runNonDetMax $
        P.fromJust <$> RT.lookup (RT.selNonDetRanged prevRange) queriedTimeline
{-# INLINE hdlQuery #-}

instance (Has (GetNowEventId :+: AppIO) sig m, Typeable k, Ord k, RT.IsRadixKey k, Ser v) ⇒ Algebra (Query k v :+: sig) (QueryC k v m) where
  alg hdl sig ctx = QueryC case sig of
    L (Query k) → do
      nowEvId ← send GetNowEventId
      modify $ Set.insert k
      queriedSG ← ask
      (ctx $>) <$> hdlQuery nowEvId k queriedSG
    R other → alg (unQueryC . hdl) (R (R other)) ctx
  {-# INLINE alg #-}

instance (Has AppIO sig m, Typeable k, Ord k, RT.IsRadixKey k, Ser v) ⇒ Algebra ((GetNowEventId :+: Query k v :+: Update k v) :+: sig) (UpdateC k v m) where
  alg hdl sig ctx = UpdateC case sig of
    L (L GetNowEventId) → do
      (evId, _ ∷ StateGraph k v) ← ask
      pure $ ctx $> evId
    L (R (L (Query k))) → do
      modify @(Set k, Map k (AppIOC v)) $ bimap (Set.insert k) id
      (nowEvId, queriedSG) ← ask
      (ctx $>) <$> hdlQuery nowEvId k queriedSG
    L (R (R (Update k v))) → do
      modify @(Set k, Map k (AppIOC v)) $ bimap id $ Map.insert k v
      pure $ ctx $> ()
    R other → alg (unUpdateC . hdl) (R (R other)) ctx
  {-# INLINE alg #-}

-- debug

toLists ∷ (Has AppIO sig m, RT.IsRadixKey k, Ser v, Typeable k) ⇒ StateGraph k v → m [(k, [(EventId, v)])]
toLists (StateGraph perKeyRT) = do
  perKey ← RT.toListM perKeyRT
  for perKey \(k, (_, perTimeRT)) →
    (k,) <$> RT.toListM perTimeRT

toListsFull ∷ (Has AppIO sig m, RT.IsRadixKey k, Ser v, Typeable k) ⇒ StateGraph k v → m [(k, [(EventId, Either () v)])]
toListsFull (StateGraph perKeyRT) = do
  perKey ← RT.toListM perKeyRT
  for perKey \(k, (perTimeRT1, perTimeRT2)) → do
    a <- RT.toListM perTimeRT1
    b <- RT.toListM perTimeRT2
    pure (k, sortBy (\(a', _) (b', _) -> compare b' a') (fmap Left <$> a) <> (fmap Right <$> b))
