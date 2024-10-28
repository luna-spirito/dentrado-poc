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
import Dentrado.POC.Memory (AppDelay (..), AppForce (..), AppIO, AppIOC, Container, Delay, InferContainerT, InferValT (..), Res, Ser, alloc, fetch, sendAI)
import Dentrado.POC.Types (EventId (..), SiteAccessLevel, StateGraphEntry (..), fromEmpty, maybeToEmpty)
import RIO hiding (ask, runReader)
import qualified RIO.Map as Map
import qualified RIO.Partial as P
import qualified RIO.Set as Set

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
newtype StateGraph k v = StateGraph {unStateGraph ∷ RT.Map Res k (RT.Map Res EventId (StateGraphEntry v))}

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

newtype UpdateC k v m a = UpdateC {unUpdateC ∷ StateC (Map k (StateGraphEntry (AppIOC v))) (ReaderC (EventId, StateGraph k v) m) a}
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
    isWriteEntry = \case
      StateGraphEntryModified _ → True
      _ → False
    isWriteEntryMaybe = maybe False isWriteEntry

    affectedReads ∷ (Container c2, Ser e) ⇒ EventId → RT.Map c2 EventId e → (e → Bool) → (e → Bool) → StateC (Set EventId) AppIOC ()
    affectedReads evId rt isWrite isRelevant =
      RT.forNonDet_
        (RT.lookupKV (RT.selNonDetRanged (RT.RBRestricted False $ RT.toRadixKey evId, RT.RBUnrestricted)) rt)
        $ P.fromJust
        >>> \(affId, aff) → do
          when (isRelevant aff) $ modify (Set.insert affId)
          pure $ not $ isWrite aff -- continue if not overwritten
    {-# SCC affectedReads #-}

    mkRunWithDeps ∷ StateGraphDeps ctx m → RunWithDeps m ctx
    mkRunWithDeps = \case
      StateGraphDepsNil → RunWithDeps (pure (const $ fmap (,()), \_ → pure Set.empty)) (\_ _ _ _ → pure ()) () ()
      StateGraphDepsCons @k2 dep deps
        | RunWithDeps otherRunA otherUpd otherEmptyAccessed otherCache0 ← mkRunWithDeps deps
        , Dict ← depsApplicativeProof deps →
            RunWithDeps @_ @_ @(Set k2, _) @(RT.MapR k2 (RT.SetR EventId), _)
              ( ( \(old, new) (otherRun, otherAff) →
                    ( \evId (QueryC act) →
                        fmap (\((a, b), c) → (b, (a, c))) $ otherRun evId $ runReader (StateGraph new) $ runState (curry pure) Set.empty act
                    , \(cache, otherCache) →
                        otherAff otherCache
                          >>= flip
                            execState
                            ( RT.diffId @_ @_ @Res AppForce old new >>= RT.toListM >>= traverse_ \(k, RT.fromMapDiffE RT.empty → (oldT, newT)) → do
                                cacheT ← fromMaybe RT.empty <$> RT.lookup (RT.selEq k) cache
                                unified ← lift $ RT.mergeId AppDelay (RT.toDelayed newT) (RT.toDelayed cacheT)
                                updatedEvs ←
                                  lift
                                    $ mapMaybe (\(affId, RT.unMapDiffE → (oldEv, newEv)) → guard (isWriteEntryMaybe oldEv || isWriteEntryMaybe newEv) *> Just affId)
                                    <$> (RT.diffId AppForce oldT newT >>= RT.toListM @Res)
                                for_ updatedEvs \evId →
                                  affectedReads @Delay
                                    evId
                                    unified
                                    (fst >>> isWriteEntryMaybe)
                                    ( snd >>> \case
                                        Just () → True
                                        Nothing → False
                                    )
                            )
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
        (RT.MapR k (RT.Map Res EventId (StateGraphEntry v)))
        ( StateC
            (DepsCache depsCache)
            (StateC (Set EventId) AppIOC)
        )
        ()
    process (oldEvs, newEvs) runWithDeps updDepsCache emptyDepsAccessed =
      whilePop @EventId \evId → do
        let markChanged timeline = affectedReads evId timeline isWriteEntry (const True)

        Dict ← pure $ depsApplicativeProof depsA
        prevStateGraph ← get @(RT.MapR k _)
        let runStateGraphUpdate (UpdateC a) =
              runReader (evId, StateGraph prevStateGraph)
                $ execState Map.empty a
            hdlEvFrom evSet = do
              evM ← RT.lookup (RT.selEq evId) evSet
              res ← for evM \ev →
                sendAI $ runWithDeps evId $ runStateGraphUpdate $ hdl ev
              pure $ fromMaybe (Map.empty, emptyDepsAccessed) res
        (oldMain, oldDeps) ← hdlEvFrom oldEvs
        (newMain, newDeps) ← hdlEvFrom newEvs
        -- Remove deleted entries
        let fullyDeleted = oldMain `Map.difference` newMain
        for_ (Map.toList fullyDeleted) \(delFromK, deleted) →
          get @(RT.MapR k (RT.MapR EventId (StateGraphEntry v)))
            >>= RT.update
              ( \oldDelFromM → do
                  oldDelFrom ← P.fromJust <$> fetch oldDelFromM
                  when (isWriteEntry deleted) $ lift $ lift $ lift $ markChanged oldDelFrom
                  alloc . Just =<< RT.delete (RT.selEq evId) oldDelFrom
              )
              (RT.selEq delFromK)
            >>= put

        -- Update entries
        for_ (Map.toList $ newMain `Map.difference` fullyDeleted) \(updateFromK, newValM) → do
          newVal ← case newValM of
            StateGraphEntrySampled → pure StateGraphEntrySampled
            StateGraphEntryModified xM → StateGraphEntryModified <$> sendAI xM
          -- TODO: temporary implementation
          let updateIfNeeded oldUpdateFrom oldValM = do
                oldVal ← fetch oldValM
                if maybe False (`same` newVal) oldVal
                  then E.empty
                  else do
                    when (isWriteEntryMaybe oldVal || isWriteEntry newVal)
                      $ lift
                      $ lift
                      $ lift
                      $ lift
                      $ lift
                      $ markChanged oldUpdateFrom
                    alloc $ Just newVal
          fromEmpty ()
            $ get @(RT.MapR k (RT.MapR EventId (StateGraphEntry v)))
            >>= RT.update
              ( \oldUpdateFromM → do
                  oldUpdateFrom ← fromMaybe RT.empty <$> fetch oldUpdateFromM
                  alloc . Just =<< RT.update (updateIfNeeded oldUpdateFrom) (RT.selEq evId) oldUpdateFrom
              )
              (RT.selEq updateFromK)
            >>= put

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
hdlQuery nowEvId k (StateGraph queriedSG) = RT.runNonDetMax do
  queriedTimeline ← maybeToEmpty =<< RT.lookup (RT.selEq k) queriedSG
  -- Range in which we search for the previous entry
  let prevRange = (RT.RBUnrestricted, RT.RBRestricted False $ RT.toRadixKey nowEvId)
  candidate ← maybeToEmpty =<< RT.lookup (RT.selNonDetRanged prevRange) queriedTimeline
  case candidate of
    StateGraphEntrySampled → E.empty
    StateGraphEntryModified v → pure v
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
      modify @(Map k (StateGraphEntry (AppIOC v))) $ Map.alter (Just . fromMaybe StateGraphEntrySampled) k
      (nowEvId, queriedSG) ← ask
      (ctx $>) <$> hdlQuery nowEvId k queriedSG
    L (R (R (Update k v))) → do
      modify @(Map k (StateGraphEntry (AppIOC v))) $ Map.insert k (StateGraphEntryModified v)
      pure $ ctx $> ()
    R other → alg (unUpdateC . hdl) (R (R other)) ctx
  {-# INLINE alg #-}

-- debug

toLists ∷ (Has AppIO sig m, RT.IsRadixKey k, Ser v, Typeable k) ⇒ StateGraph k v → m [(k, [(EventId, v)])]
toLists (StateGraph perKeyRT) = do
  perKey ← RT.toListM perKeyRT
  for perKey \(k, perTimeRT) →
    (k,) <$> do
      perTime ← RT.toListM perTimeRT
      let perTimeFiltered =
            perTime & mapMaybe \(evId, entry) →
              (evId,) <$> case entry of
                StateGraphEntrySampled → Nothing
                StateGraphEntryModified v → Just v
      pure perTimeFiltered
