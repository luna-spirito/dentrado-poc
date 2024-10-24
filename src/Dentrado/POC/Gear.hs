{-# LANGUAGE ApplicativeDo #-}
module Dentrado.POC.Gear where

import RIO hiding (asks, toList, runReader)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Effect.Fresh (Fresh)
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->) (..), Res, ValT (..), M (..), Gear (..), InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof, builtin, tryFromVal, AppForce (..), Container, InferContainerT, Delay, InferEValT (..), fetch, alloc, AppDelay (..))
import Dentrado.POC.Types (EventId (..), Event (..), SiteAccessLevel (..), StateGraphEntry (..), LocalId (..), Timestamp (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Effect.Reader (asks)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep)
import Data.Constraint (Dict(..))
import Dentrado.POC.TH (sFreshI)
import Control.Carrier.State.Church (evalState, put, get, execState, StateC, runState, modify)
import Control.Carrier.Reader (ReaderC, runReader)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.State (State)
import qualified RIO.Set as Set
import qualified Control.Effect.Empty as E
import qualified RIO.Map as Map

$(moduleId 3)

data GearTemplate' ctx out = forall cache cfg. GearTemplate' !(ValT cfg) !(ValT cache) !(GearTemplate ctx out cache cfg)

-- TODO: Separate current inputs from AppIOC into a separate monad.
-- TODO: USE RES FOR GEARS!!!
-- Slow operation.
gearFromFn :: (Typeable ctx, InferValT ctx, Ser cache, Typeable out) =>
  ValT cache ->
  cache ->
  GearFn ctx out cache ->
  AppIOC (Gear ctx out)
gearFromFn cacheT forkedCache gearFn = do
  serGearFn <- SerializedGearFn <$> unstableSerialized gearFn
  gearsFnIndexV <- asks envGearsIndex
  cache <- tryLazy gearsFnIndexV \gearsFnIndex ->
    RT.upsertChurch (RT.selEq serGearFn) gearsFnIndex <&> \case
      (Just exGearFn, _) -> Left exGearFn
      (Nothing, ins) -> Right do
        frV <- asks envFreshInd
        ind <- atomicModifyIORef' frV \old -> (old + 1, old)
        gearsV <- asks envGears
        modifyMVar_ gearsV $ pure . IMap.insert ind (Dynamic TypeRep forkedCache)
        (, ind) <$> ins ind
  pure $ UnsafeGear cacheT gearFn cache

confNewGear :: (Typeable ctx, InferValT ctx, {-InferValT cfg, InferValT cache, Ser cache,-} Typeable out) => GearTemplate' ctx out -> ctx -> AppIOC (Gear ctx out)
confNewGear (GearTemplate' cfgT cacheT@(valSerProof -> Dict) template@(UnsafeGearTemplate initCache conf _fn)) ctx = do
  cfg <- unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (ctx, Nothing)
  gearFromFn cacheT initCache $ GearFn cfgT cfg template

reconfGear :: (Typeable ctx, InferValT ctx, Typeable out) => Gear ctx out -> ctx -> AppIOC (Gear ctx out)
reconfGear (UnsafeGear cacheT@(valSerProof -> Dict) (GearFn cfgT oldCfg template@(UnsafeGearTemplate _ conf _)) oldCacheInd) newCtx = do
  gearsV <- asks envGears
  oldCache <- P.fromJust . fromDynamic . P.fromJust . IMap.lookup oldCacheInd <$> sendAI (readMVar gearsV)
  newCfg <- unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (newCtx, Just oldCfg)
  -- TODO: optimization: early return if oldCfg == newCfg.
  gearFromFn cacheT oldCache $ GearFn cfgT newCfg template

-- Generalized confNewGear and reconfGear
confGear :: (InferValT ctx, {-InferValT cfg, InferValT cache, Ser cache,-} Typeable ctx, Typeable out) =>
  GearTemplate' ctx out -> Maybe (Gear ctx out) -> ctx -> AppIOC (Gear ctx out)
confGear template exGearM ctx = case exGearM of
  Nothing -> confNewGear template ctx
  Just exGear -> reconfGear exGear ctx
{-# INLINE confGear #-}

runGear :: Gear ctx out -> AppIOC out
runGear (UnsafeGear cacheT@(valSerProof -> Dict) (GearFn cfgT cfg (UnsafeGearTemplate _ _ fn)) cacheInd) = do
  gearsV <- asks envGears
  oldCache <- P.fromJust . fromDynamic . P.fromJust . IMap.lookup cacheInd <$> sendAI (readMVar gearsV)
  (out, newCache) <- unM $ funApp' (ValTTuple cfgT cacheT) fn (cfg, oldCache)
  sendAI $ modifyMVar_ gearsV \gears -> pure $ IMap.insert cacheInd (Dynamic TypeRep newCache) gears -- TODO: better merging mechanisms to avoid rewrites
  pure out

builtinFun :: Has Fresh sig m => (a -> b) -> m (a :-> b)
builtinFun f = FunBuiltin <$> builtin f

builtinFunM :: Has Fresh sig m => (a -> f b) -> m (a :-> M f b)
builtinFunM f = builtinFun (M . f)

-- still unsafe
builtinGearTemplate' :: Has Fresh sig m => ValT cfg -> ValT cache -> cache -> ((ctx, Maybe cfg) -> AppIOC cfg) -> ((cfg, cache) -> AppIOC (out, cache)) -> m (GearTemplate' ctx out)
builtinGearTemplate' cfgT cacheT cache cfgM fnM = do
  cfg <- builtinFunM cfgM
  fn <- builtinFunM fnM
  pure $ GearTemplate' cfgT cacheT $ UnsafeGearTemplate cache cfg fn
{-# INLINE builtinGearTemplate #-}

builtinGearTemplate :: (Has Fresh sig m, InferValT cfg, InferValT cache) => cache -> ((ctx, Maybe cfg) -> AppIOC cfg) -> ((cfg, cache) -> AppIOC (out, cache)) -> m (GearTemplate' ctx out)
builtinGearTemplate = builtinGearTemplate' inferValT inferValT

-- TODO: to other module?
data Asm ctx out = forall cfg cache. Asm !(ValT cfg) !(ValT cache) !cache !((ctx, Maybe cfg) -> AppIOC cfg) !((cfg, cache) -> AppIOC (out, cache))

instance Functor (Asm ctx) where
  fmap f (Asm cfgT cacheT initial configure fn) = Asm cfgT cacheT initial configure $ fmap (bimap f id) . fn
  {-# INLINE fmap #-}

instance Applicative (Asm ctx) where
  pure x = Asm ValTUnit ValTUnit () (const $ pure ()) $ const $ pure (x, ())
  {-# INLINE pure #-}

  Asm cfg1T cache1T initial1 configure1 fn1 <*> Asm cfg2T cache2T initial2 configure2 fn2 = Asm
    (ValTTuple cfg1T cfg2T)
    (ValTTuple cache1T cache2T)
    (initial1, initial2)
    (\(ctx, cfgM) -> (,) <$> configure1 (ctx, fst <$> cfgM) <*> configure2 (ctx, snd <$> cfgM))
    \((cfg1, cfg2), (cache1, cache2)) -> (\(f', rcache1) (a', rcache2) -> (f' a', (rcache1, rcache2)))
      <$> fn1 (cfg1, cache1) <*> fn2 (cfg2, cache2)
    -- TODO: optimize for Units, removing unnecessary indirection
  {-# INLINE (<*>) #-}

asmGear :: (InferValT a, InferEValT out, Typeable a, Typeable out) => GearTemplate' a out -> Asm a out
asmGear template = Asm (ValTGear inferValT inferEValT) ValTUnit () {-_Unit-} (\(ctx, gearM) -> confGear template gearM ctx) \(gear, _) -> (,()) <$> runGear gear
{-# INLINE asmGear #-}

asmCached :: InferValT cache => cache -> Asm ctx (cache -> AppIOC (out, cache)) -> Asm ctx out
asmCached initial1 (Asm cfgT cacheT initial configure fn) = Asm cfgT (ValTTuple inferValT cacheT) (initial1, initial) configure
  \(cfg, (thisCache, otherCache)) -> fn (cfg, otherCache) >>= \(fn', outOtherCache) -> fmap (, outOtherCache) <$> fn' thisCache
{-# INLINE asmCached #-}

-- TODO: I *really* don't like this, but this thing relates to the question of how applicative/selective functors can be
-- embedded into algebraic effects.
-- asmBind :: Asm ctx a -> (a -> AppIOC b) -> Asm ctx b
-- asmBind (Asm cfgT cacheT initial configure fn) f = Asm cfgT cacheT initial configure $ fn >=> \(a, cache) -> (, cache) <$> f a
-- {-# INLINE asmBind #-}

asmAppIO :: Asm ctx (AppIOC a) -> Asm ctx a
asmAppIO (Asm cfgT cacheT initial configure fn) = Asm cfgT cacheT initial configure $
  fn >=> \(val, cache) -> (, cache) <$> val
{-# INLINE asmAppIO #-}

builtinAsmGearTemplate :: (Has Fresh sig m, InferValT ctx, Typeable ctx) => Asm ctx out -> m (GearTemplate' ctx out)
builtinAsmGearTemplate (Asm cfgT cacheT initial configure fn) =
  builtinGearTemplate' cfgT cacheT initial configure fn

events :: GearTemplate' () (RT.MapR EventId Event)
events = $sFreshI $ builtinAsmGearTemplate $ asmCached
  (0, RT.empty @Res)
  $ pure \(oldLen, oldRes) -> do
      (evs, newLen) <- readMVar =<< asks envEvents
      newRes <- foldM
        (\rt (t, ev) ->
        tryFromVal @Event ev & maybe (pure rt) \v ->
          RT.insert (RT.selEq t) v rt)
        oldRes
        (take (newLen - oldLen) evs)
      pure (newRes, (newLen, newRes))

-- indexes

-- object or event -based? Both!

-- Bad oversimplified implementation
-- Actual one should maximise use of immutable data structures.
-- How? Select maximal subtree
bucket :: (Has Fresh sig m, RT.IsRadixKey k, RT.IsRadixKey bucketK, Foldable t, InferContainerT c1, InferContainerT c2, InferContainerT c3, InferValT bucketK, InferValT v, InferValT k, InferValT ctx, Ser v, Container c2, Container c3, Container c1, Typeable k, Typeable ctx, Typeable bucketK) =>
  Asm ctx (RT.Map c3 k v) ->
  (v -> t bucketK) ->
  m (GearTemplate' ctx (RT.Map c2 bucketK (RT.Map c1 k v)))
bucket inputAsm semaphore = builtinAsmGearTemplate $ asmCached
  (RT.empty, RT.empty) -- (old input, old index)
  $ do
    newInp <- inputAsm
    pure \(oldInp, oldBuckets) -> do
      let updBuckets buckets1 (k, vD) =
            let updWith updater v buckets2 = foldM
                  (\buckets targetBucketK -> do
                    (fromMaybe RT.empty -> targetBucket, ins) <- RT.upsertChurch (RT.selEq targetBucketK) buckets
                    ins =<< updater v targetBucket)
                  buckets2
                  (semaphore v)
            in RT.hdlMapDiffE
              (updWith $ const $ RT.delete (RT.selEq k))
              (updWith $ RT.insert (RT.selEq k))
              vD
              buckets1
      newBuckets <- foldM
        updBuckets
        oldBuckets
        =<< RT.toListM @Res =<< RT.diffId AppForce oldInp newInp
      pure (newBuckets, (newInp, newBuckets))

lookupBucket :: (Container c1, Container c2, RT.IsRadixKey k1, Ser v, Typeable k1, Typeable k2) => k1 -> RT.Map c1 k1 (RT.Map c2 k2 v) -> AppIOC (RT.Map c2 k2 v)
lookupBucket k1 = fmap (fromMaybe RT.empty) . RT.lookup (RT.selEq k1)
{-# INLINE lookupBucket #-}

buffered :: InferValT out => out -> Asm ctx out -> Asm ctx (out, out)
buffered cache0 outA = asmCached cache0 do
  out <- outA
  pure \old -> pure ((old, out), out)
{-# INLINE buffered #-}

-- Notice: StateGraph updates could modify multiple objects at the same time.
newtype StateGraph k v = StateGraph { unStateGraph :: RT.Map Res k (RT.Map Res EventId (StateGraphEntry v)) }

type UserId = EventId
type LoginId = EventId

class Same a where -- TODO: temporary
  same :: a -> a -> Bool

instance Same v => Same (StateGraphEntry v) where
  same EntrySampled EntrySampled = True
  same (EntryModified x) (EntryModified y) = x `same` y
  same _ _ = False

{-
mkStateGraph :: forall ctx c event k v. (InferValT k, InferValT v, Ser event, InferValT event, InferContainerT c, Container c, RT.IsRadixKey k, Ser v, Typeable k) =>
  Asm ctx (RT.Map c EventId event) -> (k -> v) -> (event -> StateGraphUpdateC k v AppIOC ()) -> Asm ctx (StateGraph k v)
mkStateGraph inpM def fn = asmCached
  (RT.empty, RT.empty) -- (old input, result)
  $ inpM <&> \newInp (oldInp, oldRes) -> do
    diffInp0List <- (RT.toListM @Res =<< RT.diffId AppForce oldInp newInp)
    let diffInp0 = Set.fromList $ (\(evId, diff) -> Set.Entry evId $ Just diff) <$> diffInp0List
    newRes <- execState oldRes $ execState diffInp0 $ whilePop \(Set.Entry evId diffM0) -> do
      diffM <- diffM0 & maybe (RT.mkMapDiffE <$> RT.lookup (RT.selEq evId) oldInp <*> RT.lookup (RT.selEq evId) newInp) (pure . Just)
      let runFn ev ctx = do
            UnsafeRevList r <- fn ev & \(StateGraphUpdateC m) -> lift $ lift $ runReader (evId, StateGraph ctx) $ runWriter (\a _ -> pure a) m
            pure r
      case diffM of
        Nothing -> pure ()
        Just diff -> RT.hdlMapDiffE
          (\delEv () -> do
            upds <- runFn delEv oldRes
            for_ upds \(k, _) ->
              get @(RT.Map Res k (RT.Map Res EventId (StateGraphEntry v)))
              >>= RT.update
                (alloc <=< traverse (RT.delete (RT.selEq evId)) <=< fetch)
                (RT.selEq k)
              >>= put -- SHOULD STILL CAUSE UPDATES!
            )
          (\addEv () -> do
            upds <- runFn addEv =<< get
            _
            -- for_ upds \(k, )
            )
          diff
          ()
    pure (StateGraph newRes, (newInp, newRes))
-}

-- Dependent types is too much to represent this, this must be MUCH easier, although I believe that we'll have to 
-- For querying extra dependencies.
newtype StateGraphQueryC k v m a = StateGraphQueryC (StateC (Set k) (ReaderC (StateGraph k v) m) a)
  deriving (Functor, Applicative, Monad)

-- For updating the StateGraph itself.
newtype StateGraphUpdateC k v m a = StateGraphUpdateC (StateC (Map k (StateGraphEntry (AppIOC v))) (ReaderC (EventId, k -> v, StateGraph k v) m) a)
  deriving (Functor, Applicative, Monad)

data StateGraphDeps ctx m where
  StateGraphDepsNil :: StateGraphDeps ctx AppIOC
  StateGraphDepsCons ::
    (InferValT k, InferValT v, Typeable k, Ord k, RT.IsRadixKey k, Ser v) =>
    Asm ctx (StateGraph k v) ->
    StateGraphDeps ctx m ->
    StateGraphDeps ctx (StateGraphQueryC k v m)

depsApplicativeProof :: StateGraphDeps ctx m -> Dict (Applicative m)
depsApplicativeProof = \case
  StateGraphDepsNil -> Dict
  StateGraphDepsCons _ _ -> Dict

newtype DepsCache a = DepsCache { unDepsCache :: a } -- newtype to simplify inference

-- data RunWithDeps' m accessed = RunWithDeps' !(forall a. m a -> AppIOC (a, accessed))
data RunWithDeps m ctx = forall depsAccessed depsCache.
  InferValT depsCache => RunWithDeps
  !(Asm ctx (EventId -> forall a. m a -> AppIOC (a, depsAccessed), depsCache -> AppIOC (Set EventId)))
  !(EventId -> depsAccessed -> depsAccessed -> depsCache -> AppIOC depsCache)
  !depsAccessed
  !depsCache

mkStateGraph :: forall ctx c event k v handlerM. (InferValT k, InferValT v, Ser event, InferValT event, InferContainerT c, Container c, RT.IsRadixKey k, Ser v, Typeable k, Ord k, Same v) =>
  Asm ctx (RT.Map c EventId event) -> -- Events. They form the base of the stategraph.
  -- Every StateGraph is event-based, and works by interpreting events.
  (k -> v) -> -- Initial, "day 0" state of all objects.
  (StateGraphDeps ctx handlerM, event -> StateGraphUpdateC k v handlerM ()) ->
  -- (event -> StateGraphUpdateC k v AppIOC ()) ->
  Asm ctx (StateGraph k v)
mkStateGraph evsA initState (depsA, hdl) =
  let
    isWriteEntry = \case
          EntryModified _ -> True
          _ -> False
    isWriteEntryMaybe = maybe False isWriteEntry

    affectedReads :: (Container c2, Ser e) => EventId -> RT.Map c2 EventId e -> (e -> Bool) -> (e -> Bool) -> StateC (Set EventId) AppIOC ()
    affectedReads evId rt isWrite isRelevant =
      RT.forNonDet_
        (RT.lookupKV (RT.selNonDetRanged (RT.RBRestricted False $ RT.toRadixKey evId, RT.RBUnrestricted)) rt)
        $ P.fromJust >>> \(affId, aff) -> do
          when (isRelevant aff) $ modify (Set.insert affId)
          pure $ not $ isWrite aff -- continue if not overwritten

    mkRunWithDeps :: StateGraphDeps ctx m -> RunWithDeps m ctx
    mkRunWithDeps = \case
      StateGraphDepsNil -> RunWithDeps (pure (const $ fmap (, ()), \_ -> pure Set.empty)) (\_ _ _ _ -> pure ()) () ()
      StateGraphDepsCons @k2 dep deps
        | RunWithDeps otherRunA otherUpd otherEmptyAccessed otherCache0 <- mkRunWithDeps deps
        , Dict <- depsApplicativeProof deps ->
        RunWithDeps @_ @_ @(Set k2, _) @(RT.MapR k2 (RT.SetR EventId), _)
          ((\(old, new) (otherRun, otherAff) ->
            (\evId (StateGraphQueryC act) ->
              fmap (\((a, b), c) -> (b, (a, c))) $ otherRun evId $ runReader (StateGraph new) $ runState (curry pure) Set.empty act
            , \(cache, otherCache) -> otherAff otherCache >>= flip execState (
              RT.diffId @_ @_ @Res AppForce old new >>= RT.toListM >>= traverse_ \(k, RT.fromMapDiffE RT.empty -> (oldT, newT)) -> do
                cacheT <- fromMaybe RT.empty <$> RT.lookup (RT.selEq k) cache
                unified <- lift $ RT.mergeId AppDelay (RT.toDelayed newT) (RT.toDelayed cacheT)
                updatedEvs <- lift $
                  mapMaybe (\(affId, RT.unMapDiffE -> (oldEv, newEv)) -> guard (isWriteEntryMaybe oldEv || isWriteEntryMaybe newEv) *> Just affId)
                  <$> (RT.diffId AppForce oldT newT >>= RT.toListM @Res)
                for_ updatedEvs \evId -> affectedReads @Delay evId unified
                  (fst >>> isWriteEntryMaybe)
                  (snd >>> \case
                    Just () -> True
                    Nothing -> False)
            )))
            <$> buffered RT.empty (unStateGraph <$> dep)
            <*> otherRunA)
          (\evId (acc1, otherAcc1) (acc2, otherAcc2) (cache0, otherCache) -> (,)
            <$> execState cache0 do
              for_ (acc1 `Set.difference` acc2) \unwitness ->
                get @(RT.MapR k2 (RT.SetR EventId))
                >>= RT.update
                  (alloc <=< traverse (RT.delete (RT.selEq evId)) <=< fetch)
                  (RT.selEq unwitness)
                >>= put
              for_ (acc2 `Set.difference` acc1) \witness ->
                get @(RT.MapR k2 (RT.SetR EventId))
                >>= RT.update
                  (alloc <=< traverse (RT.insert (RT.selEq evId) ()) <=< fetch)
                  (RT.selEq witness)
                >>= put
            <*> otherUpd evId otherAcc1 otherAcc2 otherCache)
          (Set.empty, otherEmptyAccessed)
          (RT.empty, otherCache0)

    whilePop :: Has (State (Set a)) sig m => (a -> m ()) -> m ()
    whilePop f = do
      h0 <- get
      case Set.minView h0 of
        Nothing -> pure ()
        Just (next, h) -> put h *> f next

    process :: forall depsCache depsAccessed.
      (RT.Map c EventId event, RT.Map c EventId event) ->
      (EventId -> forall a. handlerM a -> AppIOC (a, depsAccessed)) ->
      (EventId -> depsAccessed -> depsAccessed -> depsCache -> AppIOC depsCache) ->
      depsAccessed ->
      StateC (RT.MapR k (RT.Map Res EventId (StateGraphEntry v)))
        (StateC (DepsCache depsCache)
          (StateC (Set EventId) AppIOC)) ()
    process (oldEvs, newEvs) runWithDeps updDepsCache emptyDepsAccessed =
      whilePop @EventId \evId -> do
        let markChanged timeline = affectedReads evId timeline isWriteEntry (const True)
        
        Dict <- pure $ depsApplicativeProof depsA
        prevStateGraph <- get @(RT.MapR k _)
        let runStateGraphUpdate (StateGraphUpdateC a) =
              runReader (evId, initState, StateGraph prevStateGraph) $
              runState (\res  _ -> pure res) Map.empty a
            hdlEvFrom evSet = do
              evM <- RT.lookup (RT.selEq evId) evSet
              res <- for evM \ev ->
                sendAI $ runWithDeps evId $ runStateGraphUpdate $ hdl ev
              pure $ fromMaybe (Map.empty, emptyDepsAccessed) res
        (oldMain, oldDeps) <- hdlEvFrom oldEvs
        (newMain, newDeps) <- hdlEvFrom newEvs
        -- Remove deleted entries
        let fullyDeleted = oldMain `Map.difference` newMain
        for_ (Map.toList fullyDeleted) \(delFromK, deleted) ->
          get @(RT.MapR k (RT.MapR EventId (StateGraphEntry v))) >>=
          RT.update
            (\oldDelFromM -> do
              oldDelFrom <- P.fromJust <$> fetch oldDelFromM
              when (isWriteEntry deleted) $ lift $ lift $ lift $ markChanged oldDelFrom
              alloc . Just =<< RT.delete (RT.selEq evId) oldDelFrom)
            (RT.selEq delFromK) >>=
          put

        -- Update entries
        for_ (Map.toList $ newMain `Map.difference` fullyDeleted) \(updateFromK, newValM) -> do
          newVal <- case newValM of
            EntrySampled -> pure EntrySampled
            EntryModified xM -> EntryModified <$> sendAI xM
          -- TODO: temporary implementation
          let updateIfNeeded oldUpdateFrom oldValM = do
                oldVal <- fetch oldValM
                if maybe False (`same` newVal) oldVal
                  then E.empty
                  else do
                    when (isWriteEntryMaybe oldVal || isWriteEntry newVal) $
                      lift $ lift $ lift $ lift $ lift $ markChanged oldUpdateFrom
                    alloc $ Just newVal
          runEmpty (pure False) (const $ pure True) $ RT.update
            (\oldUpdateFromM -> do
              oldUpdateFrom <- fromMaybe RT.empty <$> fetch oldUpdateFromM
              alloc . Just =<< RT.update (updateIfNeeded oldUpdateFrom) (RT.selEq evId) oldUpdateFrom)
            (RT.selEq updateFromK) =<< get @(RT.MapR k (RT.MapR EventId (StateGraphEntry v)))

        -- deps
        put . DepsCache =<< sendAI . updDepsCache evId oldDeps newDeps . unDepsCache =<< get
            
  in mkRunWithDeps depsA & \(RunWithDeps runWithDepsA updDepsCache emptyDepsAccessed initDepsCache) ->
    asmCached (initDepsCache, RT.empty) $
      (\(runWithDeps, queueDF) (oldEvs, newEvs) (depsCache0, mainCache0) -> do
        queueD <- queueDF depsCache0
        queueE <- Set.fromList . fmap fst <$> (RT.toListM @Res =<< RT.diffId AppForce oldEvs newEvs)
        (depsCache, mainCache) <- evalState (queueE <> queueD) $
          runState (curry pure) (DepsCache depsCache0) $
          execState mainCache0 $
          process (oldEvs, newEvs) runWithDeps updDepsCache emptyDepsAccessed
        pure (StateGraph mainCache, (unDepsCache depsCache, mainCache)))
      <$> runWithDepsA
      <*> buffered RT.empty evsA

-- data MultiGet

-- mkStateGraph

-- sal :: GearTemplate' UserId (StateGraph UserId SiteAccessLevel)
-- sal = $sFreshI $ builtinAsmGearTemplate $ mkStateGraph
--   _
--   _
--   _

testSuite :: [Event]
testSuite =
  [ (AdminSetAccessLevel (e 0) (e 1) SalModerator)
  , (AdminSetAccessLevel (e 1) (e 1) SalAdmin)
  , (AdminSetAccessLevel (e 0) (e 2) SalAdmin)
  ]
  where e = EventId (Timestamp 0) . LocalId
