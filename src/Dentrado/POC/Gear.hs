{-# LANGUAGE ApplicativeDo #-}
module Dentrado.POC.Gear where

import RIO hiding (asks, toList, runReader)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Effect.Fresh (Fresh)
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->) (..), Res, ValT (..), M (..), Gear (..), InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof, builtin, tryFromVal, AppForce (..), Container, InferContainerT, RevList (..), Delay, EValT (..), InferEValT (..), fetch, alloc)
import Dentrado.POC.Types (RadixTree, EventId (..), Event (..), SiteAccessLevel (..), MapDiffE, StateGraphEntry, LocalId (..), Timestamp (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Effect.Reader (asks)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep, type (:~~:) (..), eqTypeRep)
import Data.Constraint (Dict(..))
import Dentrado.POC.TH (sFreshI)
import Control.Applicative.Free.Final (Ap, runAp_, runAp, liftAp)
import qualified RIO.List as L
import GHC.Exts (IsList(..))
import Control.Carrier.State.Church (evalState, put, get, execState, StateC, runState, modify)
import Data.Functor.Compose (Compose(..))
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Carrier.Reader (ReaderC, runReader)
import Data.Coerce (coerce)
import qualified Data.Heap as Heap
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.State (State)
import Data.Heap (Heap)
import qualified RIO.Set as Set
import qualified Control.Effect.Empty as E

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

-- newtype StateGraphUpdateC k v m a = StateGraphUpdateC (WriterC (RevList (k, AppIOC (StateGraphEntry v))) (ReaderC (EventId, StateGraph k v) m) a)

whilePop :: Has (State (Heap v)) sig m => (v -> m ()) -> m ()
whilePop f = do
  h0 <- get
  case Heap.viewMin h0 of
    Nothing -> pure ()
    Just (next, h) -> put h *> f next

class Same a where
  same :: a -> a -> Bool

{-
mkStateGraph :: forall ctx c event k v. (InferValT k, InferValT v, Ser event, InferValT event, InferContainerT c, Container c, RT.IsRadixKey k, Ser v, Typeable k) =>
  Asm ctx (RT.Map c EventId event) -> (k -> v) -> (event -> StateGraphUpdateC k v AppIOC ()) -> Asm ctx (StateGraph k v)
mkStateGraph inpM def fn = asmCached
  (RT.empty, RT.empty) -- (old input, result)
  $ inpM <&> \newInp (oldInp, oldRes) -> do
    diffInp0List <- (RT.toListM @Res =<< RT.diffId AppForce oldInp newInp)
    let diffInp0 = Heap.fromList $ (\(evId, diff) -> Heap.Entry evId $ Just diff) <$> diffInp0List
    newRes <- execState oldRes $ execState diffInp0 $ whilePop \(Heap.Entry evId diffM0) -> do
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
newtype StateGraphUpdateC k v m a = StateGraphUpdateC (StateC (Map k (StateGraphEntry (AppIOC v))) (ReaderC (EventId, StateGraph k v) m) a)
  deriving (Functor, Applicative, Monad)

data StateGraphDeps ctx m where
  StateGraphDepsNil :: StateGraphDeps ctx AppIOC
  StateGraphDepsCons ::
    (InferValT k, InferValT v, Typeable k, Ord k, RT.IsRadixKey k) =>
    Asm ctx (StateGraph k v) ->
    StateGraphDeps ctx m ->
    StateGraphDeps ctx (StateGraphQueryC k v m)

depsApplicativeProof :: StateGraphDeps ctx m -> Dict (Applicative m)
depsApplicativeProof = \case
  StateGraphDepsNil -> Dict
  StateGraphDepsCons _ _ -> Dict

-- data RunWithDeps' m accessed = RunWithDeps' !(forall a. m a -> AppIOC (a, accessed))
data RunWithDeps m ctx = forall accessed cache. RunWithDeps
  !(Asm ctx (EventId -> forall a. m a -> AppIOC (a, accessed), ()))
  !(EventId -> accessed -> accessed -> cache -> AppIOC cache)
  !cache

mkStateGraph :: forall ctx c event k v handlerM. (InferValT k, InferValT v, Ser event, InferValT event, InferContainerT c, Container c, RT.IsRadixKey k, Ser v, Typeable k) =>
  Asm ctx (RT.Map c EventId event) -> -- Events. They form the base of the stategraph.
  -- Every StateGraph is event-based, and works by interpreting events.
  (k -> v) -> -- Initial, "day 0" state of all objects.
  (StateGraphDeps ctx handlerM, event -> StateGraphUpdateC k v handlerM ()) ->
  -- (event -> StateGraphUpdateC k v AppIOC ()) ->
  Asm ctx (StateGraph k v)
mkStateGraph evsA init (depsA, hdl) =
  let
    affectedReads :: EventId -> RT.MapR EventId v -> (v -> Maybe Bool) -> AppIOC (Heap EventId)
    affectedReads evId rt classify =
      execState Heap.empty $ RT.forNonDet_
        (RT.lookupKV (RT.selNonDetRanged (RT.RBRestricted False $ RT.toRadixKey evId, RT.RBUnrestricted)) rt)
        $ P.fromJust >>> \(affId, aff) -> case classify aff of
            Nothing -> pure True
            Just isWrite -> do
              modify (Heap.insert affId)
              pure $ not isWrite -- continue if not overwritten
    
    runWithDeps :: StateGraphDeps ctx m -> RunWithDeps m ctx
    runWithDeps = \case
      StateGraphDepsNil -> RunWithDeps (pure (const $ fmap (, ()), ())) (const $ const $ const $ const $ pure ()) ()
      StateGraphDepsCons @k2 dep deps
        | RunWithDeps otherRunA otherUpd otherCache0 <- runWithDeps deps
        , Dict <- depsApplicativeProof deps ->
        RunWithDeps @_ @_ @(Set k2, _) @(RT.MapR k2 (RT.SetR EventId), _)
          ((\(old, new) (otherRun, _) ->
            (\evId (StateGraphQueryC act) ->
              fmap (\((a, b), c) -> (b, (a, c))) $ otherRun evId $ runReader (StateGraph new) $ runState (curry pure) Set.empty act, ()))
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
          (RT.empty, otherCache0)
  in _
  -- let 
  -- let
  --   withQueue xA = asmAppIO $
  --     (\(oldEvs, newEvs) x -> do
  --       diffEvsList <- RT.toListM @Res =<< RT.diffId AppForce oldEvs newEvs
  --       let queue = Heap.fromList $ (\(evId, diff) -> Heap.Entry evId $ Just diff) <$> diffEvsList
  --       evalState queue x)
  --     <$> buffered RT.empty evsA
  --     <*> xA
  -- in withQueue $ asmCached RT.empty _
      
  --asmCached
--   RT.empty -- result
--   do
--     _
  -- id <$> pure undefined
    
  -- let
  --   mkRunWithDeps :: forall m. StateGraphDeps ctx m -> Asm ctx (NatTr m AppIOC)
  --   mkRunWithDeps = \case
  --     StateGraphDepsNil -> pure $ NatTr id
  --     StateGraphDepsCons depA rdeps -> do
  --       NatTr rRunWithDeps <- mkRunWithDeps rdeps
  --       dep <- depA
  --       pure $ NatTr \(StateGraphQueryC k) -> runReaderC dep _


  -- _
  -- FIRST, query the dependencies
  
  --asmCached
  -- _
  -- _



    {-
    We process heap, one element by another.
    New elements could be added to the heap.
    After we finish processing the heap, 
    -}

-- data MultiUpdate k v m a where
--   MultiGet :: k -> MultiUpdate k v m v
--   MultiSet :: k -> v -> MultiUpdate k v m ()

-- newtype MultiUpdateC k v m a = MultiUpdateC (forall r. (a -> m r) -> (k -> m v) -> (k -> v -> m ()) -> m r)
--   deriving Functor

-- instance Applicative (MultiUpdateC k v m) where
--   pure x = MultiUpdateC \p _ _ -> p x
--   {-# INLINE pure #-}
--   MultiUpdateC f <*> MultiUpdateC a = MultiUpdateC \p g s -> f (\f' -> a (p . f') g s) g s
--   {-# INLINE (<*>) #-}

-- instance Monad (MultiUpdateC k v m) where
--   MultiUpdateC a >>= f = MultiUpdateC \p g s -> a (\a' -> f a' & \(MultiUpdateC b) -> b p g s) g s
--   {-# INLINE (>>=) #-}

-- runMultiUpdate :: (a -> m r) -> (k -> m v) -> (k -> v -> m ()) -> m v
-- runMultiUpdate = _

-- instance Algebra sig m => Algebra (MultiUpdate k v :+: sig) (MultiUpdateC k v m) where
--   alg hdl sig ctx = MultiUpdateC \p g s -> case sig of
--     L (MultiGet k) -> do
--       v' <- g k
--       p $ ctx $> v'
--     L (MultiSet k v) -> do
--       s k v
--       p ctx
--     R other -> thread (dst ~<~ hdl) other (pure @(MultiUpdateC k v Identity) ctx) >>= _

-- dst :: MultiUpdateC k v Identity (MultiUpdateC k v m x1) -> m (MultiUpdateC k v Identity x1)
-- dst = _
  

-- mkStateGraph 

-- sal :: GearTemplate' UserId (StateGraph UserId )

testSuite :: [Event]
testSuite =
  [ (AdminSetAccessLevel (e 0) (e 1) SalModerator)
  , (AdminSetAccessLevel (e 1) (e 1) SalAdmin)
  , (AdminSetAccessLevel (e 0) (e 2) SalAdmin)
  ]
  where e = EventId (Timestamp 0) . LocalId
