{-# LANGUAGE ApplicativeDo #-}
module Dentrado.POC.Gear where

import RIO hiding (asks, toList, runReader)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Effect.Fresh (Fresh)
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->) (..), Res, ValT (..), M (..), Gear (..), InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof, builtin, tryFromVal, AppForce (..), Container, InferContainerT, InferEValT (..))
import Dentrado.POC.Types (EventId (..), Event (..), SiteAccessLevel (..), LocalId (..), Timestamp (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Effect.Reader (asks)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep)
import Data.Constraint (Dict(..))
import Dentrado.POC.TH (sFreshI)

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

lookupBucket :: (Container c1, Container c2, RT.IsRadixKey k1, Ser v, Typeable k1, Typeable k2) => k1 -> RT.Map c1 k1 (RT.Map c2 k2 v) -> AppIOC (RT.Map c2 k2 v)
lookupBucket k1 = fmap (fromMaybe RT.empty) . RT.lookup (RT.selEq k1)
{-# INLINE lookupBucket #-}

buffered :: InferValT out => out -> Asm ctx out -> Asm ctx (out, out)
buffered cache0 outA = asmCached cache0 do
  out <- outA
  pure \old -> pure ((old, out), out)
{-# INLINE buffered #-}

-- TODO: Temp
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
