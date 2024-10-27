{-# LANGUAGE ApplicativeDo #-}

module Dentrado.POC.Gear where

import Control.Algebra
import Control.Effect.Fresh (Fresh)
import Control.Effect.Reader (asks)
import Data.Constraint (Dict (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import qualified Data.IntMap.Strict as IMap
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Memory (AppForce (..), AppIOC, Container, Env (..), Gear (..), GearFn (..), GearTemplate (..), InferContainerT, InferEValT (..), InferValT (..), M (..), Res, RevList (..), Ser, SerializedGearFn (..), ValT (..), builtinFunM, funApp', sendAI, tryFromVal, tryLazy, unstableSerialized, valSerProof)
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (Event (..), EventId (..))
import RIO hiding (asks, runReader, toList)
import qualified RIO.Partial as P
import Type.Reflection (pattern TypeRep)

$(moduleId 3)

-- | Type alias for GearTemplate.
data GearTemplate' ctx out = ∀ cache cfg. GearTemplate' !(ValT cfg) !(ValT cache) !(GearTemplate ctx out cache cfg)

{- | Internal function. Construct GearFn from a Gear.
TODO: Separate current inputs from AppIOC into a separate monad.
TODO: USE RES FOR GEARS!!!
Slow operation.
-}
gearFromFn ∷
  (Typeable ctx, InferValT ctx, Ser cache, Typeable out) ⇒
  ValT cache →
  cache →
  GearFn ctx out cache →
  AppIOC (Gear ctx out)
gearFromFn cacheT forkedCache gearFn = do
  serGearFn ← SerializedGearFn <$> unstableSerialized gearFn
  gearsFnIndexV ← asks envGearsIndex
  cache ← tryLazy gearsFnIndexV \gearsFnIndex →
    RT.upsertChurch (RT.selEq serGearFn) gearsFnIndex <&> \case
      (Just exGearFn, _) → Left exGearFn
      (Nothing, ins) → Right do
        frV ← asks envFreshInd
        ind ← atomicModifyIORef' frV \old → (old + 1, old)
        gearsV ← asks envGears
        modifyMVar_ gearsV $ pure . IMap.insert ind (Dynamic TypeRep forkedCache)
        (,ind) <$> ins ind
  pure $ UnsafeGear cacheT gearFn cache

-- | Configure new Gear from a GearTemplate' by providing the context.
confNewGear ∷ (Typeable ctx, InferValT ctx {-InferValT cfg, InferValT cache, Ser cache,-}, Typeable out) ⇒ GearTemplate' ctx out → ctx → AppIOC (Gear ctx out)
confNewGear (GearTemplate' cfgT cacheT@(valSerProof → Dict) template@(UnsafeGearTemplate initCache conf _fn)) ctx = do
  cfg ← unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (ctx, Nothing)
  gearFromFn cacheT initCache $ GearFn cfgT cfg template

-- | Reconfigure the Gear by providing new context. Attempts to transfer the old cache to the new Gear.
reconfGear ∷ (Typeable ctx, InferValT ctx, Typeable out) ⇒ Gear ctx out → ctx → AppIOC (Gear ctx out)
reconfGear (UnsafeGear cacheT@(valSerProof → Dict) (GearFn cfgT oldCfg template@(UnsafeGearTemplate _ conf _)) oldCacheInd) newCtx = do
  gearsV ← asks envGears
  oldCache ← P.fromJust . fromDynamic . P.fromJust . IMap.lookup oldCacheInd <$> sendAI (readMVar gearsV)
  newCfg ← unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (newCtx, Just oldCfg)
  -- TODO: optimization: early return if oldCfg == newCfg.
  gearFromFn cacheT oldCache $ GearFn cfgT newCfg template

-- | Generalized confNewGear and reconfGear
confGear ∷
  (InferValT ctx {-InferValT cfg, InferValT cache, Ser cache,-}, Typeable ctx, Typeable out) ⇒
  GearTemplate' ctx out →
  Maybe (Gear ctx out) →
  ctx →
  AppIOC (Gear ctx out)
confGear template exGearM ctx = case exGearM of
  Nothing → confNewGear template ctx
  Just exGear → reconfGear exGear ctx
{-# INLINEABLE confGear #-}

-- | Run configured Gear, returning its result.
runGear ∷ Gear ctx out → AppIOC out
runGear (UnsafeGear cacheT@(valSerProof → Dict) (GearFn cfgT cfg (UnsafeGearTemplate _ _ fn)) cacheInd) = do
  gearsV ← asks envGears
  oldCache ← P.fromJust . fromDynamic . P.fromJust . IMap.lookup cacheInd <$> sendAI (readMVar gearsV)
  (out, newCache) ← unM $ funApp' (ValTTuple cfgT cacheT) fn (cfg, oldCache)
  sendAI $ modifyMVar_ gearsV \gears → pure $ IMap.insert cacheInd (Dynamic TypeRep newCache) gears -- TODO: better merging mechanisms to avoid rewrites
  pure out

-- | Make a GearTemplate out of static Haskell functions.
builtinGearTemplate' ∷ (Has Fresh sig m) ⇒ ValT cfg → ValT cache → cache → ((ctx, Maybe cfg) → AppIOC cfg) → ((cfg, cache) → AppIOC (out, cache)) → m (GearTemplate' ctx out)
builtinGearTemplate' cfgT cacheT cache cfgM fnM = do
  cfg ← builtinFunM cfgM
  fn ← builtinFunM fnM
  pure $ GearTemplate' cfgT cacheT $ UnsafeGearTemplate cache cfg fn

{-# INLINEABLE builtinGearTemplate #-}

-- | Make a GearTemplate out of static Haskell functions.
builtinGearTemplate ∷ (Has Fresh sig m, InferValT cfg, InferValT cache) ⇒ cache → ((ctx, Maybe cfg) → AppIOC cfg) → ((cfg, cache) → AppIOC (out, cache)) → m (GearTemplate' ctx out)
builtinGearTemplate = builtinGearTemplate' inferValT inferValT

{- | Abstraction to simplify construction of new Gears.
Asm allows to create new Gears by composition of parts.
-}
data Asm ctx out = ∀ cfg cache. Asm !(ValT cfg) !(ValT cache) !cache !((ctx, Maybe cfg) → AppIOC cfg) !((cfg, cache) → AppIOC (out, cache))

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
    (\(ctx, cfgM) → (,) <$> configure1 (ctx, fst <$> cfgM) <*> configure2 (ctx, snd <$> cfgM))
    \((cfg1, cfg2), (cache1, cache2)) →
      (\(f', rcache1) (a', rcache2) → (f' a', (rcache1, rcache2)))
        <$> fn1 (cfg1, cache1)
        <*> fn2 (cfg2, cache2)
  -- TODO: optimize for Units, removing unnecessary indirection
  {-# INLINE (<*>) #-}

-- | `GearTemplate'`` can be converted into `Asm`. This is analogous to "subscribing" to the result of the Gear.
asmGear ∷ (InferValT a, InferEValT out, Typeable a, Typeable out) ⇒ GearTemplate' a out → Asm a out
asmGear template = Asm (ValTGear inferValT inferEValT) ValTUnit () {-_Unit-} (\(ctx, gearM) → confGear template gearM ctx) \(gear, _) → (,()) <$> runGear gear
{-# INLINEABLE asmGear #-}

-- | Cached computation can be embedded into `Asm`.
asmCached ∷ (InferValT cache) ⇒ cache → Asm ctx (cache → AppIOC (out, cache)) → Asm ctx out
asmCached initial1 (Asm cfgT cacheT initial configure fn) = Asm
  cfgT
  (ValTTuple inferValT cacheT)
  (initial1, initial)
  configure
  \(cfg, (thisCache, otherCache)) → fn (cfg, otherCache) >>= \(fn', outOtherCache) → fmap (,outOtherCache) <$> fn' thisCache

-- | Construct `GearTemplate'` from constant `Asm`.
builtinAsmGearTemplate ∷ (Has Fresh sig m, InferValT ctx, Typeable ctx) ⇒ Asm ctx out → m (GearTemplate' ctx out)
builtinAsmGearTemplate (Asm cfgT cacheT initial configure fn) =
  builtinGearTemplate' cfgT cacheT initial configure fn

{- | Buffered `Asm` computation: returns current result along with the result returned on previous invocation.
Useful to track changes.
-}
buffered ∷ (InferValT out) ⇒ out → Asm ctx out → Asm ctx (out, out)
buffered cache0 outA = asmCached cache0 do
  out ← outA
  pure \old → pure ((old, out), out)
{-# INLINEABLE buffered #-}

-- Sample:

{- | A Gear that accesses envEvents from Dentrado.POC.Memory's Env and collects them into a Radix Tree.
Explicitly does not handle deletion of events: it's assumed that events are never deleted from the log.
If some event needs to be cancelled, this should be another event.
Obviously this is subject to change.
TODO: POC: Temp
-}
events ∷ GearTemplate' () (RT.MapR EventId Event)
events = $sFreshI
  $ builtinAsmGearTemplate
  $ asmCached
    (0, RT.empty @Res)
  $ pure \(oldLen, oldRes) → do
    (UnsafeRevList evs, newLen) ← readMVar =<< asks envEvents
    -- traceM $ "processing " <> tshow (newLen - oldLen)
    newRes ←
      foldM
        ( \rt (t, ev) →
            tryFromVal @Event ev & maybe (pure rt) \v →
              RT.insert (RT.selEq t) v rt
        )
        oldRes
        (take (newLen - oldLen) evs)
    pure (newRes, (newLen, newRes))

-- indexes

-- object or event -based? Both!

{- | Bucket partitioner.
Processes incoming RadixTree, partitioning the key-value pairs into many buckets (also RadixTree's).
TODO: Bad oversimplified implementation. Actual one should maximise use of immutable data structures.
How? Select maximal subtree
-}
bucket ∷
  (RT.IsRadixKey k, RT.IsRadixKey bucketK, Foldable t, InferContainerT c1, InferContainerT c2, InferContainerT c3, InferValT bucketK, InferValT v, InferValT k, InferValT ctx, Ser v, Container c2, Container c3, Container c1, Typeable k, Typeable ctx, Typeable bucketK) ⇒
  Asm ctx (RT.Map c3 k v) →
  (v → t bucketK) →
  Asm ctx (RT.Map c2 bucketK (RT.Map c1 k v))
bucket inputAsm semaphore = asmCached
  (RT.empty, RT.empty) -- (old input, old index)
  $ do
    newInp ← inputAsm
    pure \(oldInp, oldBuckets) → do
      let updBuckets buckets1 (k, vD) =
            let updWith updater v buckets2 =
                  foldM
                    ( \buckets targetBucketK → do
                        (fromMaybe RT.empty → targetBucket, ins) ← RT.upsertChurch (RT.selEq targetBucketK) buckets
                        ins =<< updater v targetBucket
                    )
                    buckets2
                    (semaphore v)
             in RT.hdlMapDiffE
                  (updWith $ const $ RT.delete (RT.selEq k))
                  (updWith $ RT.insert (RT.selEq k))
                  vD
                  buckets1
      newBuckets ←
        foldM
          updBuckets
          oldBuckets
          =<< RT.toListM @Res
          =<< RT.diffId AppForce oldInp newInp
      pure (newBuckets, (newInp, newBuckets))

lookupBucket ∷ (Container c1, Container c2, RT.IsRadixKey k1, Ser v, Typeable k1, Typeable k2) ⇒ k1 → RT.Map c1 k1 (RT.Map c2 k2 v) → AppIOC (RT.Map c2 k2 v)
lookupBucket k1 = fmap (fromMaybe RT.empty) . RT.lookup (RT.selEq k1)
{-# INLINEABLE lookupBucket #-}
