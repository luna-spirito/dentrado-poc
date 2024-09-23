{-# LANGUAGE DeriveFunctor #-}
module Dentrado.POC.Db where

import RIO hiding (asks)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Applicative.Free (Ap, liftAp, runAp_, runAp)
import Control.Effect.Fresh (Fresh)
import Control.Carrier.State.Church (StateC)
import Data.Kind (Type)
import Control.Effect.State (get, put)
import qualified Data.Data as D
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->) (..), Res, ValT (..), Val, M (..), Gear (..), funApp, InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof, builtin, tryFromVal, AppForce (..), Container)
import Dentrado.POC.Types (Any1 (..), Dynamic1 (..), RadixTree, Timestamp (..), EventId, Event (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Carrier.Reader (ReaderC)
import Control.Effect.Reader (asks)
import Control.Carrier.Error.Church (runError)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep)
import Data.Constraint (Dict(..))
import Dentrado.POC.TH (sFreshI)

$(moduleId 3)

-- Slow operation.
confGearFromTemplate :: (Typeable ctx, InferValT ctx, Ser cache, Typeable out) =>
  -- ValT cfg ->
  -- cfg ->
  ValT cache ->
  cache ->
  GearFn ctx out cache ->
  -- GearTemplate ctx out cache cfg ->
  AppIOC (Gear ctx out)
confGearFromTemplate cacheT forkedCache gearFn = do
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

confNewGear :: (Typeable ctx, InferValT ctx, InferValT cfg, InferValT cache, Ser cache, Typeable out) => GearTemplate ctx out cache cfg -> ctx -> AppIOC (Gear ctx out)
confNewGear template@(UnsafeGearTemplate initCache conf _fn) ctx = do
  cfg <- unM $ funApp' inferValT conf (ctx, Nothing)
  confGearFromTemplate inferValT initCache $ GearFn inferValT cfg template

reconfGear :: (Typeable ctx, InferValT ctx, Typeable out) => Gear ctx out -> ctx -> AppIOC (Gear ctx out)
reconfGear (UnsafeGear cacheT@(valSerProof -> Dict) (GearFn cfgT oldCfg template@(UnsafeGearTemplate _ conf _)) oldCacheInd) newCtx = do
  gearsV <- asks envGears
  oldCache <- P.fromJust . fromDynamic . P.fromJust . IMap.lookup oldCacheInd <$> sendAI (readMVar gearsV)
  newCfg <- unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (newCtx, Just oldCfg)
  -- TODO: optimization: early return if oldCfg == newCfg.
  confGearFromTemplate cacheT oldCache $ GearFn cfgT newCfg template

-- Generalized confNewGear and reconfGear
confGear :: (InferValT ctx, InferValT cfg, InferValT cache, Ser cache, Typeable ctx, Typeable out) =>
  GearTemplate ctx out cache cfg -> Maybe (Gear ctx out) -> ctx -> AppIOC (Gear ctx out)
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

data StateGraph k v = StateGraph (RadixTree Res k (RadixTree Res EventId v))

{-
I will start prototyping here and then factor this out

First of all. This is POC. Don't do something stupid and overengineered.
To start, you need to show that Dentrado *can* replicate an existing system
without any over-the-top functionality that Dentrado is meant to offer.
After the initial prototype is ready, that's where you can work on reimplementing
immutability-related functionality and showcasing advantages.

Model: WikiDot

-}

builtinFun :: Has Fresh sig m => (a -> b) -> m (a :-> b)
builtinFun f = FunBuiltin <$> builtin f

builtinFunM :: Has Fresh sig m => (a -> f b) -> m (a :-> M f b)
builtinFunM f = builtinFun (M . f)

builtinUnsafeGearTemplate :: (Has Fresh sig m) => cache -> ((ctx, Maybe cfg) -> AppIOC cfg) -> ((cfg, cache) -> AppIOC (out, cache)) -> m (GearTemplate ctx out cache cfg)
builtinUnsafeGearTemplate cache cfgM fnM = do
  cfg <- builtinFunM cfgM
  fn <- builtinFunM fnM
  pure $ UnsafeGearTemplate cache cfg fn

{-
I believe I'm quite content with how RadixTree is implemented right now,
but:
1) Parallel insert, for the love of god.
I'm afraid it's pain to write in the HS, but hopefully could be made
pretty easily in HVM or something.
...

TODO: RadixZipper -> RadixTreeChurch, which consists
of RadixChunkChurch
-}

events :: GearTemplate
  ()
  (RadixTree Res EventId Event)
  (Int, RadixTree Res EventId Event)
  ()
events = $sFreshI $ builtinUnsafeGearTemplate
  (0, RT.empty @Res) -- processed at the moment
  (\((), _) -> pure ())
  \((), (oldLen, oldRes)) -> do
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

bucket ::
  (Has Fresh sig m, InferValT v, InferValT k, InferValT cache, InferValT cfg, InferValT ctx, Ser cache, Ser v, RT.IsRadixKey k, RT.IsRadixKey bucketK, Container c, Typeable k, Typeable ctx, Typeable bucketK) =>
  (v -> [bucketK]) ->
  GearTemplate ctx (RadixTree Res k v) cache cfg ->
  m (GearTemplate ctx (RadixTree Res bucketK (RadixTree c k v)) (RadixTree Res k v, RadixTree Res bucketK (RadixTree c k v)) (Gear ctx (RadixTree Res k v)))
bucket semaphore inputGearTemplate = builtinUnsafeGearTemplate
  (RT.empty @Res, RT.empty @Res) -- (old input, old index)
  (\(ctx, inputGear) -> confGear inputGearTemplate inputGear ctx)
  \(inputGear, (oldInp, oldBuckets)) -> do
    newInp <- runGear inputGear
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

objsFor :: Event -> [EventId]
objsFor = \case
  Register -> []
  Login reg -> [reg]
  CreateSite login -> [login]
  SetSiteAccessLevel login site usr _lvl -> [login, site, usr]
  CreateArticle login site -> [login, site]
  UpdateArticle login art _ -> [login, art]

  
