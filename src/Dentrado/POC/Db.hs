{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE ApplicativeDo #-}
module Dentrado.POC.Db where

import RIO hiding (asks, toList)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Effect.Fresh (Fresh)
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->) (..), Res, ValT (..), M (..), Gear (..), InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof, builtin, tryFromVal, AppForce (..), Container, InferContainerT, RevList, ValGear (..), Delay)
import Dentrado.POC.Types (RadixTree, EventId, Event (..), SiteAccessLevel, MapDiffE)
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Effect.Reader (asks)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep, type (:~~:) (..), eqTypeRep)
import Data.Constraint (Dict(..))
import Dentrado.POC.TH (sFreshI)
import Control.Applicative.Free.Final (Ap, runAp_, runAp, liftAp)
import qualified RIO.List as L
import GHC.Exts (IsList(..))
import Control.Carrier.State.Church (evalState, put, get)
import Data.Functor.Compose (Compose(..))

$(moduleId 3)

data GearTemplate' ctx out = forall cache cfg. GearTemplate' !(ValT cfg) !(ValT cache) !(GearTemplate ctx out cache cfg)

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
builtinGearTemplate' :: (Has Fresh sig m, InferValT cache) => ValT cfg -> cache -> ((ctx, Maybe cfg) -> AppIOC cfg) -> ((cfg, cache) -> AppIOC (out, cache)) -> m (GearTemplate' ctx out)
builtinGearTemplate' cfgT cache cfgM fnM = do
  cfg <- builtinFunM cfgM
  fn <- builtinFunM fnM
  pure $ GearTemplate' cfgT inferValT $ UnsafeGearTemplate cache cfg fn
{-# INLINE builtinGearTemplate #-}

builtinGearTemplate :: (Has Fresh sig m, InferValT cfg, InferValT cache) => cache -> ((ctx, Maybe cfg) -> AppIOC cfg) -> ((cfg, cache) -> AppIOC (out, cache)) -> m (GearTemplate' ctx out)
builtinGearTemplate = builtinGearTemplate' inferValT

-- TODO: generalize over monad?
-- TODO: selective?
data AsmF ctx out where
  AsmF :: !(ValT out) -> !(GearTemplate' ctx out) -> AsmF ctx (AppIOC out) -- TODO: `Typeable out` is technical debt, should be removed?
type Asm ctx = Ap (AsmF ctx)

liftAsm :: InferValT out => GearTemplate' ctx out -> Asm ctx (AppIOC out)
liftAsm = liftAp . AsmF inferValT

data UnpackedAsm ctx out = forall cfg. UnpackedAsm !(ValT cfg) !((ctx, Maybe cfg) -> AppIOC cfg) !(cfg -> AppIOC out)

-- still unsafe
-- TODO: replace eqTypeRep with unsafeCast in production?
unpackAsm :: forall ctx out. (InferValT ctx, Typeable ctx) => Asm ctx out -> UnpackedAsm ctx out
unpackAsm asm = UnpackedAsm @_ @_ @[ValGear ctx]
  (ValTList $ ValTValGear inferValT)
  (\(ctx, cfgM) ->
    let
      newInstantiateFs = runAp_
        (\(AsmF @newOut outT@(valSerProof -> Dict) template) -> [\oldCfgM ->
          let oldCfg = oldCfgM <&> \(ValGear @_ @oldOut (valSerProof -> Dict) oldInst) ->
                case eqTypeRep (TypeRep @newOut) (TypeRep @oldOut) of
                  Nothing -> error "impossible"
                  Just HRefl -> oldInst
          in ValGear outT <$> confGear template oldCfg ctx])
        asm
      oldInstantiations :: [Maybe (ValGear ctx)] = maybe (L.repeat Nothing) (Just <$>) cfgM
    in sequenceA $ L.zipWith ($) (toList @(RevList _) newInstantiateFs) oldInstantiations)
  (\cfg -> evalState cfg $ runAp
    (\(AsmF @expectedOut (valSerProof -> Dict) _) ->
      get @[ValGear ctx] >>= \case
        [] -> error "impossible"
        (ValGear @_ @actualOut (valSerProof -> Dict) x:xs) -> put @[ValGear ctx] xs *> pure case eqTypeRep (TypeRep @expectedOut) (TypeRep @actualOut) of
            Nothing -> error "impossible"
            Just HRefl -> runGear x
    )
    asm)
{-# INLINE unpackAsm #-}

builtinAsmGearTemplate :: (Has Fresh sig m, InferValT ctx, Typeable ctx, InferValT cache) => cache -> Asm ctx (cache -> AppIOC (out, cache)) -> m (GearTemplate' ctx out)
builtinAsmGearTemplate initial asm =
  unpackAsm asm & \(UnpackedAsm cfgT configure fn) ->
    builtinGearTemplate' cfgT initial configure \(cfg, cache) -> fn cfg >>= ($ cache)

-- data StateGraph k v = StateGraph (RadixTree Res k (RadixTree Res EventId v))

{-
I will start prototyping here and then factor this out

First of all. This is POC. Don't do something stupid and overengineered.
To start, you need to show that Dentrado *can* replicate an existing system
without any over-the-top functionality that Dentrado is meant to offer.
After the initial prototype is ready, that's where you can work on reimplementing
immutability-related functionality and showcasing advantages.

Model: WikiDot
-}

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

events :: GearTemplate' () (RadixTree Res EventId Event)
events = $sFreshI $ builtinAsmGearTemplate
  (0, RT.empty @Res) -- processed at the moment
  (pure \(oldLen, oldRes) -> do
    (evs, newLen) <- readMVar =<< asks envEvents
    newRes <- foldM
      (\rt (t, ev) ->
      tryFromVal @Event ev & maybe (pure rt) \v ->
        RT.insert (RT.selEq t) v rt)
      oldRes
      (take (newLen - oldLen) evs)
    pure (newRes, (newLen, newRes)))

-- indexes

-- object or event -based? Both!

bucket :: (Has Fresh sig m, RT.IsRadixKey k, RT.IsRadixKey bucketK, Foldable t, InferContainerT c1, InferContainerT c2, InferContainerT c3, InferValT bucketK, InferValT v, InferValT k, InferValT ctx, Ser v, Container c2, Container c3, Container c1, Typeable k, Typeable ctx, Typeable bucketK) =>
  Asm ctx (AppIOC (RadixTree c3 k v)) ->
  (v -> t bucketK) ->
  m (GearTemplate' ctx (RadixTree c2 bucketK (RadixTree c1 k v)))
bucket inputAsm semaphore = builtinAsmGearTemplate
  (RT.empty, RT.empty) -- (old input, old index)
  do
    inputM <- inputAsm
    pure \(oldInp, oldBuckets) -> do
      newInp <- inputM
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

objSemaphore :: Event -> [EventId]
objSemaphore = \case
  Register -> []
  Login reg -> [reg]
  CreateSite login -> [login]
  SetSiteAccessLevel login site usr _lvl -> [login, site, usr]
  CreateMessage login site -> [login, site]
  UpdateMessage login art _ -> [login, art]

typeSemaphore :: Event -> [Word32]
typeSemaphore = pure . \case
  Register -> 0
  Login {} -> 1
  CreateSite {} -> 3
  SetSiteAccessLevel {} -> 4
  CreateMessage {} -> 6
  UpdateMessage {} -> 7

-- Notice: StateGraph updates could modify multiple objects at the same time.
data StateGraphEntry v = EntrySampled | EntryModified v
newtype StateGraph k v = StateGraph (RadixTree Res k (RadixTree Res EventId (StateGraphEntry v)))

type UserId = EventId
type LoginId = EventId

typeToEvents :: GearTemplate' () (RadixTree Res Word32 (RadixTree Res EventId Event))
typeToEvents = $sFreshI $ bucket (liftAsm events) typeSemaphore

lookupBucket :: (Container c1, Container c2, RT.IsRadixKey k1, Ser v, Typeable k1, Typeable k2) => k1 -> RadixTree c1 k1 (RadixTree c2 k2 v) -> AppIOC (RadixTree c2 k2 v)
lookupBucket k1 = fmap (fromMaybe RT.empty) . RT.lookup (RT.selEq k1)
{-# INLINE lookupBucket #-}

-- Not actually needed, but fun.
userToLogins :: GearTemplate' () (RadixTree Res UserId (RadixTree Res LoginId Event))
userToLogins = $sFreshI 
  let loginEvents = (lookupBucket 1 =<<) <$> liftAsm typeToEvents
  in bucket loginEvents \case
    Login user -> [user] :: [EventId]
    _ -> error "impossible"

type SiteId = EventId

-- scan2 :: RadixTree c k v1 -> RadixTree c k v2 -> (RadixTree c k v1 -> k -> v2 -> v) -> AppIOC (RadixTree Delay k v)
-- scan2 = _

-- scanl :: Asm ctx (AppIOC (RadixTree c k v1)) -> Asm ctx (AppIOC (RadixTree c k v2)) -> (k -> v2 -> (k -> Maybe v1) -> vfin) -> Asm ctx (AppIOC (RadixTree Res k (MapDiffE vfin)))
-- scanl leftM treeM f = _

-- eventToDelayedUser :: GearTemplate' () (RadixTree Delay EventId UserId)
-- eventToDelayedUser = _
{-
how could it possibly work?
Well, that's a tough question.
if we're using Res, this is trivial.
However, it's much harder if we don't want to store this prism in the actual memory
(AND I DON'T WANT IT STORED!)

What parts of said tree *do not change*?
* When old events are not modified, the tree is not updated.
* When 

-}

-- PERMISSIONS MUST DEPEND! ON THE USER ASSOCIATED WITH EACH LOGIN
-- permissions :: SiteId -> GearTemplate' () (StateGraph UserId SiteAccessLevel)
-- permissions siteId =
--   let permEvents = getCompose do
--         typeToEvents' <- Compose $ liftAsm typeToEvents
        
--   in stateGraph permEvents _

{-

stateGraph: accepts old radix tree and stategraph as input.


-}

-- stateGraph :: () -> (RadixTree c k evV, StateGraph k v) -> RadixTree c k evV -> AppIOC (StateGraph k v)
-- stateGraph = _

-- permissions :: SiteId -> GearTemplate' () (StateGraph UserId SiteAccessLevel)
-- permissions = _






-- bindDistinct :: RadixTree Res k ev -> (ev -> (UserId, LoginId)) -> RadixTree Res LoginId (RadixTree ) -> RadixTree Res UserId v
-- bindDist

{-

So, uh. We now know all the logins and what user they are associated to.
How, knowing `RadixTree LoginId UserId` pairs and `RadixTree LoginId Event` for each login, how can we construct
`RadixTree EventId Event` for each user?

This tasks sounds oddly familiar.

First of all, let's get all the user's logins by joining objsFor and eventTypeFor.
Then, 

-}
-- loginToUser :: GearTemplate' () (RadixTree Res EventId EventId)
-- loginToUser = $sFreshI $ builtinGearTemplate
--   _
--   _
--   _

-- userActs :: GearTemplate' () (StateGraph UserId Event)
-- userActs = $sFreshI $ builtinGearTemplate
--   _
--   (\((), _) -> _)
--   _
  -- TODO: cutoff

{-

-}

{-
read :: Gear () (RT.RadixTree EventId (EventId, Text, Text)) -- read message: author, title, value
-}


{-
Login system should not consider Login event,
Site system should not consider CreateSite event,
Article system should not consider UpdateArticle event.
Instead, all such systems, in the worst case, could accept
metadata as input, but nothing else.
-}
  
