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
import Dentrado.POC.Memory (AppIOC, (:->), Res, ValT (..), Val, M (..), Gear (..), funApp, InferValT (..), Env (..), unstableSerialized, tryLazy, GearTemplate (..), GearFn (..), SerializedGearFn (..), Ser, sendAI, funApp', valSerProof)
import Dentrado.POC.Types (Any1 (..), Dynamic1 (..))
import Data.Dynamic (Dynamic (..), fromDynamic)
import Control.Carrier.Reader (ReaderC)
import Control.Effect.Reader (asks)
import Control.Carrier.Error.Church (runError)
import qualified Data.IntMap.Strict as IMap
import Type.Reflection (pattern TypeRep)
import Data.Constraint (Dict(..))

$(moduleId 3)

-- Slow operation.
confGear' :: (Typeable ctx, InferValT ctx, Ser cache, Typeable out) =>
  -- ValT cfg ->
  -- cfg ->
  ValT cache ->
  cache ->
  GearFn ctx out cache ->
  -- GearTemplate ctx out cache cfg ->
  AppIOC (Gear ctx out)
confGear' cacheT forkedCache gearFn = do
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
  confGear' inferValT initCache $ GearFn inferValT cfg template

reconfGear :: (Typeable ctx, InferValT ctx, Typeable out) => Gear ctx out -> ctx -> AppIOC (Gear ctx out)
reconfGear (UnsafeGear cacheT@(valSerProof -> Dict) (GearFn cfgT oldCfg template@(UnsafeGearTemplate _ conf _)) oldCacheInd) newCtx = do
  gearsV <- asks envGears
  oldCache <- P.fromJust . fromDynamic . P.fromJust . IMap.lookup oldCacheInd <$> sendAI (readMVar gearsV)
  newCfg <- unM $ funApp' (ValTTuple inferValT (ValTMaybe cfgT)) conf (newCtx, Just oldCfg)
  -- TODO: optimization: early return if oldCfg == newCfg.
  confGear' cacheT oldCache $ GearFn cfgT newCfg template

runGear :: Gear ctx out -> AppIOC out
runGear (UnsafeGear cacheT@(valSerProof -> Dict) (GearFn cfgT cfg (UnsafeGearTemplate _ _ fn)) cacheInd) = do
  gearsV <- asks envGears
  oldCache <- P.fromJust . fromDynamic . P.fromJust . IMap.lookup cacheInd <$> sendAI (readMVar gearsV)
  (out, newCache) <- unM $ funApp' (ValTTuple cfgT cacheT) fn (cfg, oldCache)
  sendAI $ modifyMVar_ gearsV \gears -> pure $ IMap.insert cacheInd (Dynamic TypeRep newCache) gears -- TODO: better merging mechanisms to avoid rewrites
  pure out
  
newtype Timestamp = Timestamp Word32 deriving (Eq, Ord)
-- | Event id, local to the timestamp.
-- 8 highest bits represent id of the source cluster server.
-- 24 lowest bit represent "epoch", monotonic id of event within the source cluster server within the second.
newtype LocalId = LocalId Word32 deriving (Eq, Ord)
-- | Full Event ID
data EventId = EventId !Timestamp !LocalId deriving (Eq, Ord)

instance RT.IsRadixKey EventId where
  toRadixKey (EventId (Timestamp a) (LocalId b)) = [a, b]
  fromRadixKey = \case
    [a, b] -> EventId (Timestamp a) (LocalId b)
    _ -> error "key corrupted"

{-

data Ctx = Ctx { }

asEventTree :: GearBuilder () (RT.MapR EventId Event)

users :: GearBuilder () (RT.MapR EventId Event)
users = UnsafeGearBuilder $ builtin \() -> _


-}
