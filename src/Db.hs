module Dentrado.POC.Db where

import RIO hiding (Map, Set)
-- import Dentrado.POC.Data
import qualified RIO.HashSet as HS
import Control.Algebra
import System.Mem.StableName (StableName, makeStableName, hashStableName)
import GHC.IO.Unsafe (unsafePerformIO)
import Data.Hashable (Hashable(..))
import Data.Typeable (cast)
import Control.Applicative.Free.Fast (Ap, runAp_, liftAp, runAp)
import Control.Carrier.Writer.Strict (runWriter)
import Control.Effect.Writer
import Control.Carrier.State.Strict (StateC)
import Control.Carrier.Accum.Strict (AccumC)
import Control.Effect.Accum (add, look)
import qualified RIO.HashMap as HM
import Control.Effect.State (modify, get)
import Data.Kind (Type)
import qualified RIO.Partial as P

{-

-- Желательно всё уместить в StateGraph, чтобы он был монолитным объектом.
-- Это позволит сохранить чистую семантику
-- Так что...
-- 1) Мы или делаем его полностью монолитным, включая в StateGraph информацию о самих данных и зависимостях
-- 2) Мы храним данные о сателлитах всё же отдельно
-- Временное решение: две структры, полная и расширенная
type DepId = Word32
data StateEntry s v = StateEntry !s !(RadixSet (DepId, _)) !v -- signal, dependencies and the final value
data StateGraph k s v = StateGraph !v !(RadixTree k (RadixZipper EventId StateEntry)) -- initial value and updates for each object
newtype StateGraphDeps k = StateGraphDeps (RadixTree DepId (RadixTree EventId (RadixSet k))

stateGraph do
  dep1 <- _
  dep2 <- _
  pure
    (_functionGetsSamplerReturnsV
    , )
  

t-}

-- Gear
data Snapshot e bm m a where
  SnapshotEvents :: Snapshot e bm m e
  SnapshotUnsafeReadGear :: Typeable b => Gear e b -> Snapshot e bm m (b bm)

data DiffEntry v = DiffAdd v | DiffRemove v | DiffUpdate v v
-- newtype MapDiff k v = MapDiff (MapI k (MapDiffEntry v))
-- type SetDiff k = MapDiff k ()

-- instance
-- Three approaches to modeling diffs: 
-- 1) Naive: Map k (Diff v)
-- 2) Two, for added and removed entries.
-- Should be better for performance, but why would we care
-- ...
-- Idea: use 1, but interpret Diff v by specifying "onRemove" and "onAdd" functions.
-- Much less boilerplate

-- data SetUpd a = SetUpd { setUpdAdd :: Set a, setUpdRemove :: Set a }
-- instance Ord a => Semigroup (SetUpd a) where
--   (SetUpd a1 r1) <> (SetUpd a2 r2) = SetUpd ((a1 `Set.difference` r2) <> a2) ((r1 `Set.difference` a2) <> r2)
-- instance Ord a => Monoid (SetUpd a) where
--   mempty = SetUpd mempty mempty

data Gear e b where
  UnsafeGear :: Typeable a
    => (a, SetI (AnyGear e))
    -> (forall sig m. Has (Snapshot e m) sig m => a -> m (a, b m))
    -> (a -> a -> SetDiff (AnyGear e))
    -> Gear e b

instance Eq (Gear e b) where
  a == b = a `compare` b == EQ
instance Hashable (Gear e b) where
  salt `hashWithSalt` a = salt `hashWithSalt` hashStableName (stableNameFor a)
instance Ord (Gear e b) where
  a `compare` b = hashStableName (stableNameFor a) `compare` hashStableName (stableNameFor b)

data AnyGear e = forall b. Typeable b => AnyGear (Gear e b)
data AnyValue = forall a. Typeable a => AnyValue a

instance Typeable e => Hashable (AnyGear e) where
  salt `hashWithSalt` (AnyGear g) = salt `hashWithSalt` g
instance Typeable e => Eq (AnyGear e) where
  a == b = a `compare` b == EQ
instance Typeable e => Ord (AnyGear e) where
  (AnyGear a) `compare` (AnyGear b) = hashStableName (stableNameFor a) `compare` hashStableName (stableNameFor b)

-- Gear funs

-- | Make an autonomous gear, i. e. the gear that does not depend on anything
-- probably such a rare case that this function should be removed
autoGear :: (Typeable a, Typeable e) => a -> (forall sig m. Has (Snapshot e m) sig m => a -> m (a, b m)) -> Gear e b
autoGear initialCache f = UnsafeGear (initialCache, mempty) f mempty

-- Assembly

data AssemblyF e m a where
  AssemblyF :: Typeable a => Gear e a -> AssemblyF e m (m (a m))
type Assembly e m = Ap (AssemblyF e m)

gearToAsm :: Typeable a => Gear e a -> Assembly e m (m (a m))
gearToAsm gear = liftAp (AssemblyF gear)

withCache :: forall sig2 m2 a b e. (Typeable a, Typeable b, Typeable e) =>
  a -> (forall sig m. Has (Snapshot e m) sig m => Assembly e m (a -> m (a, b m)))
  -> Has (Snapshot e m2) sig2 m2 => Assembly e m2 (m2 (b m2))
withCache initialCache f = gearToAsm $ UnsafeGear
  (initialCache, runAp_ (\(AssemblyF gear) -> Set.singleton $ AnyGear gear) $ f @sig2 @m2)
  (run (runAp (\(AssemblyF gear) -> pure (send (SnapshotUnsafeReadGear gear))) f))
  mempty

-- mToAsm :: (Typeable b, Typeable e) => (forall sig m. Has (Snapshot e m) sig m => m b) -> forall m. Functor m => Assembly e m (m b)
-- mToAsm f = (getConst <$>) <$> gearToAsm (autoGear () (\() -> (\x -> ((), Const x)) <$> f))


-- Db

newtype DbC e m a = DbC { runDbC :: AccumC e (StateC (HashMap (AnyGear e) (Int, Maybe AnyValue)) m) a }
  deriving (Functor, Applicative, Monad)

data Db e (m :: Type -> Type) a where
  DbAddEvent :: e -> Db e m ()
  DbPin :: Typeable b => Gear e b -> Db e m ()

instance (Typeable e, Monoid e, Algebra sig m) => Algebra (Db e :+: Snapshot e (DbC e m) :+: sig) (DbC e m) where
  alg hdl sig ctx = case sig of
    L (DbAddEvent e) -> DbC (add e $> ctx)
    L (DbPin gear) -> updPins gear (+1) $> ctx
    R (L SnapshotEvents) -> DbC $ (ctx $>) <$> look
    R (L (SnapshotUnsafeReadGear gear@(UnsafeGear @a (initialCache, initialPins) upd calculatePinsUpd))) -> do
      store <- DbC $ get @(HashMap (AnyGear e) (Int, Maybe AnyValue))
      let (oldCache, pinsUpdBase) = case HM.lookup (AnyGear gear) store of
            Just (_, x) -> (P.fromJust $ cast x, mempty)
            Nothing -> (initialCache, MapDiff $ Map.fromSet (const $ MapDiffAdd ()) initialPins)
      (newCache, val) <- upd @_ @_ oldCache
      let pinsUpd = pinsUpdBase <> calculatePinsUpd oldCache newCache
      DbC $ modify @(HashMap (AnyGear e) (Int, Maybe AnyValue))
        let
          updateCache = HM.alter (updCacheCell $ fmap \_ -> Just $ AnyValue newCache) (AnyGear gear)
          -- updatePinned gears f x = foldl' (flip $ HM.alter f) x gears
          updatePinned = _
         in _ . updateCache
      --      updatePinned (setUpdRemove pinsUpd) ((\(pins, cache) -> if pins <= 0
      --          then error "Unpinning non-pinned gear"
      --          else
      --            if pins == 1
      --              then Nothing
      --              else Just (pins-1, cache)
      --        ) . P.fromJust) .
      --      updatePinned (setUpdAdd pinsUpd) (updCacheCell $ first (+1)) .
      --      updateCache
      pure $ ctx $>  val
    R (R sig') -> DbC $ alg (runDbC . hdl) (R $ R sig') ctx
    where
      updCacheCell f = Just . f . fromMaybe (0, Nothing)
      updPins :: Typeable b => Gear e b -> (Int -> Int) -> DbC e m ()
      updPins gear f = DbC $ modify @(HashMap (AnyGear e) (Int, Maybe AnyValue)) (HM.alter (updCacheCell $ first f) (AnyGear gear))

snapshotEvents :: forall e sig m. Has (Snapshot e m) sig m => m e
snapshotEvents = send $ SnapshotEvents @_ @m
