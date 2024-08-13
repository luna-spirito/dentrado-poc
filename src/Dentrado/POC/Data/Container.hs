module Dentrado.POC.Data.Container where

import RIO hiding (mask, toList, catch, ask, runReader)
import System.IO.Unsafe (unsafePerformIO)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.Empty (empty)
import Control.Algebra
import GHC.Base (Symbol)
import Control.Effect.Fresh (Fresh (..))
import Control.Carrier.Fresh.Church (fresh)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Reader (ReaderC, runReader)
import Data.Kind (Type)
import Control.Effect.Reader (ask)
import Control.Carrier.Lift

$(moduleId 0)

-- TODO: SecureIO instead of IO, a top-level monad that catches IO errors
-- TODO: cleanup funcs
-- harsh truth is, IO operations can only be guaranteely tracked by other IO operations
-- so, to emit and catch Reduced, we need no Writer, but IO.
-- Maybe we could make some abomination of a monad stack (MyIO (Writer ReducedOrWhatever IO)), but I'd fall back to just using Lift IO for now I guess

globalFreshCounter :: IORef Int
globalFreshCounter = unsafePerformIO $ newIORef 0
{-# NOINLINE globalFreshCounter #-}

-- Top-level monad that combines IO and Fresh, since Fresh is needed for the entire duration of the application and should not backtrack
-- Actually just uses IORef to store Fresh
newtype FreshIOC a = FreshIOC { runFreshIO :: IO a }
  deriving (Functor, Applicative, Monad)

type FreshIO = Lift FreshIOC :+: Fresh

instance Algebra FreshIO FreshIOC where
  alg hdl sig ctx = case sig of
    L (LiftWith l) -> l hdl ctx
    R Fresh -> FreshIOC $ (ctx $>) <$> atomicModifyIORef globalFreshCounter (\old -> (old+1, old))

sendFIO :: Has (Lift FreshIOC) sig m => IO a -> m a
sendFIO = sendM . FreshIOC

data Reduce' (s :: Symbol) (m :: Type -> Type) a where
  GetReduce' :: Reduce' s m (IORef Bool)
newtype Reduce'C (s :: Symbol) m a = Reduce'C (ReaderC (IORef Bool) m a)
  deriving (Functor, Applicative, Monad, MonadTrans)

instance Algebra sig m => Algebra (Reduce' s :+: sig) (Reduce'C s m) where
  alg hdl sig ctx = Reduce'C $ case sig of
    L GetReduce' -> (ctx $>) <$> ask
    R r -> alg ((\(Reduce'C x) -> x) . hdl) (R r) ctx
  {-# INLINE alg #-}
type Reduce = Reduce' ""
type ReduceC = Reduce'C ""

runReduce' :: forall s sig m a. Has FreshIO sig m => Reduce'C s m a -> m a
runReduce' (Reduce'C act) = do
  flag <- sendFIO $ newIORef False
  runReader flag act

runReduce :: forall sig m a. Has FreshIO sig m => ReduceC m a -> m a
runReduce = runReduce' @""

catchReduce :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> m a -> Reduce'C s FreshIOC () -> m a
catchReduce (Proxy @s) act onReduce = do
  flag <- send $ GetReduce' @s
  liftWith @FreshIOC \hdl ctx -> do
    let orig `overwriteWith` new = when (orig /= new) $ FreshIOC $ writeIORef flag new
    outerVal <- FreshIOC $ readIORef flag
    outerVal `overwriteWith` False
    res <- hdl (ctx $> act)
    innerVal <- FreshIOC $ readIORef flag
    innerVal `overwriteWith` outerVal
    when innerVal $
      let (Reduce'C redAct) = onReduce
      in runReader flag redAct
    pure res

reduce' :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> m ()
reduce' (Proxy @s) = do
  flag <- send $ GetReduce' @s
  sendFIO $ writeIORef flag True

----

class Cast a b where -- better to use one from lib. In any case, shouldn't be defined *here*.
  cast :: a -> b
instance Cast a a where
  cast = id

-- TODO: Res (Maybe a) should store variant info at ptr level, not at the data level. Therefore, we'll need
-- some new class that defines how things are packed.
data Res a = Res !Word64 !a -- identified resource, probably requires fetching from the disk
newtype ResPOC a = ResPOC Word64 -- welp, yeah. This declaration will be merged into Res in the final
-- dentrado implementation, but, since POC doesn't have any internal storage and can't fetch resource by some identifier, these types
-- are separate here. For now.
instance Cast (Res a) (ResPOC a) where
  cast (Res p _) = ResPOC p

alloc :: Has Fresh sig m => a -> m (Res a)
alloc v = (\i -> Res (fromIntegral i) v) <$> fresh

fetch :: Has Fresh sig m => Res a -> m a
fetch (Res _ x) = pure x -- temp

tryFetch :: Res a -> Maybe a
tryFetch (Res _ a) = Just a

class Container t where
  wrap :: Res a -> t a
  unwrap' :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> t a -> m (Res a)
  tryUnwrap :: t a -> Maybe (Res a)
  same :: t a -> t b -> Bool

allocC :: (Container t, Has Fresh sig m) => p -> m (t p)
allocC x = wrap <$> alloc x

unwrap :: (Container c, Has (FreshIO :+: Reduce) sig m) => c a -> m (Res a)
unwrap = unwrap' $ Proxy @""

tryFetchC :: Container c => c a -> Maybe a
tryFetchC c = tryUnwrap c >>= \(Res _ x) -> Just x -- temp

fetchC' :: (Container c, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> c a -> m a
fetchC' proxy x = fetch =<< unwrap' proxy x

fetchC :: (Container c, Has (FreshIO :+: Reduce) sig m) => c a -> m a
fetchC = fetchC' (Proxy @"")

instance Container Res where
  wrap = id
  unwrap' _ = pure
  tryUnwrap = Just
  same (Res aId _) (Res bId _) = aId == bId
data AppForce = AppForce

data Delay a where
  DelayFresh :: !(Delay (FreshIOC (Res a))) -> !(IORef (Maybe (Res a))) -> Delay a -- TODO: when some Delay is duplicated into `a` and `b`,
  -- if `a` emits Reduced, `b` should emit Reduced independently, to ensure that reduction happens in both ctxs of `a` and `b`.
  DelayApp :: !(Delay (Res a -> b)) -> !(Delay a) -> Delay b
  DelayPin :: !(Res a) -> Delay a

mkDelayFresh :: (Has FreshIO sig m) => Delay (FreshIOC (Res a)) -> m (Delay a)
mkDelayFresh x = DelayFresh x <$> sendM (FreshIOC $ newIORef Nothing)

delayFresh :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> Delay (FreshIOC (Res a)) -> IORef (Maybe (Res a)) -> m (Res a)
delayFresh (Proxy @s) actM memo =
  sendM (FreshIOC $ readIORef memo) >>= \case
    Just res -> pure res
    Nothing -> do
      reduce' (Proxy @s)
      act <- delayVal (Proxy @s) actM
      res <- sendM act
      sendFIO $ writeIORef memo (Just res)
      pure res

delayApp :: (Container t, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> Delay (Res a -> b) -> t a -> m b
delayApp proxy df da = delayVal proxy df <*> unwrap' proxy da

delayVal :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> Delay a -> m a
delayVal proxy = \case
  DelayFresh a b -> fetch =<< delayFresh proxy a b
  DelayApp df da -> delayApp proxy df da
  DelayPin x -> fetch x

instance Container Delay where
  wrap = DelayPin
  unwrap' proxy = \case
    DelayPin x -> pure x
    DelayFresh actM memo -> delayFresh proxy actM memo
    DelayApp df da -> alloc =<< delayApp proxy df da
  tryUnwrap = \case
    DelayPin x -> Just x
    DelayFresh _actM memo -> unsafePerformIO (readIORef memo)
    DelayApp _ _  -> Nothing
  same = curry \case
    (DelayPin a, DelayPin b) -> a `same` b
    -- (DelayConst @x x, DelayConst @y y) -> maybe False (\Refl -> x == y) $ eqT @x @y
    (DelayFresh valM1 memo1, DelayFresh valM2 memo2) ->
      unsafePerformIO (runEmpty (pure False) pure do
       m1 <- maybe empty pure =<< readIORef memo1
       m2 <- maybe empty pure =<< readIORef memo2
       pure $ m1 `same` m2)
      || (valM1 `same` valM2)
    (DelayApp df1 da1, DelayApp df2 da2) ->
      df1 `same` df2 && da1 `same` da2
    _nonMatching -> False
data AppDelay = AppDelay

-- | Presence of Delay fields in some types interferes with construction of the most optimal spine.
-- Reducible is a potential fix that allows to "reduce" the spine as more Delayed computations
-- are resolved.
newtype Reducible a = Reducible (IORef a)

instance Show a => Show (Reducible a) where
  show = show . readReducible

mkReducible :: a -> Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef

readReducible :: Reducible a -> a
readReducible (Reducible x) = unsafePerformIO $ readIORef x

reducible' :: Has (FreshIO :+: Reduce' s) sig m => Proxy s -> (a -> Reduce'C s FreshIOC a) -> Reducible a -> (a -> m b) -> m b
reducible' proxy reductor (Reducible red) f = do
  orig <- sendFIO $ readIORef red
  catchReduce proxy
    (f orig)
    do
      newValue <- reductor orig
      sendFIO $ writeIORef red newValue

reducible :: Has (FreshIO :+: Reduce) sig m => (a -> ReduceC FreshIOC a) -> Reducible a -> (a -> m b) -> m b
reducible = reducible' (Proxy @"")

sNothing :: Container c => c (Maybe a)
sNothing = wrap $ $sRunEvalFresh $ alloc Nothing
