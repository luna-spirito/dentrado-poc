{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
module Coroutine where
{-# LANGUAGE ApplicativeDo #-}

import RIO
import Control.Algebra
import Data.Kind (Type)
import System.IO (putStrLn)
import Control.Carrier.Lift (sendIO)

-- Stupid and slow coroutine implementation

data FTCQueue m a b where
  Leaf :: (a -> m b) -> FTCQueue m a b
  Node :: FTCQueue m a x -> FTCQueue m x b -> FTCQueue m a b

unconsFTC :: FTCQueue m a b -> ((a -> m b) -> r) -> (forall x. (a -> m x) -> FTCQueue m x b -> r) -> r
unconsFTC (Leaf f)               r _  = r f
unconsFTC (Node (Node f1 f2) f3) r rp = unconsFTC (Node f1 (Node f2 f3)) r rp
unconsFTC (Node (Leaf f) f2)     _ rp = rp f f2

data CoroutineResult signal m a =
  forall s. CoroutineYield (signal s) (FTCQueue (CoroutineC signal m) s a)
  | CoroutineReturn a
newtype CoroutineC signal m a = CoroutineC { unwrapCoroutineC :: m (CoroutineResult signal m a)}

instance Applicative m => Functor (CoroutineResult signal m) where
  fmap f = \case
    CoroutineYield s q -> CoroutineYield s (Node q $ Leaf $ CoroutineC . pure . CoroutineReturn . f)
    CoroutineReturn x -> CoroutineReturn $ f x
instance Applicative m => Functor (CoroutineC signal m) where
  f `fmap` (CoroutineC v) = CoroutineC $ fmap f <$> v

instance Monad m => Applicative (CoroutineC signal m) where
  pure = CoroutineC . pure . CoroutineReturn
  (CoroutineC coroF) <*> coroX = CoroutineC $ coroF >>= \case
    CoroutineReturn f -> fmap f <$> unwrapCoroutineC coroX
    CoroutineYield s f -> pure $ CoroutineYield s $ Node f $ Leaf (<$> coroX)

instance Monad m => Monad (CoroutineC signal m) where
  (CoroutineC coroX) >>= f = CoroutineC $ coroX >>= \case
    CoroutineReturn x -> unwrapCoroutineC $ f x
    CoroutineYield s x -> pure $ CoroutineYield s $ Node x $ Leaf f

data Yield signal (m :: Type -> Type) a where
  Yield :: signal s -> Yield signal m s

instance Algebra sig m => Algebra (Yield signal :+: sig) (CoroutineC signal m) where
  alg hdl sig ctx = CoroutineC $ case sig of
    L (Yield s) -> pure $ CoroutineYield s $ Leaf (pure . (ctx $>))
    R other -> thread (unwrapCoroutineC . join . CoroutineC . pure ~<~ hdl) other (CoroutineReturn ctx)

yield :: Has (Yield signal) sig m => signal s -> m s
yield = send . Yield

innerToCoro :: Monad m => FTCQueue (CoroutineC signal m) a b -> a -> CoroutineC signal m b
innerToCoro q a = CoroutineC $ unconsFTC q
  (\f -> unwrapCoroutineC $ f a)
  (\f q' -> unwrapCoroutineC (f a) >>= \case
    CoroutineReturn x -> unwrapCoroutineC $ innerToCoro q' x
    CoroutineYield s respond -> pure $ CoroutineYield s (Node respond q')
    )

stepCoroutineC :: Monad m => CoroutineC signal m a -> (a -> m r) -> (forall s. signal s -> (s -> CoroutineC signal m a) -> m r) -> m r
stepCoroutineC (CoroutineC x) onRet onYield = x >>= \case
  CoroutineReturn r -> onRet r
  CoroutineYield s n -> onYield s $ innerToCoro n
