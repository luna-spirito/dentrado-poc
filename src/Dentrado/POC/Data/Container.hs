module Dentrado.POC.Data.Container where

import RIO hiding (mask, toList, catch)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (StableName, makeStableName, eqStableName)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.Empty (empty)
import Data.Typeable (eqT, type (:~:) (..))
import Control.Algebra
import Control.Carrier.Writer.Church (runWriter, WriterC)
import Data.Monoid (Any(..))
import Control.Effect.Writer

stableNameFor :: a -> StableName a
stableNameFor !x = unsafePerformIO $ makeStableName x

data Delay a where
  DelayAp :: Typeable a => !(Delay (a -> b)) -> !(Delay a) -> !(IORef (Maybe b)) -> Delay b
  DelayPin :: !a -> Delay a

dPure :: a -> Delay a
dPure = DelayPin

dAp :: Typeable a => Delay (a -> b) -> Delay a -> Delay b
dAp a b = DelayAp a b $ unsafePerformIO $ newIORef Nothing

-- | `Contains t` means that:
-- 1) It's possible to construct `t a` from `a`
-- 2) It's possible to `extract` `a` from `t a`
-- 3) It's possible to quickly check if two containers hold the same value,
-- but false negatives are possible
class Container t where
  construct :: a -> t a -- probably `a -> m (t a)`
  extract :: Has (Writer Any) sig m => t a -> m a -- probably `t a -> m a`
  tryExtract :: t a -> Maybe a
  same :: t a -> t b -> Bool

instance Container Identity where
  construct = Identity
  extract = pure . runIdentity
  tryExtract = Just . runIdentity
  same a b = stableNameFor (runIdentity a) `eqStableName` stableNameFor (runIdentity b)

instance Container Delay where
  construct = dPure
  extract = \case
    DelayPin x -> pure x
    DelayAp df da mv -> unsafePerformIO do
      vM <- readIORef mv
      case vM of
        Just v -> pure $ pure v
        Nothing -> do
          let v = run $ runWriter @Any (\_ y -> pure y) $ extract df <*> extract da
          writeIORef mv $ Just v
          pure $ tell (Any True) $> v
  tryExtract = \case
    DelayPin x -> Just x
    DelayAp _ _ mv -> unsafePerformIO $ readIORef mv
  same a b = case (a, b) of
    (DelayPin a', DelayPin b') -> stableNameFor a' `eqStableName` stableNameFor b'
    (DelayAp @a1 df1 da1 mv1, DelayAp @a2 df2 da2 mv2) ->
      unsafePerformIO (runEmpty (pure False) pure do
        v1 <- maybe empty pure =<< readIORef mv1
        v2 <- maybe empty pure =<< readIORef mv2
        pure $ stableNameFor v1 `eqStableName` stableNameFor v2)
      || maybe False (\Refl -> df1 `same` df2 && da1 `same` da2) (eqT @a1 @a2)
    (DelayAp {}, DelayPin _) -> False
    (DelayPin _, DelayAp {}) -> False

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

catch :: forall w a sig m. (Monoid w, Has (Writer w) sig m) => m a -> m (w, a)
catch x = censor @w (const mempty) $ listen x

reducible :: Has (Writer Any) sig m => (a -> m a) -> Reducible a -> (a -> m b) -> m b
reducible reductor (Reducible red) f =
  let originalValue = unsafePerformIO $ readIORef red
  in do
    (Any changed, result) <- catch $ f originalValue
    if changed
      then do
        newValue <- reductor originalValue
        pure $ unsafePerformIO (writeIORef red newValue) `seq` result
      else
        pure result
{-# INLINE reducible #-}

-- Perform operation that can't really cause reduction of anything
nonRe :: WriterC Any Identity a -> a
nonRe = runIdentity . runWriter (\_ -> pure)
