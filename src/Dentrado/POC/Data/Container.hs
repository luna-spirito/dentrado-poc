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
import GHC.Exts (Symbol)
import Control.Effect.Fresh (Fresh)
import Control.Carrier.Fresh.Church (fresh)
import Control.Effect.Writer ( Writer, censor, listen, tell )
import Dentrado.POC.TH (moduleId, sRunEvalFresh)

$(moduleId 0)

newtype Reduced' (s :: Symbol) = Reduced' Bool
  deriving (Semigroup, Monoid) via Any
type Reduced = Reduced' ""

-- | `Contains t` means that:
-- 1) It's possible to construct `t a` from `a`
-- 2) It's possible to `extract` `a` from `t a`
-- 3) It's possible to quickly check if two containers hold the same value,
-- but false negatives are possible
class Container t where
  construct :: Has Fresh sig m => a -> m (t a)
  apl :: Has (Fresh :+: Writer (Reduced' s1) :+: Writer (Reduced' s2)) sig m => Proxy s1 -> Proxy s2 -> t (a -> b) -> t a -> m (t b) -- VERY general interface
  -- operations on Ptr can cause extraction (and therefore reduction). Also, computed value needs to be placed into a new Ptr.
  extract' :: Has (Fresh :+: Writer (Reduced' s)) sig m => Proxy s -> t a -> m a -- extraction uncovers new information, so it can cause reduction,
  -- and this new information sometimes requires registering as well (Delay).
  tryExtract :: t a -> Maybe a
  same :: t a -> t b -> Bool

extract :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => c a -> m a
extract = extract' $ Proxy @""

instance Container Identity where
  construct = pure . Identity
  extract' _ = pure . runIdentity
  tryExtract = Just . runIdentity
  apl _ _ f a = pure $ f <*> a
  same a b = stableNameFor (runIdentity a) `eqStableName` stableNameFor (runIdentity b) where
    stableNameFor :: a -> StableName a
    stableNameFor !x = unsafePerformIO $ makeStableName x

-- ptr, delay

data DPtr a = DPtr !Word64 !a -- dereferenced pointer

extractDPtr :: DPtr a -> a
extractDPtr (DPtr _i a) = a

sameDPtr :: DPtr a -> DPtr b -> Bool
sameDPtr (DPtr i1 _a) (DPtr i2 _b) = i1 == i2

instance Container DPtr where
  construct v = (\i -> DPtr (fromIntegral i) v) <$> fresh
  extract' _ = pure . extractDPtr
  tryExtract = Just . extractDPtr
  apl _p1 _p2 fM aM = construct $ extractDPtr fM $ extractDPtr aM
  same (DPtr i1 _) (DPtr i2 _) = i1 == i2

type Ptr a = DPtr a -- in actual implementation, Ptr could be unloaded

data Delay a where
  DelayAp :: !(Delay (a -> b)) -> !(Delay a) -> !(IORef (Maybe (DPtr b))) -> Delay b
  DelayConst :: (Typeable a, Eq a) => !a -> Delay a
  DelayPin :: DPtr a -> Delay a

-- Containers:
-- 1) Identity — debug
-- 2) Ind — immutable value
-- 3) Delay — builds on top of Ind and introduces quick comparison
instance Container Delay where
  construct val = DelayPin <$> construct val
  apl _p1 _p2 a b = pure $ DelayAp a b $ unsafePerformIO $ newIORef Nothing
  extract' (Proxy @s) = \case
    DelayPin x -> extract' (Proxy @s) x
    DelayConst x -> pure x
    DelayAp df da mv -> do
      case unsafePerformIO $ readIORef mv of
        Just v -> pure $ extractDPtr v
        Nothing -> do
          tell (Reduced' @s True)
          v <- extract' (Proxy @s) df <*> extract' (Proxy @s) da
          v' <- construct v
          unsafePerformIO $
            writeIORef mv (Just v') $> pure v
  tryExtract = \case
    DelayPin x -> tryExtract x
    DelayConst x -> Just x
    DelayAp _ _ mv -> extractDPtr <$> unsafePerformIO (readIORef mv)
  same = curry \case
    (DelayPin a, DelayPin b) -> a `same` b
    (DelayConst @x x, DelayConst @y y) -> maybe False (\Refl -> x == y) $ eqT @x @y
    (DelayAp @a1 df1 da1 mv1, DelayAp @a2 df2 da2 mv2) ->
      unsafePerformIO (runEmpty (pure False) pure do
       v1 <- maybe empty pure =<< readIORef mv1
       v2 <- maybe empty pure =<< readIORef mv2
       pure $ v1 `same` v2)
      || (df1 `same` df2 && da1 `same` da2)
    _nonMatching -> False

-- | Presence of Delay fields in some types interferes with construction of the most optimal spine.
-- Reducible is a potential fix that allows to "reduce" the spine as more Delayed computations
-- are resolved.
newtype Reducible a = Reducible (IORef a)

instance Show a => Show (Reducible a) where
  show = show . readReducible

mkReducible :: a -> Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef
{-# INLINE mkReducible #-}

readReducible :: Reducible a -> a
readReducible (Reducible x) = unsafePerformIO $ readIORef x
{-# INLINE readReducible #-}

catch :: forall w a sig m. (Monoid w, Has (Writer w) sig m) => m a -> m (w, a)
catch x = censor @w (const mempty) $ listen x

reducible' :: Has (Writer (Reduced' s)) sig m => Proxy s -> (a -> m a) -> Reducible a -> (a -> m b) -> m b
reducible' (Proxy @s) reductor (Reducible red) f =
  let originalValue = unsafePerformIO $ readIORef red
  in do
    (Reduced' changed, result) <- catch @(Reduced' s) $ f originalValue
    if changed
      then do
        newValue <- reductor originalValue
        unsafePerformIO $ writeIORef red newValue $> pure result
      else
        pure result
{-# INLINE reducible' #-}

reducible :: Has (Writer Reduced) sig m => (a -> m a) -> Reducible a -> (a -> m b) -> m b
reducible = reducible' (Proxy @"")

-- Perform operation that can't really cause reduction of anything
-- TODO: implement custom Identity-like monad? Although this alters the behaviour.
--  UPD: no, absolutely don't do that. Like e.g. `merge`, it places nonRe at the top level, yet still uses `catch`. Identity breaks `catch`.
--  monad laws are violated as well. Stupid, stupid gard
nonRe :: Applicative m => WriterC Reduced m a -> m a
nonRe = runWriter @Reduced (\_ -> pure)

sNothing :: Container c => c (Maybe a)
sNothing = $sRunEvalFresh $ construct Nothing
