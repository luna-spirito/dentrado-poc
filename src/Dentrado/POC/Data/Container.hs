module Dentrado.POC.Data.Container where

import RIO hiding (mask, toList, catch)
import System.IO.Unsafe (unsafePerformIO)
import System.Mem.StableName (StableName, makeStableName, eqStableName)
import Control.Carrier.Empty.Church (runEmpty)
import Control.Effect.Empty (empty)
import Control.Algebra
import Control.Carrier.Writer.Church (runWriter, WriterC)
import Data.Monoid (Any(..))
import GHC.Exts (Symbol)
import Control.Effect.Fresh (Fresh (..))
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
  -- app :: Has (Fresh :+: Writer (Reduced' s1) :+: Writer (Reduced' s2)) sig m => Proxy s1 -> Proxy s2 -> t (a -> b) -> t a -> m (t b) -- VERY general interface
  -- -- operations on Ptr can cause extraction (and therefore reduction). Also, computed value needs to be placed into a new Ptr.
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
  -- app _ _ f a = pure $ f <*> a
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
  -- app _p1 _p2 fM aM = construct $ extractDPtr fM $ extractDPtr aM
  same (DPtr i1 _) (DPtr i2 _) = i1 == i2

type Ptr a = DPtr a -- in actual implementation, Ptr could be unloaded

-- to combat impredicativity
newtype FreshM a = FreshM { unFreshM :: forall sig m. Has Fresh sig m => m a }

instance Functor FreshM where
  fmap f (FreshM x) = FreshM $ f <$> x
instance Applicative FreshM where
  pure x = FreshM $ pure x
  (FreshM f) <*> (FreshM a) = FreshM $ f <*> a
instance Monad FreshM where
  (FreshM a) >>= f = FreshM $ a >>= \a' ->
    let (FreshM res) = f a' in res 
instance Algebra Fresh FreshM where
  alg _ Fresh ctx = FreshM ((ctx $>) <$> send Fresh)

data Extracted c a = Extracted !(c a) !a

-- TODO: Question about optimal evaluation. While the result of evaluation should be shared, "extraction" for
-- each individual copy should happen separately, with each copy causing parent to reduce.
-- I believe this approach requires stronger work about linearity & explicit duplication.
-- IDEA: currently, memoization is done at the level of Application.
-- however, most of the time, what's problematic for performance is DB operations.
-- So probably we create a new constructor to support executing DB operations and tie memoization to it.
data Delay a where
  DelayFresh :: !(Delay (FreshM a)) -> !(IORef (Maybe (DPtr a))) -> Delay a
  DelayApp :: !(Delay (Extracted Delay a -> b)) -> !(Delay a) -> Delay b
  -- DelayConst :: (Typeable a, Eq a) => !a -> Delay a -- probably needs to be moved to DPtr
  DelayPin :: DPtr a -> Delay a

delayFresh :: Delay (FreshM a) -> Delay a
delayFresh x = DelayFresh x $ unsafePerformIO $ newIORef Nothing

instance Container Delay where
  construct val = DelayPin <$> construct val
  -- app _p1 _p2 a b = pure $ DelayApp a b $ unsafePerformIO $ newIORef Nothing
  extract' (Proxy @s) = \case
    DelayPin x -> extract' (Proxy @s) x
    -- DelayConst x -> pure x
    DelayFresh actM memo ->
      case unsafePerformIO $ readIORef memo of
        Just res -> pure $ extractDPtr res
        Nothing -> do
          tell (Reduced' @s True)
          FreshM act <- extract' (Proxy @s) actM
          res <- act
          res' <- construct res
          unsafePerformIO $
            writeIORef memo (Just res') $> pure res
    DelayApp df da -> -- TODO: does not emit Reduced', since it's unlikely to need being cached? disallows to make tryExtract on DelayApp.
      censor @(Reduced' s) (const mempty) $ extract' (Proxy @s) df <*> (Extracted da <$> extract' (Proxy @s) da)
  tryExtract = \case
    DelayPin x -> tryExtract x
    -- DelayConst x -> Just x
    DelayFresh _actM memo -> extractDPtr <$> unsafePerformIO (readIORef memo)
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

nonRe' :: forall s m a. Applicative m => WriterC (Reduced' s) m a -> m a
nonRe' = runWriter (\_ -> pure)

-- Perform operation that can't really cause reduction of anything
-- TODO: implement custom Identity-like monad? Although this alters the behaviour.
--  UPD: no, absolutely don't do that. Like e.g. `merge`, it places nonRe at the top level, yet still uses `catch`. Identity breaks `catch`.
--  monad laws are violated as well. Stupid, stupid gard
nonRe :: Applicative m => WriterC Reduced m a -> m a
nonRe = nonRe'

sNothing :: Container c => c (Maybe a)
sNothing = $sRunEvalFresh $ construct Nothing
