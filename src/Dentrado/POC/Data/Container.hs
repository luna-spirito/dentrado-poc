module Dentrado.POC.Data.Container where

import RIO hiding (mask, toList, catch)
import System.IO.Unsafe (unsafePerformIO)
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

class Cast a b where -- better to use lib function
  cast :: a -> b

data Res a = Res !Word64 !a -- identified resource

alloc :: Has Fresh sig m => a -> m (Res a)
alloc v = (\i -> Res (fromIntegral i) v) <$> fresh

fetch :: Has Fresh sig m => Res a -> m a
fetch (Res _ x) = pure x -- temp

tryFetch :: Res a -> Maybe a
tryFetch (Res _ a) = Just a

newtype Reduced' (s :: Symbol) = Reduced' Bool
  deriving (Semigroup, Monoid) via Any
type Reduced = Reduced' ""

class Container t where
  wrap :: Res a -> t a
  unwrap' :: Has (Fresh :+: Writer (Reduced' s)) sig m => Proxy s -> t a -> m (Res a)
  tryUnwrap :: t a -> Maybe (Res a)
  same :: t a -> t b -> Bool

allocC :: (Container t, Has Fresh sig m) => p -> m (t p)
allocC x = wrap <$> alloc x

unwrap :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => c a -> m (Res a)
unwrap = unwrap' $ Proxy @""

tryFetchC :: Container c => c a -> Maybe a
tryFetchC c = tryUnwrap c >>= \(Res _ x) -> Just x -- temp

fetchC' :: (Container c, Has (Fresh :+: Writer (Reduced' s)) sig m) => Proxy s -> c a -> m a
fetchC' proxy x = fetch =<< unwrap' proxy x

fetchC :: (Container c, Has (Fresh :+: Writer Reduced) sig m) => c a -> m a
fetchC = fetchC' (Proxy @"")

instance Container Res where
  wrap = id
  unwrap' _ = pure
  tryUnwrap = Just
  same (Res aId _) (Res bId _) = aId == bId

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

data Delay a where
  DelayFresh :: !(Delay (FreshM (Res a))) -> !(IORef (Maybe (Res a))) -> Delay a
  DelayApp :: !(Delay (Res a -> b)) -> !(Delay a) -> Delay b
  DelayPin :: !(Res a) -> Delay a

delayFresh :: Has (Fresh :+: Writer (Reduced' s)) sig m => Proxy s -> Delay (FreshM (Res a)) -> IORef (Maybe (Res a)) -> m (Res a)
delayFresh (Proxy @s) actM memo = 
  case unsafePerformIO $ readIORef memo of
    Just res -> pure res
    Nothing -> do
      tell (Reduced' @s True)
      FreshM act <- delayVal (Proxy @s) actM
      res <- act
      unsafePerformIO $
        writeIORef memo (Just res) $> pure res

delayApp :: (Container t, Has (Fresh :+: Writer (Reduced' s)) sig m) => Proxy s -> Delay (Res a -> b) -> t a -> m b
delayApp proxy df da = delayVal proxy df <*> unwrap' proxy da

delayVal :: Has (Fresh :+: Writer (Reduced' s)) sig m => Proxy s -> Delay a -> m a
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
sNothing = wrap $ $sRunEvalFresh $ alloc Nothing
