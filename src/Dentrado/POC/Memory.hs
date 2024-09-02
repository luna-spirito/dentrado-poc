{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE PolyKinds #-}
module Dentrado.POC.Memory where

import RIO hiding (mask, toList, catch, ask, asks, runReader, Reader)
import Control.Algebra
import Dentrado.POC.TH (moduleId, sFreshI)
import Data.Kind (Type)
import Control.Carrier.Lift
import Control.Carrier.State.Church (StateC)
import GHC.Exts (IsList(..))
import RIO.List (uncons)
import Control.Effect.State (get, put, State)
import qualified GHC.Generics as G
import Type.Reflection (TypeRep, pattern TypeRep, type (:~~:) (..), eqTypeRep)
import Control.Carrier.Writer.Church (WriterC, Writer)
import qualified Data.ByteString.Builder as B
import Control.Effect.Writer (tell)
import Control.Carrier.Empty.Church (EmptyC, runEmpty)
import qualified Data.ByteString as B
import Control.Effect.Empty (Empty, empty)
import qualified Control.Effect.Empty as E
import Control.Carrier.Reader (ReaderC, asks, runReader)
import System.Mem.Weak (Weak, deRefWeak, mkWeakPtr)
import Data.Tuple (swap)
import Data.Functor.Compose (Compose(..))
import GHC.Base (Symbol)
import Control.Effect.Reader (ask, Reader)
import System.IO.Unsafe (unsafePerformIO)
import Data.Dynamic (Dynamic, fromDynamic)
import Data.Bits (finiteBitSize, unsafeShiftR, (.|.), unsafeShiftL)
import qualified RIO.Partial as P
import qualified Data.IntMap.Strict as IMap
import Control.Effect.Fresh (Fresh (..), fresh)
import Control.Effect.Sum (Member, inj)
import Unsafe.Coerce (unsafeCoerce)
import Data.ByteString.Unsafe as B
import Data.Constraint (Dict(..), withDict)
import Dentrado.POC.Types (Reducible(..), RadixTree, RadixChunk', readReducible)
import qualified Type.Reflection as T

$(moduleId 0)

-- Misc

newtype RevList a = UnsafeRevList [a]

instance Semigroup (RevList a) where
  UnsafeRevList a <> UnsafeRevList b = UnsafeRevList $ b <> a
instance Monoid (RevList a) where
  mempty = []

revSnoc :: RevList a -> a -> RevList a
revSnoc (UnsafeRevList ls) x = UnsafeRevList $ x:ls

revUnsnoc :: RevList a -> Maybe (RevList a, a)
revUnsnoc (UnsafeRevList x) = (\(v, l) -> (UnsafeRevList l, v)) <$> uncons x

instance IsList (RevList a) where
  type Item (RevList a) = a
  fromList ls = UnsafeRevList $ reverse ls
  {-# INLINE fromList #-}
  toList (UnsafeRevList ls) = reverse ls
  {-# INLINE toList #-}

-- TODO: SecureIO instead of IO, a top-level monad that catches IO errors
-- TODO: cleanup funcs
-- harsh truth is, IO operations can only be guaranteely tracked by other IO operations
-- so, to emit and catch Reduced, we need no Writer, but IO.
-- Maybe we could make some abomination of a monad stack (MyIO (Writer ReducedOrWhatever IO)), but I'd fall back to just using Lift IO for now I guess

class Cast a b where -- better to use one from lib. In any case, shouldn't be defined *here*.
  cast :: a -> b
instance Cast a a where
  cast = id

data Dynamic1 f = forall a. Dynamic1 !(Type.Reflection.TypeRep a) !(f a)
data Any1 f = forall a. Any1 !(f a)

-- Resources and storage

-- res builtin
data ResB a = ResB !Word64 {- no bang -} a
-- res allocated
data ResA a
  = Ser a => ResNew !a -- Ser to serialize, since serialization is a background job
  | ResUnloaded !Word64
  | ResLoaded !a
data Res a
  = ResBuiltin !(ResB a) -- ! ommitted so that the resource is lazily loaded.
  | ResAlloc !(MVar (ResA a))

newtype EnvLoad = EnvLoad (forall a. Ser a => Word64 -> IO a)
-- TODO ASAP: replace with RadixTree
data Env = Env
  { envFreshInd :: !(IORef Int)
  , envBuiltins :: !(IntMap Dynamic)
  , envKnown :: !(MVar (IntMap (Weak (Dynamic1 Res)))) -- Resources, known to RAM. May not even be actually loaded.
  , envLoad :: !EnvLoad
  -- , external :: !(MVar (Map Word64 (Map ByteString Res)))
  }

newtype AppIOC a = AppIOC { unAppIOC :: ReaderC Env IO a }
  deriving (Functor, Applicative, Monad)
type AppIO = Fresh :+: Lift AppIOC :+: Reader Env

sendAIO :: Has AppIO sig m => IO a -> m a
sendAIO = sendM . AppIOC . lift
{-# INLINE sendAIO #-}

instance Algebra AppIO AppIOC where
  alg hdl sig ctx = case sig of
    L Fresh -> AppIOC do
      freshInd <- asks envFreshInd
      sendIO $ atomicModifyIORef' freshInd \old -> (old + 1, ctx $> old)
    R (L (LiftWith f)) -> f hdl ctx
    R (R other) -> AppIOC $ alg (unAppIOC . hdl) (inj other) ctx

-- Serialization

data Obj r
  = ObjRes !r
  | ObjExt !Word64 !ByteString

data Consume e (m :: Type -> Type) a where
  Consume :: Consume e m e

consume :: Has (Consume e) sig m => m e
consume = send Consume
{-# INLINE consume #-}

newtype ConsumeC e m a = ConsumeC { unConsumeC :: StateC [e] m a }
  deriving (Functor, Applicative, Monad)

instance (Algebra sig m, Member Empty sig) => Algebra (Consume e :+: sig) (ConsumeC e m) where
  alg hdl sig ctx = ConsumeC case sig of
    L Consume -> do
      oldList <- get
      (x, xs) <- maybe empty pure $ uncons oldList
      put xs
      pure $ ctx $> x
    R other -> alg (unConsumeC . hdl) (R other) ctx

-- | Serialization class.
-- This class is used to serialize/deserialize objects.
class Typeable a => Ser a where -- typeable is probably excessive, but is needed to "simplify" Ser (Res a)
  ser :: a -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) ()
  deser :: ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) a

  default ser :: (Generic a, GSer (G.Rep a)) => a -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) ()
  ser = gSer . G.from

  default deser :: (Generic a, GSer (G.Rep a)) => ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) a
  deser = G.to <$> gDeser

putWord8 :: Has (Writer Builder) sig m => Word8 -> m ()
putWord8 = tell . B.word8

getWord8 :: Has (State ByteString :+: Empty) sig m => m Word8
getWord8 = do
  old <- get
  (x, new) <- maybe empty pure $ B.uncons old
  put new
  pure x

instance Ser Word8 where
  ser = putWord8
  deser = getWord8
instance Ser Word32 where
  ser = tell . B.word32BE
  deser = do
    old <- get
    E.guard (B.length old >= 4)
    put $ B.drop 4 old
    -- https://hackage.haskell.org/package/cereal-0.5.8.3/docs/src/Data.Serialize.Get.html#getWord32be
    pure $
      (fromIntegral @_ @Word32 (old `B.unsafeIndex` 0) `unsafeShiftL` 24) .|.
      (fromIntegral @_ @Word32 (old `B.unsafeIndex` 1) `unsafeShiftL` 16) .|.
      (fromIntegral @_ @Word32 (old `B.unsafeIndex` 2) `unsafeShiftL`  8) .|.
      fromIntegral @_ @Word32 (old `B.unsafeIndex` 3)

instance Ser a => Ser (Maybe a)

instance Typeable a => Ser (ResB a) where
  ser x = tell @(RevList (Obj (Any1 Res))) [ObjRes $ Any1 $ ResBuiltin x]
  deser = do
    addr :: Word64 <- consume >>= \case
      ObjRes addr -> pure addr
      _notRes -> empty
    builtins <- asks envBuiltins
    pure $ ResB addr $ P.fromJust $ fromDynamic $ P.fromJust $ IMap.lookup (fromIntegral addr) builtins -- TODO-post-POC

instance Typeable a => Ser (Res a) where
  ser x = tell @(RevList (Obj (Any1 Res))) [ObjRes $ Any1 x]
  deser = do
    addr :: Word64 <- consume >>= \case
      ObjRes addr -> pure addr
      _notRes -> empty
    if (addr `unsafeShiftR` (finiteBitSize addr - 1)) == 1
      then do
        builtins <- asks envBuiltins
        pure $ ResBuiltin $ ResB addr $ P.fromJust $ fromDynamic $ P.fromJust $ IMap.lookup (fromIntegral addr) builtins -- TODO-post-POC
      else do
        knownM <- asks envKnown
        let cleanupAddr = modifyMVar_ knownM $ IMap.alterF (\val -> do
                alive <- maybe (pure False) (fmap isJust . deRefWeak) val
                pure $ guard alive *> val
              ) (fromIntegral addr)
        sendAIO $ modifyMVar knownM \oldKnown -> swap <$> getCompose (IMap.alterF (Compose . \existingWeak -> do
            existingM <- maybe (pure Nothing) deRefWeak existingWeak
            case existingM of
              Nothing -> do
                new <- ResAlloc <$> newMVar (ResUnloaded addr)
                (new,) . Just <$> mkWeakPtr (Dynamic1 TypeRep new) (Just cleanupAddr)
              Just (Dynamic1 t2 existing) -> (, existingWeak) <$> do
                Just HRefl <- pure $ eqTypeRep (TypeRep @a) t2 -- TODO-post-POC: invent something to deal with this failure
                pure existing

          ) (fromIntegral addr) oldKnown)

instance (Ser a, Ser b) => Ser (a, b) where
  ser (a, b) = ser a *> ser b
  deser = (,) <$> deser <*> deser

instance (Container c, Ser a, Typeable c, Typeable k) => Ser (RadixTree c k a)
instance (Container c, Ser a, Typeable c, Typeable k) => Ser (RadixChunk' c k a)

-- GSer

class GSer (f :: k -> Type) where
  gSer :: f x -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) ()
  gDeser :: ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) (f x) -- probably better to encapsulate

class GSerSum (f :: k -> Type) where
  gSerSum :: Int -> f x -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) ()
  gDeserSum :: Int -> ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) (f x)

class GSumSize (f :: k -> Type) where
  sumSize :: Proxy f -> Int

instance (GSumSize a, GSumSize b) => GSumSize (a G.:+: b) where
  sumSize _ = sumSize (Proxy @a) + sumSize (Proxy @b)
instance GSumSize (a G.:*: b) where
  sumSize _ = 1
instance GSumSize a => GSumSize (G.M1 i c a) where
  sumSize _ = sumSize (Proxy @a)
instance GSumSize (G.K1 i a) where
  sumSize _ = 1
instance GSumSize G.U1 where
  sumSize _ = 1

instance (GSumSize a, GSerSum a, GSerSum b) => GSerSum (a G.:+: b) where
  gSerSum i = \case
    G.L1 l -> gSerSum i l
    G.R1 r -> gSerSum (i + sumSize (Proxy @a)) r
  gDeserSum i = if i >= sumSize (Proxy @a)
    then G.R1 <$> gDeserSum (i - sumSize (Proxy @a))
    else G.L1 <$> gDeserSum i
gSerSum_ :: forall k (f :: k -> Type) x. GSer f => Int -> f x -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) ()
gSerSum_ i v = putWord8 (fromIntegral i) *> gSer v
gDeserSum_ :: forall k (f :: k -> Type) x. GSer f => Int -> ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) (f x)
gDeserSum_ = \case
  0 -> error "invalid fresh"
  _ -> gDeser
instance GSer (a G.:*: b) => GSerSum (a G.:*: b) where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_
instance GSerSum a => GSerSum (G.M1 i c a) where
  gSerSum i = gSerSum i . G.unM1
  gDeserSum i = G.M1 <$> gDeserSum i
instance GSer (G.K1 c a :: k -> Type) => GSerSum (G.K1 c a :: k -> Type) where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_
instance GSerSum G.U1 where
  gSerSum = gSerSum_
  gDeserSum = gDeserSum_

instance GSerSum (a G.:+: b) => GSer (a G.:+: b) where
  gSer = gSerSum 0
  gDeser = do
    i <- getWord8
    gDeserSum (fromIntegral i)
instance (GSer a, GSer b) => GSer (a G.:*: b) where
  gSer (a G.:*: b) = gSer a *> gSer b
  gDeser = do
    i <- getWord8
    gDeserSum (fromIntegral i)
instance GSer a => GSer (G.M1 i c a) where
  gSer = gSer . G.unM1
  gDeser = G.M1 <$> gDeser
instance Ser a => GSer (G.K1 i a) where
  gSer (G.K1 a) = ser a
  gDeser = G.K1 <$> deser
instance GSer G.U1 where
  gSer G.U1 = pure ()
  gDeser = pure G.U1

-- Reduce

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

runReduce' :: forall s sig m a. Has AppIO sig m => Reduce'C s m a -> m a
runReduce' (Reduce'C act) = do
  flag <- sendAIO $ newIORef False
  runReader flag act

runReduce :: forall sig m a. Has AppIO sig m => ReduceC m a -> m a
runReduce = runReduce' @""

catchReduce :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> m a -> Reduce'C s AppIOC () -> m a
catchReduce (Proxy @s) act onReduce = do
  flag <- send $ GetReduce' @s
  liftWith @AppIOC \hdl ctx -> do
    let orig `overwriteWith` new = when (orig /= new) $ sendAIO $ writeIORef flag new
    outerVal <- sendAIO $ readIORef flag
    outerVal `overwriteWith` False
    res <- hdl (ctx $> act)
    innerVal <- sendAIO $ readIORef flag
    innerVal `overwriteWith` outerVal
    when innerVal $
      let (Reduce'C redAct) = onReduce
      in runReader flag redAct
    pure res

reduce' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> m ()
reduce' (Proxy @s) = do
  flag <- send $ GetReduce' @s
  sendAIO $ writeIORef flag True

instance Ser a => Ser (Reducible a) where
  ser = ser . readReducible
  deser = mkReducible <$> deser

mkReducible :: a -> Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef

reducible' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> (a -> Reduce'C s AppIOC a) -> Reducible a -> (a -> m b) -> m b
reducible' proxy reductor (Reducible red) f = do
  orig <- sendAIO $ readIORef red
  catchReduce proxy
    (f orig)
    do
      newValue <- reductor orig
      sendAIO $ writeIORef red newValue

reducible :: Has (AppIO :+: Reduce) sig m => (a -> ReduceC AppIOC a) -> Reducible a -> (a -> m b) -> m b
reducible = reducible' (Proxy @"")

-- Values and functions

infixr 1 :->
data a :-> b where
  FunBuiltin :: !(ResB (a -> b)) -> (a :-> b)
  FunUnsafeSignal :: !(ResB (Any1 (Signaller m a))) -> (i :-> M m a)

data Signaller m r i = Signaller !(ValT i) !(i -> m r)

-- TODO: maybe unsafes could be cleaned by... uh... Res (c a) ~ Res (Any1 c)?
-- well, implement Res in a way that it allows deserialized data to itself say the type.

-- "Signals" are *exclusively* builtins.
data M m r
  = forall i. MUnsafeSignal !(ResB (Any1 (Signaller m r))) !i
  | forall a. MBind !(ValT a) !(M m a) !(a :-> M m r)

instance (Typeable a, Typeable b) => Ser (a :-> b) where
  ser = \case
    FunBuiltin x -> putWord8 0 *> ser x
    FunUnsafeSignal x -> putWord8 1 *> case TypeRep @b of
      _M `T.App` TypeRep `T.App` TypeRep -> ser x
      _imp -> error "impossible"
  deser = getWord8 >>= \case
    0 -> FunBuiltin <$> deser
    _1 -> case TypeRep @b of
      (TypeRep @m_) `T.App` TypeRep `T.App` TypeRep
        | Just HRefl <- eqTypeRep (TypeRep @m_) (TypeRep @M) -> FunUnsafeSignal <$> deser
      _imp -> empty

instance (Typeable m, Typeable a) => Ser (M m a) where
  ser = \case
    MUnsafeSignal @_ @_ @i f@(ResB _ (Any1 @_ @i2 (Signaller (valSerProof -> Dict) _))) i ->
      putWord8 0 *> ser f *> withUnsafeEq @i @i2 (ser i)
    MBind aT@(valSerProof -> Dict) aM f ->
      putWord8 1 *> ser (Any1 aT) *> ser aM *> ser f
  deser = getWord8 >>= \case
    0 -> do
      signaller'@(ResB _ (Any1 @_ @i (Signaller (valSerProof -> Dict) _))) <- deser
      MUnsafeSignal signaller' <$> deser @i
    _1 -> do
      Any1 aT@(valSerProof -> Dict) <- deser
      aM <- deser
      MBind aT aM <$> deser
  
  -- ser = \case
  --   MSignal res@(ResB _ (valSerProof -> Dict, _)) i -> putWord8 0 *> ser res *> ser i
  --   MBind a aT@(valSerProof -> Dict) b -> putWord8 1 *> ser a *> ser (Any1 aT) *> ser b
  -- deser = getWord8 >>= \case
  --   0 -> do
  --     f <- deser
  --     pure $ MSignal f i

funApp :: a :-> b -> a -> b
funApp f x = case f of
  FunBuiltin (ResB _ f') -> f' x
  FunUnsafeSignal f' -> MUnsafeSignal f' x

-- runM :: M m a -> 

--

data MonadT m where
  MonadTAppIOC :: MonadT AppIOC
  MonadTReduceC :: MonadT m -> MonadT (ReduceC m)
  MonadTReduceC1 :: MonadT m -> MonadT (Reduce'C "1" m)
  MonadTReduceC2 :: MonadT m -> MonadT (Reduce'C "2" m)

class InferMonadT m where
  inferMonadT :: MonadT m
instance InferMonadT AppIOC where
  inferMonadT = MonadTAppIOC
instance InferMonadT m => InferMonadT (ReduceC m) where
  inferMonadT = MonadTReduceC inferMonadT
instance InferMonadT m => InferMonadT (Reduce'C "1" m) where
  inferMonadT = MonadTReduceC1 inferMonadT
instance InferMonadT m => InferMonadT (Reduce'C "2" m) where
  inferMonadT = MonadTReduceC2 inferMonadT

instance Ser (Any1 MonadT) where
  ser (Any1 x) = case x of
    MonadTAppIOC -> putWord8 0
    MonadTReduceC y -> putWord8 1 *> ser (Any1 y)
    MonadTReduceC1 y -> putWord8 2 *> ser (Any1 y)
    MonadTReduceC2 y -> putWord8 3 *> ser (Any1 y)
  deser = getWord8 >>= \case
    0 -> pure $ Any1 MonadTAppIOC
    1 -> (\(Any1 x) -> Any1 $ MonadTReduceC x) <$> deser
    2 -> (\(Any1 x) -> Any1 $ MonadTReduceC1 x) <$> deser
    _3 -> (\(Any1 x) -> Any1 $ MonadTReduceC2 x) <$> deser

monadTypeableProof :: MonadT m -> Dict (Typeable m)
monadTypeableProof = \case
  MonadTAppIOC -> Dict
  MonadTReduceC (monadTypeableProof -> Dict) -> Dict
  MonadTReduceC1 (monadTypeableProof -> Dict) -> Dict
  MonadTReduceC2 (monadTypeableProof -> Dict) -> Dict

data ContainerT a where
  ContainerTRes :: ContainerT Res

class InferContainerT a where
  inferContainerT :: ContainerT a
instance InferContainerT Res where
  inferContainerT = ContainerTRes

instance Ser (Any1 ContainerT) where
  ser (Any1 ContainerTRes) = pure ()
  deser = pure $ Any1 ContainerTRes

containerContainerProof :: ContainerT a -> Dict (Container a)
containerContainerProof = \case
  ContainerTRes -> Dict

--

-- ValT is a **runtime** value that stores type of the object.
-- It shouldn't necessarily be GADT, but this is the best way I see to connect it to the Hask type.
data ValT a where
  ValTFun :: !(ValT a) -> !(ValT b) -> ValT (a :-> b)
  ValTTuple :: !(ValT a) -> !(ValT b) -> ValT (a, b)
  ValTRadixTree :: !(ContainerT c) -> !(ValT k) -> !(ValT v) -> ValT (RadixTree c k v)
  ValTContainer :: !(ContainerT c) -> !(ValT a) -> ValT (c a)
  ValTMonad :: !(MonadT m) -> !(ValT a) -> ValT (M m a)

class InferValT a where
  inferValT :: ValT a
instance (InferValT a, InferValT b) => InferValT (a :-> b) where
  inferValT = ValTFun inferValT inferValT
instance (InferValT a, InferValT b) => InferValT (a, b) where
  inferValT = ValTTuple inferValT inferValT
instance (InferContainerT c, InferValT k, InferValT v) => InferValT (RadixTree c k v) where
  inferValT = ValTRadixTree inferContainerT inferValT inferValT
instance (InferContainerT c, InferValT v) => InferValT (c v) where
  inferValT = ValTContainer inferContainerT inferValT
instance (InferMonadT m, InferValT a) => InferValT (M m a) where
  inferValT = ValTMonad inferMonadT inferValT

valSerProof :: ValT x -> Dict (Ser x)
valSerProof = \case
  ValTFun (valSerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTTuple (valSerProof -> Dict) (valSerProof -> Dict) -> Dict--withDict (valSerProof a) (withDict (valSerProof b) Dict)
  ValTRadixTree (containerContainerProof -> Dict) (valSerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTContainer (containerContainerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTMonad (monadTypeableProof -> Dict) (valSerProof -> Dict) -> Dict

instance Ser (Any1 ValT) where -- The payload is the value.
  ser (Any1 x) = case x of
    ValTFun a b -> putWord8 0 *> ser (Any1 a) *> ser (Any1 b)
    ValTTuple a b -> putWord8 1 *> ser (Any1 a) *> ser (Any1 b)
    ValTRadixTree c k v -> putWord8 2 *> ser (Any1 c) *> ser (Any1 k) *> ser (Any1 v)
    ValTContainer c v -> putWord8 3 *> ser (Any1 c) *> ser (Any1 v)
    ValTMonad m a -> putWord8 4 *> ser (Any1 m) *> ser (Any1 a)
  deser = getWord8 >>= \case
    0 -> do
      Any1 a <- deser
      Any1 b <- deser
      pure $ Any1 $ ValTFun a b
    1 -> do
      Any1 a <- deser
      Any1 b <- deser
      pure $ Any1 $ ValTTuple a b
    2 -> do
      Any1 c <- deser
      Any1 k <- deser
      Any1 v <- deser
      pure $ Any1 $ ValTRadixTree c k v
    3 -> do
      Any1 c <- deser
      Any1 v <- deser
      pure $ Any1 $ ValTContainer c v
    _4 -> do
      Any1 m <- deser
      Any1 a <- deser
      pure $ Any1 $ ValTMonad m a

data Val a = Val { getType :: !(ValT a), getVal :: !a }

asVal :: InferValT a => a -> Val a
asVal = Val inferValT

instance Ser (Any1 Val) where
  ser (Any1 (Val t@(valSerProof -> Dict) v)) = ser (Any1 t) *> ser v
  deser = do
    Any1 t@(valSerProof -> Dict) <- deser
    Any1 . Val t <$> deser

-- Container

alloc :: (Has AppIO sig m, Ser a) => a -> m (Res a)
alloc v = ResAlloc <$> sendAIO (newMVar $ ResNew v)

fetch :: forall sig m a. (Has AppIO sig m, Ser a) => Res a -> m a
fetch = \case
  ResBuiltin (ResB _ v) -> pure v
  ResAlloc ref -> do
    EnvLoad load <- asks envLoad
    sendAIO $ modifyMVar ref \res' -> case res' of
      ResNew v -> pure (res', v)
      ResUnloaded k -> do
        v <- load @a k
        pure (ResLoaded v, v)
      ResLoaded v -> pure (res', v)

tryFetch :: Res a -> Maybe a
tryFetch = \case
  ResBuiltin (ResB _ v) -> Just v
  ResAlloc ref -> case unsafePerformIO $ readMVar ref of
    ResNew v -> Just v
    ResUnloaded _ -> Nothing
    ResLoaded v -> Just v

class (forall a. Typeable a => Ser (t a), Typeable t) => Container t where
  wrap :: Res a -> t a
  unwrap' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> t a -> m (Res a)
  tryUnwrap :: t a -> Maybe (Res a)
  same :: t a -> t b -> Bool

allocC :: (Container t, Has AppIO sig m, Ser a) => a -> m (t a)
allocC x = wrap <$> alloc x

unwrap :: (Container c, Has (AppIO :+: Reduce) sig m) => c a -> m (Res a)
unwrap = unwrap' $ Proxy @""

tryFetchC :: Container c => c a -> Maybe a
tryFetchC c = tryUnwrap c >>= tryFetch

fetchC' :: (Container c, Has (AppIO :+: Reduce' s) sig m, Ser a) => Proxy s -> c a -> m a
fetchC' proxy x = fetch =<< unwrap' proxy x

fetchC :: (Container c, Has (AppIO :+: Reduce) sig m, Ser a) => c a -> m a
fetchC = fetchC' (Proxy @"")

instance Container Res where
  wrap = id
  unwrap' _ = pure
  tryUnwrap = Just
  same (ResBuiltin (ResB aId _)) (ResBuiltin (ResB bId _)) = aId == bId
  same (ResAlloc a) (ResAlloc b) = a == unsafeCoerce b
  same _ _ = False
data AppForce = AppForce

data Delay a where
  DelayPin :: !(Res a) -> Delay a
  DelayCache :: !(DelayApp (M AppIOC (Res a))) -> !(IORef (Maybe (Res a))) -> Delay a -- TODO: when some Delay is duplicated into `a` and `b`,

data DelayApp a where
  DelayAppUnsafeFun :: !(Res (Any1 Val)) {- typeOf val ~ a -} -> DelayApp a
  DelayApp :: !(DelayApp (Res a :-> b)) -> !(Delay a) -> DelayApp b -- we could store (DelayApp a) as the second argument, but I believe this interface is good enough

mkDelayCache :: Has AppIO sig m => DelayApp (M AppIOC (Res a)) -> m (Delay a)
mkDelayCache x = DelayCache x <$> sendAIO (newIORef Nothing)

delayCache :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> DelayApp (M AppIOC (Res a)) -> IORef (Maybe (Res a)) -> m (Res a)
delayCache (Proxy @s) actM memo =
  sendAIO (readIORef memo) >>= \case
    Just res -> pure res
    Nothing -> do
      reduce' (Proxy @s)
      act <- delayAppVal (Proxy @s) actM
      res <- sendM act
      sendAIO $ writeIORef memo (Just res)
      pure res

withUnsafeEq :: forall a b x. (a ~ b => x) -> x
withUnsafeEq = withDict (unsafeCoerce @() @(Dict (a ~ b)) ())

delayAppVal :: forall sig m s x. Has (AppIO :+: Reduce' s) sig m => Proxy s -> DelayApp x -> m x
delayAppVal proxy = fmap (\(Val _ x) -> x) . delayAppVal' where
  delayAppVal' :: forall y. DelayApp y -> m (Val y)
  delayAppVal' = \case
    DelayAppUnsafeFun f -> do
      Any1 @_ @a val <- fetchC' proxy f
      pure $ withUnsafeEq @a @y val
    DelayApp (f :: DelayApp (Res a :-> y)) a -> delayAppVal' f >>= \case
      Val (ValTFun (valSerProof -> Dict) bT) f' ->
        Val bT . funApp f' <$> unwrap' proxy a

instance Container Delay where
  wrap = DelayPin
  unwrap' proxy = \case
    DelayPin x -> pure x
    DelayCache actM memo -> delayCache proxy actM memo
  tryUnwrap = \case
    DelayPin x -> Just x
    DelayCache _actM memo -> unsafePerformIO (readIORef memo)
    -- DelayApp _ _  -> Nothing
  same = curry \case
      (DelayPin a, DelayPin b) -> a `same` b
      (DelayCache valM1 memo1, DelayCache valM2 memo2) ->
        unsafePerformIO (runEmpty (pure False) pure do
         m1 <- maybe empty pure =<< readIORef memo1
         m2 <- maybe empty pure =<< readIORef memo2
         pure $ m1 `same` m2)
        || (valM1 `sameDelayApp` valM2)
      _nonMatching -> False
    where
      sameDelayApp :: DelayApp a -> DelayApp b -> Bool
      sameDelayApp = curry \case
        (DelayAppUnsafeFun a, DelayAppUnsafeFun b) -> a `same` b
        (DelayApp df1 da1, DelayApp df2 da2) ->
          df1 `sameDelayApp` df2 && da1 `same` da2
        _nonMatching -> False
data AppDelay = AppDelay

instance Typeable a => Ser (Delay a) where
  ser = \case
    DelayPin a -> putWord8 0 *> ser a
    DelayCache app _memo -> putWord8 1 *> ser app
  deser = getWord8 >>= \case
    0 -> DelayPin <$> deser
    _1 -> DelayCache <$> deser <*> sendAIO (newIORef Nothing)

instance Typeable a => Ser (DelayApp a) where -- Actually, this task is mostly about serializing ust a list of [Res], which is already a thing.
-- we could use some manipulations to cut costs and reuse existing functionality.
  ser = void . ser' 0 where
    ser' :: forall b. Word8 -> DelayApp b -> WriterC (RevList (Obj (Any1 Res))) (WriterC Builder AppIOC) (ValT b)
    ser' args = \case
      DelayAppUnsafeFun f -> do
        putWord8 args *> ser f
        Any1 @_ @c (Val valT _) <- fetch f
        pure $ withUnsafeEq @b @c valT
      DelayApp f a -> ser' (args + 1) f >>= \case
        ValTFun (ValTContainer ContainerTRes (valSerProof -> Dict)) bT -> ser a $> bT
  deser = do
      args <- getWord8
      valR <- deser
      Any1 (Val valT _) <- fetch valR
      deser' args (DelayAppUnsafeFun valR) valT
    where
      deser' :: forall a1. Word8 -> DelayApp a1 -> ValT a1 -> ConsumeC (Obj Word64) (StateC ByteString (EmptyC AppIOC)) (DelayApp a)
      deser' 0 d (valSerProof -> Dict) = do
        HRefl <- maybe empty pure $ eqTypeRep (TypeRep @a1) (TypeRep @a)
        pure d
      deser' args d (ValTFun (ValTContainer ContainerTRes (valSerProof -> Dict)) bT) = do
        a <- deser
        deser' (args - 1) (DelayApp d a) bT
      deser' _args _d _nonFun = empty
  
builtin :: Has Fresh sig m => a -> m (ResB a)
builtin v = do
  i <- fromIntegral <$> fresh
  pure $ assert
    (i `unsafeShiftR` (finiteBitSize i - 1) == 1)
    (ResB i v)

wrapB :: Container c => ResB a -> c a
wrapB = wrap . ResBuiltin

sNothing :: ResB (Maybe a)
sNothing = $sFreshI $ builtin Nothing-- $sFreshI $ builtin Nothing

mkBuiltinSignal :: (Has Fresh sig1 m1, InferValT i) => (i -> m a) -> m1 (i :-> M m a)
mkBuiltinSignal f = FunUnsafeSignal <$> builtin (Any1 $ Signaller inferValT f)

delayAppBuiltinFun :: (Has Fresh sig m, InferValT a) => a -> m (DelayApp a)
delayAppBuiltinFun x = DelayAppUnsafeFun . ResBuiltin <$> builtin (Any1 $ asVal x)
