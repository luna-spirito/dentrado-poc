{-# LANGUAGE DefaultSignatures #-}
{-# LANGUAGE QuantifiedConstraints #-}
module Dentrado.POC.Memory where

import RIO hiding (mask, toList, catch, ask, asks, runReader, Reader)
import Control.Algebra
import Dentrado.POC.TH (moduleId, sFreshI)
import Data.Kind (Type)
import Data.Type.Equality (type (~))
import Control.Carrier.Lift
import Control.Carrier.State.Church (StateC)
import GHC.Exts (IsList(..))
import RIO.List (uncons)
import Control.Effect.State (get, put, State)
import qualified GHC.Generics as G
import Type.Reflection (pattern TypeRep, type (:~~:) (..), eqTypeRep)
import Control.Carrier.Writer.Church (WriterC, Writer, runWriter)
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
import Dentrado.POC.Types (Reducible(..), RadixTree, RadixChunk', readReducible, Dynamic1 (..), Any1 (..), Timestamp, Event, EventId, LocalId, SiteAccessLevel)
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

tryLazy :: MonadUnliftIO m => MVar a -> (a -> m (Either b (m (a, b)))) -> m b
tryLazy xV f = do
  xTry <- readMVar xV
  f xTry >>= \case
    Left res -> pure res
    Right _ -> modifyMVar xV \x -> f x >>= \case
      Left res -> pure (x, res)
      Right act -> act

-- Resources

-- res builtin
data ResB a = ResB !Word64 {- no bang -} a
-- res allocated
data ResA a
  = Ser a => ResNew !a -- Ser to serialize, since serialization is a background job
  | ResUnloaded !Word64
  | ResLoaded !Word64 !a
data Res a
  = ResBuiltin !(ResB a)
  | ResAlloc !(MVar (ResA a))

-- Env

newtype EnvLoad = EnvLoad (forall a. Ser a => Word64 -> IO a)
newtype EnvStore = EnvStore (forall a. Ser a => a -> IO Word64)
-- TODO ASAP: replace with RadixTree
data Env = Env
  { envFreshInd :: !(IORef Int) -- POC-only
  , envBuiltins :: !(IntMap Dynamic)
  , envKnown :: !(MVar (IntMap (Weak (Dynamic1 Res)))) -- Resources, known to RAM. May not even be actually loaded.
  -- TODO: contention-free
  , envLoad :: !EnvLoad
  , envStore :: !EnvStore
  -- In the future, we'll need to implement deduplication mechanism.
  -- However, putting deduplicatable entities (those that contain Res)
  -- *as keys* of the RadixTree breaks a lot.
  -- We'll either have to teach the deduplicator handle RadixTree, or
  -- we invent something stupid to make sure that those Res are left alone
  -- and not affected by the deduplicator.
  -- For the time being, we'll consider deduplicator a non-existant concept.
  , envGearsIndex :: !(MVar (RadixTree Res SerializedGearFn Int))
  , envGears :: !(MVar (IntMap Dynamic))

  , envEvents :: !(MVar ([(EventId, Any1 Val)], Int))
  }

newtype AppIOC a = AppIOC { unAppIOC :: ReaderC Env IO a }
  deriving (Functor, Applicative, Monad, MonadIO, MonadUnliftIO)
type AppIO = Lift AppIOC :+: Reader Env

instance Algebra AppIO AppIOC where
  alg hdl sig ctx = case sig of
    L (LiftWith f) -> f hdl ctx
    R other -> AppIOC $ alg (unAppIOC . hdl) (inj other) ctx

sendAI :: Has AppIO sig m => AppIOC a -> m a
sendAI = sendM
{-# INLINE sendAI #-}

-- Serialization

-- TODO: Track gears & events & ... & other externals as Obj
data Obj r
  = ObjRes !r
  -- | ObjExt !Word64 !ByteString
  -- I can't handle this at the moment.

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

-- AppIOC needed here because serialization rules could be tred in other Res
type SerM = WriterC Builder AppIOC
type DeserM = StateC ByteString (EmptyC AppIOC)

-- | Serialization class.
-- This class is used to serialize/deserialize objects.
-- Typeable: not required, but I see no reason not to include it here, because this requirement appears everywhere.
class Typeable a => Ser a where
  ser :: a -> WriterC (RevList (Obj (Any1 Res))) SerM ()
  deser :: ConsumeC (Obj Word64) DeserM a

  default ser :: (Generic a, GSer (G.Rep a)) => a -> WriterC (RevList (Obj (Any1 Res))) SerM ()
  ser = gSer . G.from

  default deser :: (Generic a, GSer (G.Rep a)) => ConsumeC (Obj Word64) DeserM a
  deser = G.to <$> gDeser

getInd :: Res a -> AppIOC Word64
getInd = \case
  ResBuiltin (ResB i _) -> pure i
  ResAlloc xV -> do
    EnvStore store <- asks envStore
    sendAI $ tryLazy xV $ pure . \case
      ResUnloaded i -> Left i
      ResLoaded i _ -> Left i
      ResNew o -> Right do
        i <- liftIO $ store o
        pure (ResLoaded i o, i)

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

instance Ser Word64 where
  ser = tell . B.word64BE
  deser = do
    old <- get
    E.guard (B.length old >= 8)
    put $ B.drop 8 old
    return $! (fromIntegral (old `B.unsafeIndex` 0) `unsafeShiftL` 56) .|.
              (fromIntegral (old `B.unsafeIndex` 1) `unsafeShiftL` 48) .|.
              (fromIntegral (old `B.unsafeIndex` 2) `unsafeShiftL` 40) .|.
              (fromIntegral (old `B.unsafeIndex` 3) `unsafeShiftL` 32) .|.
              (fromIntegral (old `B.unsafeIndex` 4) `unsafeShiftL` 24) .|.
              (fromIntegral (old `B.unsafeIndex` 5) `unsafeShiftL` 16) .|.
              (fromIntegral (old `B.unsafeIndex` 6) `unsafeShiftL`  8) .|.
              (fromIntegral (old `B.unsafeIndex` 7) )

-- Hope this won't backfire...
-- TODO: Redo with varint
instance Ser Int where
  ser = ser @Word64 . fromIntegral
  deser = fromIntegral <$> deser @Word64

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
        sendAI $ liftIO $ modifyMVar knownM \oldKnown -> swap <$> getCompose (IMap.alterF (Compose . \existingWeak -> do
            existingM <- maybe (pure Nothing) deRefWeak existingWeak
            case existingM of
              Nothing -> do
                new <- ResAlloc <$> newMVar (ResUnloaded addr)
                (new,) . Just <$> mkWeakPtr (Dynamic1 TypeRep new) (Just cleanupAddr)
              Just (Dynamic1 t2 existing) -> (, existingWeak) <$> do
                Just HRefl <- pure $ eqTypeRep (TypeRep @a) t2 -- TODO-post-POC: invent something to deal with this failure
                pure existing
          ) (fromIntegral addr) oldKnown)

instance Ser Text where
  ser a =
    let encoded = encodeUtf8 a
    in ser (B.length encoded) *> tell (B.byteString encoded)
  deser = do
    l :: Int <- deser
    old <- get
    put $ B.drop l old
    either (const E.empty) pure $ decodeUtf8' $ B.take l old

instance (Ser a, Ser b) => Ser (a, b) where
  ser (a, b) = ser a *> ser b
  deser = (,) <$> deser <*> deser

instance (Container c, Ser a, Typeable c, Typeable k) => Ser (RadixTree c k a)
instance (Container c, Ser a, Typeable c, Typeable k) => Ser (RadixChunk' c k a)

-- POC stuff
instance Ser Timestamp
instance Ser LocalId
instance Ser EventId

instance Ser SiteAccessLevel
instance Ser Event

-- GSer

class GSer (f :: k -> Type) where
  gSer :: f x -> WriterC (RevList (Obj (Any1 Res))) SerM ()
  gDeser :: ConsumeC (Obj Word64) DeserM (f x) -- probably better to encapsulate

class GSerSum (f :: k -> Type) where
  gSerSum :: Int -> f x -> WriterC (RevList (Obj (Any1 Res))) SerM ()
  gDeserSum :: Int -> ConsumeC (Obj Word64) DeserM (f x)

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
gSerSum_ :: forall k (f :: k -> Type) x. GSer f => Int -> f x -> WriterC (RevList (Obj (Any1 Res))) SerM ()
gSerSum_ i v = putWord8 (fromIntegral i) *> gSer v
gDeserSum_ :: forall k (f :: k -> Type) x. GSer f => Int -> ConsumeC (Obj Word64) DeserM (f x)
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
  flag <- sendAI $ newIORef False
  runReader flag act

runReduce :: forall sig m a. Has AppIO sig m => ReduceC m a -> m a
runReduce = runReduce' @""

catchReduce :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> m a -> Reduce'C s AppIOC () -> m a
catchReduce (Proxy @s) act onReduce = do
  flag <- send $ GetReduce' @s
  liftWith @AppIOC \hdl ctx -> do
    let orig `overwriteWith` new = when (orig /= new) $ sendAI $ writeIORef flag new
    outerVal <- sendAI $ readIORef flag
    outerVal `overwriteWith` False
    res <- hdl (ctx $> act)
    innerVal <- sendAI $ readIORef flag
    innerVal `overwriteWith` outerVal
    when innerVal $
      let (Reduce'C redAct) = onReduce
      in runReader flag redAct
    pure res

reduce' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> m ()
reduce' (Proxy @s) = do
  flag <- send $ GetReduce' @s
  sendAI $ writeIORef flag True

instance Ser a => Ser (Reducible a) where
  ser = ser . readReducible
  deser = mkReducible <$> deser

mkReducible :: a -> Reducible a
mkReducible = Reducible . unsafePerformIO . newIORef

reducible' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> (a -> Reduce'C s AppIOC a) -> Reducible a -> (a -> m b) -> m b
reducible' proxy reductor (Reducible red) f = do
  orig <- sendAI $ readIORef red
  catchReduce proxy
    (f orig)
    do
      newValue <- reductor orig
      sendAI $ writeIORef red newValue

reducible :: Has (AppIO :+: Reduce) sig m => (a -> ReduceC AppIOC a) -> Reducible a -> (a -> m b) -> m b
reducible = reducible' (Proxy @"")

-- Values and functions

infixr 1 :->
data a :-> b where
  FunBuiltin :: !(ResB (a -> b)) -> (a :-> b)
  FunCurry :: ((a, b) :-> c) -> (a :-> b :-> c)
  FunCurry1 :: {-no bang-}ValT a -> !a -> !((a, b) :-> c) -> (b :-> c)

-- TODO: maybe unsafes could be cleaned by... uh... Res (c a) ~ Res (Any1 c)?
-- well, implement Res in a way that it allows deserialized data to itself say the type.

-- "Signals" are *exclusively* builtins.
instance (Typeable a, Typeable b) => Ser (a :-> b) where
  ser = \case
    FunBuiltin x -> putWord8 0 *> ser x
    FunCurry f -> case TypeRep @b of
      arr `T.App` TypeRep `T.App` TypeRep
        | Just HRefl <- eqTypeRep arr (TypeRep @(:->))
        -> putWord8 1 *> ser f
      _imp -> error "impossible"
    FunCurry1 xT@(valSerProof -> Dict) x f -> putWord8 2 *> ser (Any1 (Val xT x)) *> ser f
  deser = getWord8 >>= \case
    0 -> FunBuiltin <$> deser
    1 -> case TypeRep @b of
      arr `T.App` TypeRep `T.App` TypeRep
        | Just HRefl <- eqTypeRep arr (TypeRep @(:->))
        -> FunCurry <$> deser
      _err -> empty
    _2 -> do
      Any1 (Val xT@(valSerProof -> Dict) x) <- deser
      FunCurry1 xT x <$> deser

funApp :: InferValT a => a :-> b -> a -> b
funApp = funApp' inferValT

funApp' :: ValT a -> (a :-> b) -> a -> b
funApp' xT f x = case f of
  FunBuiltin (ResB _ f') -> f' x
  FunCurry f' -> FunCurry1 xT x f'
  FunCurry1 aT a f' -> funApp' (ValTTuple aT xT) f' (a, x)

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

--

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

newtype M m a = M { unM :: m a }
newtype C c a = C { unC :: c a }
  deriving Ser

-- ValT is a **runtime** value that stores type of the object.
-- It shouldn't necessarily be GADT, but this is the best way I see to connect it to the Hask type.
data ValT a where
  ValTFun :: !(ValT a) -> !(EValT b) -> ValT (a :-> b)
  ValTTuple :: !(ValT a) -> !(ValT b) -> ValT (a, b)
  ValTRadixTree :: !(ContainerT c) -> !(ValT k) -> !(ValT v) -> ValT (RadixTree c k v)
  ValTContainer :: !(ContainerT c) -> !(ValT a) -> ValT (C c a)
  ValTMaybe :: !(ValT a) -> ValT (Maybe a)
  ValTReducible :: !(ValT a) -> ValT (Reducible a)
  ValTRadixChunk :: !(ContainerT c) -> !(ValT k) -> !(ValT v) -> ValT (RadixChunk' c k v)
  ValTEvent :: ValT Event -- should not be here, but tolerable for POC

-- EValT is an ephemeral extension of ValT. It includes types that
-- cannot be easily serialized.
-- One typical case for EValT to appear is as the right hand of an :-> arrow.
-- This refers to a computation that produces a non-serializable result (like a monad).
data EValT a where
  EValT{-Lift-} :: ValT a -> EValT a
  EValTMonad :: MonadT m -> EValT a -> EValT (M m a)

class InferValT a where
  inferValT :: ValT a
instance (InferValT a, InferEValT b) => InferValT (a :-> b) where
  inferValT = ValTFun inferValT inferEValT
instance (InferValT a, InferValT b) => InferValT (a, b) where
  inferValT = ValTTuple inferValT inferValT
instance (InferContainerT c, InferValT k, InferValT v) => InferValT (RadixTree c k v) where
  inferValT = ValTRadixTree inferContainerT inferValT inferValT
instance (InferContainerT c, InferValT v) => InferValT (C c v) where
  inferValT = ValTContainer inferContainerT inferValT
instance InferValT a => InferValT (Maybe a) where
  inferValT = ValTMaybe inferValT
instance InferValT a => InferValT (Reducible a) where
  inferValT = ValTReducible inferValT
instance (InferContainerT c, InferValT k, InferValT v) => InferValT (RadixChunk' c k v) where
  inferValT = ValTRadixChunk inferContainerT inferValT inferValT
instance InferValT Event where
  inferValT = ValTEvent

class InferEValT a where
  inferEValT :: EValT a
instance {-# OVERLAPPABLE #-} InferValT a => InferEValT a where
  inferEValT = EValT inferValT
instance (InferMonadT m, InferEValT a) => InferEValT (M m a) where
  inferEValT = EValTMonad inferMonadT inferEValT

valSerProof :: ValT x -> Dict (Ser x)
valSerProof = \case
  ValTFun (valSerProof -> Dict) (evalTypeableProof -> Dict) -> Dict
  ValTTuple (valSerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTRadixTree (containerContainerProof -> Dict) (valSerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTContainer (containerContainerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTMaybe (valSerProof -> Dict) -> Dict
  ValTReducible (valSerProof -> Dict) -> Dict
  ValTRadixChunk (containerContainerProof -> Dict) (valSerProof -> Dict) (valSerProof -> Dict) -> Dict
  ValTEvent -> Dict

evalTypeableProof :: EValT x -> Dict (Typeable x)
evalTypeableProof = \case
  EValT (valSerProof -> Dict) -> Dict
  EValTMonad (monadTypeableProof -> Dict) (evalTypeableProof -> Dict) -> Dict

deserValT :: Word8 -> ConsumeC (Obj Word64) DeserM (Any1 ValT)
deserValT = \case
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
  4 -> do
    Any1 a <- deser
    pure $ Any1 $ ValTMaybe a
  5 -> do
    Any1 a <- deser
    pure $ Any1 $ ValTReducible a
  6 -> do
    Any1 c <- deser
    Any1 k <- deser
    Any1 v <- deser
    pure $ Any1 $ ValTRadixChunk c k v
  _7 -> pure $ Any1 $ ValTEvent
  -- >= 150 RESERVED FOR EVAL

instance Ser (Any1 ValT) where
  ser (Any1 x) = case x of
    ValTFun a b -> putWord8 0 *> ser (Any1 a) *> ser (Any1 b)
    ValTTuple a b -> putWord8 1 *> ser (Any1 a) *> ser (Any1 b)
    ValTRadixTree c k v -> putWord8 2 *> ser (Any1 c) *> ser (Any1 k) *> ser (Any1 v)
    ValTContainer c v -> putWord8 3 *> ser (Any1 c) *> ser (Any1 v)
    ValTMaybe a -> putWord8 4 *> ser (Any1 a)
    ValTReducible a -> putWord8 5 *> ser (Any1 a)
    ValTRadixChunk c k v -> putWord8 6 *> ser (Any1 c) *> ser (Any1 k) *> ser (Any1 v)
    ValTEvent -> putWord8 7
    -- >= 150 RESERVED FOR EVal
  deser = getWord8 >>= deserValT

instance Ser (Any1 EValT) where
  ser (Any1 x) = case x of
    EValT a -> ser (Any1 a)
    EValTMonad m a -> putWord8 150 *> ser (Any1 m) *> ser (Any1 a)
  deser = getWord8 >>= \case
    n | n < 150 -> do
      Any1 x <- deser
      pure $ Any1 $ EValT x
    _150 -> do
      Any1 m <- deser
      Any1 a <- deser
      pure $ Any1 $ EValTMonad m a

-- Do we need `a` here?
data Val a = Val !(ValT a) !a
data EVal a = EVal !(EValT a) !a

asVal :: InferValT a => a -> Val a
asVal = Val inferValT

tryFromVal :: forall a. Typeable a => Any1 Val -> Maybe a
tryFromVal (Any1 (Val @b (valSerProof -> Dict) a)) =
  (\HRefl -> a) <$> eqTypeRep (TypeRep @a) (TypeRep @b)

instance Ser (Any1 Val) where
  ser (Any1 (Val t@(valSerProof -> Dict) v)) = ser (Any1 t) *> ser v
  deser = do
    Any1 t@(valSerProof -> Dict) <- deser
    Any1 . Val t <$> deser

-- Container

alloc :: (Has AppIO sig m, Ser a) => a -> m (Res a)
alloc v = ResAlloc <$> sendAI (newMVar $ ResNew v)

fetch :: forall sig m a. (Has AppIO sig m, Ser a) => Res a -> m a
fetch = \case
  ResBuiltin (ResB _ v) -> pure v
  ResAlloc ref -> do
    EnvLoad load <- asks envLoad
    sendAI $ tryLazy ref $ pure . \case
      ResNew v -> Left v
      ResLoaded _ v -> Left v
      ResUnloaded k -> Right do
        v <- liftIO $ load @a k
        pure (ResLoaded k v, v)

tryFetch :: Res a -> Maybe a
tryFetch = \case
  ResBuiltin (ResB _ v) -> Just v
  ResAlloc ref -> case unsafePerformIO $ readMVar ref of
    ResNew v -> Just v
    ResUnloaded _ -> Nothing
    ResLoaded _ v -> Just v

class (forall a. Typeable a => Ser (t a), Typeable t) => Container t where
  wrap :: Res a -> t a
  unwrap' :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> t a -> m (Res a)
  tryUnwrap :: t a -> Maybe (Res a)
  same :: t a -> t b -> Bool -- may have false negatives. `same a b = False` is a lawful implementation

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
  DelayCache :: !(DelayApp (M AppIOC (C Res a))) -> !(IORef (Maybe (Res a))) -> Delay a -- TODO: when some Delay is duplicated into `a` and `b`,

data DelayApp a where
  DelayAppUnsafeFun :: !(Res (Any1 Val)) {- typeOf val ~ a -} -> DelayApp a
  DelayApp :: !(DelayApp (C Res a :-> b)) -> !(Delay a) -> DelayApp b -- we could store (DelayApp a) as the second argument, but I believe this interface is good enough

mkDelayCache :: Has AppIO sig m => DelayApp (M AppIOC (C Res a)) -> m (Delay a)
mkDelayCache x = DelayCache x <$> sendAI (newIORef Nothing)

delayCache :: Has (AppIO :+: Reduce' s) sig m => Proxy s -> DelayApp (M AppIOC (C Res a)) -> IORef (Maybe (Res a)) -> m (Res a)
delayCache (Proxy @s) actM memo =
  sendAI (readIORef memo) >>= \case
    Just res -> pure res
    Nothing -> do
      reduce' (Proxy @s)
      M act <- delayAppVal (Proxy @s) actM
      C res <- sendM act
      sendAI $ writeIORef memo (Just res)
      pure res

withUnsafeEq :: forall a b x. (a ~ b => x) -> x
withUnsafeEq = withDict (unsafeCoerce @() @(Dict (a ~ b)) ())

delayAppVal :: forall sig m s x. Has (AppIO :+: Reduce' s) sig m => Proxy s -> DelayApp x -> m x
delayAppVal proxy = fmap (\(EVal _ x) -> x) . delayAppVal' where
  delayAppVal' :: forall y. DelayApp y -> m (EVal y)
  delayAppVal' = \case
    DelayAppUnsafeFun f -> do
      Any1 @_ @a (Val vT v) <- fetchC' proxy f
      pure $ withUnsafeEq @a @y $ EVal (EValT vT) v
    DelayApp (f :: DelayApp (C Res a :-> y)) a -> delayAppVal' f >>= \case
      EVal (EValT (ValTFun aT@(valSerProof -> Dict) bT)) f' ->
        EVal bT . funApp' aT f' . C <$> unwrap' proxy a

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
    _1 -> DelayCache <$> deser <*> sendAI (newIORef Nothing)

instance Typeable a => Ser (DelayApp a) where -- Actually, this task is mostly about serializing ust a list of [Res], which is already a thing.
-- we could use some manipulations to cut costs and reuse existing functionality.
  ser = void . ser' 0 where
    ser' :: forall b. Word8 -> DelayApp b -> WriterC (RevList (Obj (Any1 Res))) SerM (EValT b)
    ser' args = \case
      DelayAppUnsafeFun f -> do
        putWord8 args *> ser f
        Any1 @_ @c (Val valT _) <- fetch f
        pure $ withUnsafeEq @b @c $ EValT valT
      DelayApp f a -> ser' (args + 1) f >>= \case
        EValT (ValTFun (ValTContainer ContainerTRes (valSerProof -> Dict)) bT) -> ser a $> bT
  deser = do
      args <- getWord8
      valR <- deser
      Any1 (Val valT _) <- fetch valR
      deser' args (DelayAppUnsafeFun valR) $ EValT valT
    where
      deser' :: forall a1. Word8 -> DelayApp a1 -> EValT a1 -> ConsumeC (Obj Word64) DeserM (DelayApp a)
      deser' 0 d (evalTypeableProof -> Dict) = do
        HRefl <- maybe empty pure $ eqTypeRep (TypeRep @a1) (TypeRep @a)
        pure d
      deser' args d (EValT (ValTFun (ValTContainer ContainerTRes (valSerProof -> Dict)) bT)) = do
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

delayAppBuiltinFun :: (Has Fresh sig m, InferValT a) => a -> m (DelayApp a)
delayAppBuiltinFun x = DelayAppUnsafeFun . ResBuiltin <$> builtin (Any1 $ asVal x)

-- Gears (I don't like that it's here)

-- | A template of the Gear, which can be instantiated into GearFn.
data GearTemplate ctx (out :: Type) cache cfg = UnsafeGearTemplate !cache !((ctx, Maybe cfg) :-> M AppIOC cfg) !((cfg, cache) :-> M AppIOC (out, cache))
  deriving Generic
-- | GearFn, an instantiated GearTemplate that only needs `cache` as input.
data GearFn ctx out cache = forall cfg. GearFn !(ValT cfg) !cfg !(GearTemplate ctx out cache cfg)
-- | Gear, a GearFn paired with a reference to the `cache` storage.
data Gear ctx out = forall cache. UnsafeGear !(ValT cache) !(GearFn ctx out cache) !Int

-- An object in it's serialized form. Padded to Chunk size.
newtype Serialized a = UnsafeSerialized ByteString

-- "unstable" in a sense that serializing an object twice
-- does not necessarily yield the same result.
-- TODO: dedup, this doesn't work with dedup, at all.
unstableSerialized :: Ser a => a -> AppIOC (Serialized a)
unstableSerialized x = do
  (val, UnsafeRevList refs) <- runWriter (\a b -> pure (a, b)) $ runWriter (\a _ -> pure a) $ ser x
  refsI <- for refs \(ObjRes (Any1 r)) -> getInd r
  pure $
    let
      unpadded = toStrictBytes $ B.toLazyByteString $ val <> mconcat (B.word64BE <$> refsI)
      padded =
        let finalSegSize = B.length unpadded `mod` 4
        in unpadded <> if finalSegSize == 0 -- yes, I hate myself
          then mempty
          else B.pack $ replicate (4 - finalSegSize) (0 :: Word8)
    in UnsafeSerialized padded

-- Right now I don't have a good idea of how this could be represented generically over both f (GearFn) and number of arguments in Haskell.
data SerializedGearFn = forall ctx out state. SerializedGearFn (Serialized (GearFn ctx out state))

instance (Typeable ctx, Typeable out, Ser state, Typeable cfg) => Ser (GearTemplate ctx out state cfg)
instance (Typeable ctx, Typeable out, Ser state) => Ser (GearFn ctx out state) where
  ser (GearFn cfgT@(valSerProof -> Dict) cfg fn) = ser (Any1 cfgT) *> ser cfg *> ser fn
  deser = do
    Any1 cfgT@(valSerProof -> Dict) <- deser
    GearFn cfgT <$> deser <*> deser
