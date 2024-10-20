{-# LANGUAGE RecursiveDo, PatternSynonyms #-}
{-# LANGUAGE ConstraintKinds #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (lookup, Set, Map, mask, toList, catch, runReader, (<|>))
import Data.Bits (countTrailingZeros, (.&.), unsafeShiftR, complement, xor, finiteBitSize, unsafeShiftL, (.|.), countLeadingZeros)
import Control.Algebra
import Data.Foldable (foldrM)
import Dentrado.POC.TH (moduleId, sFreshI)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Monad.Fix (MonadFix)
import Data.Monoid (First(..))
import Control.Effect.NonDet (NonDet)
import Control.Effect.Choose (Choose(..), (<|>))
import qualified Control.Effect.Empty as E
import GHC.Exts (IsList(..))
import Control.Carrier.NonDet.Church (runNonDet, NonDetC (..), runNonDetA)
import Control.Effect.Fresh (Fresh)
import Language.Haskell.TH (Q, Exp, lamE, varE, appE, newName, varP)
import Control.Carrier.Reader (runReader)
import Data.Kind (Type)
import Dentrado.POC.Memory (Res (..), Cast (..), Container (..), AppIO, Reduce' (..), Delay (..), ReduceC, AppIOC, AppForce(..), Reduce, RevList, AppDelay(..), Reduce'C (..), allocC, mkReducible, tryFetchC, reduce', runReduce, fetchC, reducible, revSnoc, sNothing, fetch, unwrap, mkDelayCache, runReduce', alloc, reducible', builtin, Ser, ResB (..), wrapB, (:->) (..), delayAppBuiltinFun, DelayApp (..), M (..), C (..), InferValT, InferContainerT, Serialized (..), SerializedGearFn (..))
import Control.Effect.Writer (tell)
import Dentrado.POC.Types (Chunk, RadixTree (..), RadixChunk, RadixChunk' (..), readReducible, EventId (EventId), Timestamp (..), LocalId (..), MapDiffE (..))
import qualified Data.ByteString as B
import qualified Data.ByteString.Unsafe as B
import qualified Data.ByteString.Builder as B
import qualified RIO.NonEmpty as NE
import Control.Effect.Empty (Empty (..))
import Data.Coerce (coerce)
import Control.Monad.Free (Free (..))
import Data.Functor.Compose (Compose (..))

$(moduleId 1)

-- TODO: path compression for really long unique keys
-- TODO: proper church encoding.

class IsRadixKey key where
  toRadixKey :: key -> [Chunk]
  fromRadixKey :: [Chunk] -> key
  -- LAW: a `compare` b = toRadixKey a `compare` toRadixKey b

instance IsRadixKey [Chunk] where
  toRadixKey = id
  fromRadixKey = id
instance IsRadixKey Chunk where
  toRadixKey = pure
  fromRadixKey = \case
    [x] -> x
    _ -> error "key corrupted"

-- TODO: UNSAFE
-- Deal with it when implementing deduplication
-- instance IsRadixKey ByteString where
instance IsRadixKey (Serialized a) where
  toRadixKey = \(UnsafeSerialized x) -> f x where
    f (B.null -> True) = []
    f b =
      let x =
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 0) `unsafeShiftL` 24) .|.
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 1) `unsafeShiftL` 16) .|.
            (fromIntegral @_ @Word32 (b `B.unsafeIndex` 2) `unsafeShiftL`  8) .|.
            fromIntegral @_ @Word32 (b `B.unsafeIndex` 3)
      in x : f (B.drop 4 b)
  fromRadixKey =
    UnsafeSerialized . toStrictBytes . B.toLazyByteString . mconcat . fmap B.word32BE
instance IsRadixKey (SerializedGearFn) where
  toRadixKey (SerializedGearFn x) = toRadixKey x
  fromRadixKey = SerializedGearFn . fromRadixKey

instance IsRadixKey EventId where
  toRadixKey (EventId (Timestamp a) (LocalId b)) = [a, b]
  fromRadixKey = \case
    [a, b] -> EventId (Timestamp a) (LocalId b)
    _ -> error "key corrupted"

instance IsRadixKey [EventId] where
  toRadixKey = concatMap toRadixKey
  fromRadixKey = \case
    (a:b:xs) -> fromRadixKey @EventId [a, b] : fromRadixKey @[EventId] xs
    [] -> []
    _ -> error "key corrupted"


tryMask :: Chunk -> Chunk -> Maybe Bool
tryMask mask key =
  if prefixBits .&. mask == prefixBits .&. key
  then Just $ 1 .&. (key `unsafeShiftR` countTrailingZeros mask) == 1
  else Nothing
  where
    prefixBits = complement $ mask - 1 `xor` mask
{-# INLINE tryMask #-}

makeMask :: Chunk -> Chunk -> (Chunk, Bool)
makeMask l r =
  let maskBit = unsafeShiftL 1 (finiteBitSize (0 :: Chunk) - 1 - countLeadingZeros (l `xor` r))
  in (maskBit .|. (l .&. complement (maskBit-1)), r .&. maskBit /= 0)

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.


-- aliases

type Map = RadixTree
type MapR = Map Res
type Set = RadixTree
type SetR k = MapR k ()

hdlMapDiffE :: Monad m => (v -> a -> m a) -> (v -> a -> m a) -> MapDiffE v -> a -> m a
hdlMapDiffE onDel onAdd = \case
  MapDel v -> onDel v
  MapUpd v1 v2 -> onAdd v2 <=< onDel v1
  MapAdd v -> onAdd v
{-# INLINE hdlMapDiffE #-}

mkMapDiffE :: Maybe a -> Maybe a -> Maybe (MapDiffE a)
mkMapDiffE a b = case (a, b) of
  (Nothing, Nothing) -> Nothing
  (Nothing, Just b') -> Just $ MapAdd b'
  (Just a', Nothing) -> Just $ MapDel a'
  (Just a', Just b') -> Just $ MapUpd a' b'

data SetDiffE = SetAdd | SetDel

instance Cast (MapDiffE ()) (Maybe SetDiffE) where
  cast = \case
    MapAdd () -> Just SetAdd
    MapUpd () () -> Nothing
    MapDel () -> Just SetDel

sNil :: ResB (RadixChunk c2 k a)
sNil = $sFreshI $ builtin $ mkReducible Nil

-- -- TODO: Don't know how effective is this
reduceChunk'' :: (Container c, Has (AppIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a, Maybe (c (RadixChunk c k a)))
reduceChunk'' (Proxy @s) = \case
  Tip _ (RadixTree (tryFetchC -> Just Nothing) (tryFetchC -> Just (readReducible -> Nil))) -> reduce' (Proxy @s) $> (Nil, Just $ wrapB sNil)
  Bin _ left'@(tryFetchC -> Just (readReducible -> left)) right'@(tryFetchC -> Just (readReducible -> right))
    | Nil <- left -> reduce' (Proxy @s) $> (right, Just right') -- hopefully no need to reduceChunk left/right
    | Nil <- right -> reduce' (Proxy @s) $> (left, Just left')
  nonReducible -> pure (nonReducible, Nothing)
{-# INLINE reduceChunk'' #-}

reduceChunk' :: (Container c, Has (AppIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk' p v = fst <$> reduceChunk'' p v
{-# INLINE reduceChunk' #-}

reduceChunk :: (Container c, Has (AppIO :+: Reduce) sig m) => RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk = reduceChunk' (Proxy @"")
{-# INLINE reduceChunk #-}

allocReducedChunk :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k) => (forall b. c2 b -> ReduceC m (c1 b)) -> RadixChunk' c2 k a -> m (c1 (RadixChunk c2 k a))
allocReducedChunk f c = runReduce $ reduceChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v
{-# INLINE allocReducedChunk #-}

data SChunk
data STree

-- in SelBin, returning new seelector is superfluous, we could just use previous one
newtype FinalPath = FinalPath [Chunk]
class Selector s m where
  selTree :: Ser a => Container c => s k STree -> c (Maybe a) -> m (Maybe (s k SChunk))
  selBin :: s k SChunk -> Chunk -> m (Maybe (Bool, s k SChunk))
  selTip :: s k SChunk -> Chunk -> m (Maybe (s k STree))
  selNil :: s k SChunk -> m (Chunk, [Chunk])

accessRadix :: forall sel c k a tree chunk sig m. (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Typeable k, Ser a)
  => (c (Maybe a) -> chunk -> tree) -- ^ on sub, tree
  -> (FinalPath -> RadixTree c k a -> tree) -- ^ on found, tree
  -> (Chunk -> [Chunk] -> FinalPath -> chunk) -- ^ on missing, chunk
  -> (Chunk -> tree -> chunk) -- ^ on Tip, chunk
  -> (Bool -> Chunk -> c (RadixChunk c k a) -> chunk -> chunk) -- ^ on branch, chunk
  -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m chunk, RevList Chunk -> sel k STree -> RadixTree c k a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m chunk
    goChunk path sel1 chunkM =
      let
        selNil' = do
          (k, ks) <- selNil sel1
          pure (k, onMissingC k ks (FinalPath $ toList path <> [k] <> ks))
        newBranch :: Chunk -> m chunk
        newBranch exKey = do
          (key, missing) <- selNil'
          let (mask, placeRight) = makeMask exKey key
          pure $ onBranchC placeRight mask chunkM missing
      in fetchC chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> snd <$> selNil'
        (Tip key subtree) -> selTip sel1 key >>= \case
          Nothing -> newBranch key
          Just sel2 -> onTipC key <$> goTree (path `revSnoc` key) sel2 subtree
        (Bin mask l r) -> selBin sel1 mask >>= \case
          Nothing -> newBranch mask
          Just (pickRight, sel2) -> onBranchC pickRight mask (if pickRight then l else r) <$> goChunk path sel2 (if pickRight then r else l)
    goTree :: RevList Chunk -> sel k STree -> RadixTree c k a -> m tree
    goTree path sel1 rt@(RadixTree val chunk) = selTree sel1 val >>= \case
      Nothing -> pure $ onFoundT (FinalPath $ toList path) rt
      Just sel2 -> onSubT val <$> goChunk path sel2 chunk
  in (goChunk, goTree)
{-# INLINE accessRadix #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c k a) -> c (RadixChunk c k a) -> RadixChunk' c k a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k)  => (forall b. c2 b -> ReduceC m (c1 b)) -> Bool -> Chunk -> c2 (RadixChunk c2 k a) -> c2 (RadixChunk c2 k a) -> m (c1 (RadixChunk c2 k a))
mkBin f a b c d = allocReducedChunk f $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkTipNonRe :: Chunk -> RadixTree c k a -> RadixChunk' c k a
mkTipNonRe = Tip

mkTip :: (Container c1, Container c2, Has AppIO sig m, Ser a, Typeable k) => (forall b. c2 b -> ReduceC m (c1 b)) -> Chunk -> RadixTree c2 k a -> m (c1 (RadixChunk c2 k a))
mkTip f k v = allocReducedChunk f $ mkTipNonRe k v
{-# INLINE mkTip #-}

internalLookup :: (Has (AppIO :+: Reduce) sig m, Selector sel m, Container c, IsRadixKey k, Ser a, Typeable k) => (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (Maybe (k, a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (Maybe (k, a))))
internalLookup = accessRadix
  (\_ -> id)
  (\(FinalPath k) (RadixTree a _) -> ((fromRadixKey k,) <$>) <$> fetchC a)
  (\_ _ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookupKV :: (Has AppIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe (k, a))
lookupKV k tr = runReduce $ join $ snd internalLookup [] k tr

lookup :: (Has AppIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe a)
lookup k tr = fmap snd <$> lookupKV k tr

internalNested :: (Ser a, Container c, Algebra sig m, Has AppIO sig m, Typeable k) => a -> [Chunk] -> m (c (RadixChunk c k a))
internalNested val ks = do
  finalVal <- allocC $ Just val
  (_state, res) <- foldrM
    (\key (subval, subchunk) ->
      (wrapB sNothing,) <$> allocC (mkReducible $ mkTipNonRe key $ RadixTree subval subchunk)) -- unlikely reduced
    (finalVal, wrapB sNil)
    ks
  pure res

internalInsert :: forall sel c k sig m a. (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Ser a, Typeable k) => a -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalInsert val = accessRadix
  (\a b -> RadixTree a <$> b)
  (\_ (RadixTree _oldVal b) -> (`RadixTree` b) <$> allocC (Just val))
  (\key1 keys2 _ -> internalNested val (key1:keys2))
  (\k v -> allocC . mkReducible . mkTipNonRe k =<< v)
  (\k r a b -> allocC . mkReducible . mkBinNonRe k r a =<< b)
{-# INLINE internalInsert #-}

-- short-circuit
insert :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser p, Typeable k) => sel k STree -> p -> RadixTree c k p -> m (RadixTree c k p)
insert k v tr = runReduce $ join $ snd (internalInsert v) [] k tr

-- could be m (f (...)), but I don't think it's worth it
-- edit: probably needed, but probably overshadowed by the Church theme
internalUpdate :: (Selector sel m, Container c, Has (AppIO :+: Reduce) sig m, Ser a, Typeable k)
  => (c (Maybe a) -> m (c (Maybe a))) -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalUpdate f = accessRadix
  (\a b -> RadixTree a <$> b) -- on sub, tree
  (\_ (RadixTree updated sub) -> (`RadixTree` sub) <$> f updated) -- on found, tree
  (\_ _ _ -> pure $ wrapB sNil) -- on missing, chunk
  (\key tree -> mkTip pure key =<< tree) -- on Tip, chunk
  (\k r a b -> mkBin pure k r a =<< b) -- on branch, chunk
{-# INLINE internalUpdate #-}

-- short-circuit?
update :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k) => (c (Maybe a) -> ReduceC m (c (Maybe a))) -> sel k STree -> RadixTree c k a -> m (RadixTree c k a)
update f k tr = runReduce $ join $ snd (internalUpdate f) [] k tr

-- short-circuit
delete :: (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (RadixTree c k a)
delete = update (\_ -> pure $ wrapB sNothing)

pop :: (Selector sel (ReduceC (WriterC (First a) m)), Container c, Has AppIO sig m, Ser a, Typeable k) => sel k STree -> RadixTree c k a -> m (Maybe a, RadixTree c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure $ wrapB sNothing
  )
  k rt

upsertChurchInternal ::
  (Selector sel (ReduceC m), Container c, Has AppIO sig m, Ser a, Typeable k, IsRadixKey k) =>
    (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> ReduceC m (  ReduceC m (Maybe (k, a)), a -> m (c (RadixChunk c k a)) )
    , RevList Chunk -> sel k STree -> RadixTree c k a -> ReduceC m (  ReduceC m (Maybe (k, a)), a -> m (RadixTree c k a) ))
-- actually the snd part could work with any other monad, but I'm afraid to break the specialization at any step, needs testing.
upsertChurchInternal = accessRadix
  (\a (lookRes, ins) -> (lookRes, \newVal -> RadixTree a <$> ins newVal)) -- on sub, tree
  (\(FinalPath k) (RadixTree exVal sub) -> (fmap (fromRadixKey k,) <$> fetchC exVal, \newVal -> (`RadixTree` sub) <$> allocC (Just newVal))) -- on found, tree
  (\k1 ks _ -> (pure Nothing, \newVal -> internalNested newVal (k1:ks))) -- on missing, chunk
  (\key (lookRes, ins) -> (lookRes, \newVal -> mkTip pure key =<< ins newVal)) -- on Tip, chunk
  (\k r a (lookRes, ins) -> (lookRes, \newVal -> mkBin pure k r a =<< ins newVal)) -- on branch, chunk
{-# INLINE upsertChurchInternal #-}

upsertChurch :: (Container c, Has AppIO sig m, Selector sel (ReduceC m), Ser a, Typeable k, IsRadixKey k) => sel k STree -> RadixTree c k a -> m (Maybe a, a -> m (RadixTree c k a))
upsertChurch sel tree = runReduce do
  (lookRes1M, ins1) <- snd upsertChurchInternal [] sel tree
  lookRes1 <- lookRes1M
  pure (snd <$> lookRes1, ins1)

-- misc

-- TODO: in some places we implicitly allocC. Shouldn't all allocations be performed by the end-user?
-- TODO: prepF hurts performance, we should get rid of it if possible.
-- TODO: move onTree/onBin/onTip/onNil to strategy
class (Container c, Container cfin) => AppWither strat m c cfin where
  -- stratWither :: strat -> ResB (Res a :-> ReduceC m (Res b)) -> c a -> ReduceC m (cfin b)
  stratWitherLift :: (Has Fresh sig2 m2, InferValT a, InferValT b) => strat -> (Res a -> ReduceC m (Res b)) -> m2 (c a -> ReduceC m (cfin b))

instance (Has AppIO sig m, Container c, Container cfin) => AppWither AppForce m c cfin where
  stratWitherLift _ f = pure \a -> do
    a' <- unwrap a
    wrap <$> f a'

instance AppWither AppDelay AppIOC Delay Delay where
  stratWitherLift _ f = do
    preparedF <- delayAppBuiltinFun . FunBuiltin =<< builtin (M . fmap C . runReduce . f . unC)
    pure \a -> mkDelayCache (preparedF `DelayApp` a)

witherF :: forall tree chunk sig1 m1 sig2 m2 strat c cfin k a b.
  (Has Fresh sig1 m1, MonadFix m1, AppWither strat m2 c cfin, InferValT a, InferValT b, Ser a, Has AppIO sig2 m2, Typeable k, InferValT chunk, InferValT k, InferContainerT c)
  => (cfin (Maybe b) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (Res (Maybe a) -> a -> ReduceC m2 (Res (Maybe b)))
  -> m1 (c (RadixChunk c k a) -> ReduceC m2 (cfin chunk), RadixTree c k a -> m2 tree) -- impredicativity
witherF onTree onBin onTip onNil strat f = mdo
  goVal <- stratWitherLift strat \vR -> do
    vM <- fetch vR
    case vM of
      Nothing -> pure $ ResBuiltin sNothing
      Just v -> f vR v
  goChunk <- stratWitherLift strat \chunkRes -> do
    chunkRed <- fetch chunkRes
    reducible reduceChunk chunkRed \case
      Tip mask v -> do
        t <- goTree v
        lift $ onTip mask t
      Bin mask l r -> do
        (l', r') <- (,) <$> goChunk l <*> goChunk r
        lift $ onBin True mask l' r'
      Nil -> lift onNil
  let
    goTree :: RadixTree c k a -> ReduceC m2 tree
    goTree (RadixTree vC subC) = do
      (a, b) <- (,)
        <$> goVal vC
        <*> goChunk subC
      lift $ onTree a b
  pure (goChunk, runReduce . goTree)

wither :: forall sig1 m1 sig2 m2 strat c cfin k a b.
  (Has Fresh sig1 m1, MonadFix m1, Has AppIO sig2 m2, AppWither strat m2 c cfin, Ser b, Ser a, Typeable k, InferValT b, InferValT a, InferValT k, InferContainerT cfin, InferContainerT c)
  => strat
  -> (Res (Maybe a) -> a -> ReduceC m2 (Res (Maybe b)))
  -> m1 (c (RadixChunk c k a) -> ReduceC m2 (cfin (RadixChunk cfin k b)), RadixTree c k a -> m2 (RadixTree cfin k b)) -- impredicativity
wither = witherF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ ResBuiltin sNil)

sWither :: Q Exp
sWither = do
  strat <- newName "strat"
  f <- newName "f"
  [varP strat, varP f] `lamE` (
      varE 'snd `appE` (sFreshI `appE` (varE 'wither `appE` varE strat `appE` varE f))
    )

data OnOne chunk (m :: Type -> Type) c k this fin = OnOne
  { onOneVal :: !(Res (Maybe this) -> this -> m (Res (Maybe fin))) -- this must be unwrapped for this conclusion
  , onOneSubtree :: !(Res (RadixChunk c k this) -> ReduceC m (Res chunk)) }
newtype OnBoth m one two fin = OnBoth
  { onBothVal :: Res (Maybe one) -> one -> Res (Maybe two) -> two -> m (Res (Maybe fin)) }
data OnSame chunk m c cfin k one two fin = OnSame
  { onSameVal :: !(c (Maybe one) -> c (Maybe two) -> m (cfin (Maybe fin)))
  , onSameValR :: !(Res (Maybe one) -> Res (Maybe two) -> m (Res (Maybe fin)))
  , onSameSubtree :: !(c (RadixChunk c k one) -> c (RadixChunk c k two) -> m (cfin chunk))
  , onSameSubtreeR :: !(Res (RadixChunk c k one) -> Res (RadixChunk c k two) -> m (Res chunk)) }

class (Container c, Container cfin) => AppMerge strat m c cfin where
  -- stratMerge :: strat -> Res (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" m) (Res z)) -> c x -> c y -> Reduce'C "1" (Reduce'C "2" m) (cfin z)
  stratMergeLift :: (Has Fresh sig2 m2, InferValT x, InferValT y, InferValT z)
    => strat -> (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" m) (Res z)) -> m2 (c x -> c y -> Reduce'C "1" (Reduce'C "2" m) (cfin z))

instance (Has AppIO sig m, Container c, Container cfin) => AppMerge AppForce m c cfin where
  stratMergeLift _ f = pure \a b ->
    wrap <$> join (f <$> unwrap' (Proxy @"1") a <*> unwrap' (Proxy @"2") b)

instance AppMerge AppDelay AppIOC Delay Delay where
  stratMergeLift _ f = do
    preparedF <- delayAppBuiltinFun . FunCurry . FunBuiltin =<< builtin \(C a, C b) -> M $
      fmap C $ runReduce' @"2" $ runReduce' @"1" $ f a b
    pure \a b -> mkDelayCache (preparedF `DelayApp` a `DelayApp` b)
 

reduce1 :: Algebra sig m => ReduceC m a -> Reduce'C "1" (Reduce'C "2" m) a
reduce1 (Reduce'C act) = do
  flag <- send $ GetReduce' @"1"
  lift $ lift $ runReader flag act

reduce2 :: Algebra sig m => ReduceC m a -> Reduce'C "1" (Reduce'C "2" m) a
reduce2 (Reduce'C act) = do
  flag <- send $ GetReduce' @"2"
  lift $ lift $ runReader flag act

-- I believe there is a problem with how mergeF handles references and containers. It performs some destructive wraps and unwraps here and there.
mergeF :: forall sig1 m1 sig2 m2 strat c cfin k one two fin chunk tree.
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, Has AppIO sig2 m2
  , InferContainerT c, InferValT one, InferValT two, InferValT fin, InferValT chunk, InferValT k, Typeable k
  , Ser one, Ser two)
  => (cfin (Maybe fin) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> strat
  -> OnOne chunk m2 c k one fin
  -> OnOne chunk m2 c k two fin
  -> OnBoth m2 one two fin
  -> Maybe (OnSame chunk m2 c cfin k one two fin)
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> m2 tree)
mergeF onTree onBin onTip strat one1 one2 both sameM = mdo
  let
    checkSame :: forall c2 a b w. Container c2 => c2 a -> c2 b -> (OnSame chunk m2 c cfin k one two fin -> w) -> w -> w
    checkSame = case sameM of
        Just hdl -> \a b h o -> if a `same` b
          then h hdl
          else o
        Nothing -> \_ _ _ o -> o
    checkSameMergeChunk a b = checkSame a a (\s -> lift $ lift $ onSameSubtree s a b) (mergeChunk a b)
  mergeVal <- stratMergeLift strat \r1 r2 -> do
    checkSame r1 r2
      (\s -> lift $ lift $ onSameValR s r1 r2)
      do
        v1 <- fetch r1
        v2 <- fetch r2
        lift $ lift $ case (v1, v2) of
          (Just a , Just b ) -> onBothVal both r1 a r2 b
          (Just a , Nothing) -> onOneVal one1 r1 a
          (Nothing, Just b ) -> onOneVal one2 r2 b
          (Nothing, Nothing) -> pure $ ResBuiltin sNothing
  mergeChunk  <- stratMergeLift strat \res1 res2 ->
    checkSame
      res1
      res2
      (\s -> lift $ lift $ onSameSubtreeR s res1 res2)
      do
        v1 <- fetch res1
        v2 <- fetch res2
        let binOfMerges mask a1 a2 b1 b2 = do
              (a, b) <- (,) <$> checkSameMergeChunk a1 a2 <*> checkSameMergeChunk b1 b2
              lift $ lift $ onBin True mask a b
            unrelated key1 key2 = do
              let (mask, pickRight) = makeMask key1 key2
              (a, b) <- (,) <$> reduce1 (onOneSubtree one1 res1) <*> reduce2 (onOneSubtree one2 res2)
              lift $ lift $ onBin pickRight mask (wrap a) (wrap b)
            oneContainsTwo mask1 key2 l1 r1 = case tryMask mask1 key2 of
              Just True  -> binOfMerges mask1 l1 (wrapB sNil) r1 (wrap res2)
              Just False -> binOfMerges mask1 l1 (wrap res2) r1 (wrapB sNil)
              Nothing -> unrelated mask1 key2
            twoContainsOne key1 mask2 l2 r2 = case tryMask mask2 key1 of
              Just False -> binOfMerges mask2 (wrap res1) l2 (wrapB sNil) r2
              Just True  -> binOfMerges mask2 (wrapB sNil) l2 (wrap res1) r2
              Nothing -> unrelated mask2 key1
        reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) v1 \v1' ->
          reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) v2 \v2' ->
            case (v1', v2') of
              (_, Nil) -> reduce1 $ onOneSubtree one1 res1
              (Nil, _) -> reduce2 $ onOneSubtree one2 res2
              (Bin mask1 l1 r1, Bin mask2 l2 r2)
                | mask1 == mask2 -> binOfMerges mask1 l1 l2 r1 r2
                | otherwise -> if countTrailingZeros mask1 >= countTrailingZeros mask2
                  then oneContainsTwo mask1 mask2 l1 r1
                  else twoContainsOne mask1 mask2 l2 r2
              (Bin mask1 l1 r1, Tip key2 _) -> oneContainsTwo mask1 key2 l1 r1
              (Tip key1 _, Bin mask2 l2 r2) -> twoContainsOne key1 mask2 l2 r2
              (Tip key1 l, Tip key2 r)
                | key1 == key2 -> do
                  t <- mergeTree l r
                  lift $ lift $ onTip key1 t
                | otherwise -> unrelated key1 key2
  let mergeTree (RadixTree k1 s1) (RadixTree k2 s2) = do
        (a, b) <- (,)
          <$> checkSame k1 k2 (\s -> lift $ lift $ onSameVal s k1 k2) (mergeVal k1 k2)
          <*> checkSameMergeChunk s1 s2
        lift $ lift $ onTree a b
  pure \a b -> runReduce' @"2" $ runReduce' @"1" $ mergeTree a b

merge ::
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, Has AppIO sig2 m2
  , InferContainerT c, InferContainerT cfin, InferValT one, InferValT two, InferValT fin, InferValT k, Typeable k
  , Ser one, Ser two, Ser fin)
  => strat
  -> OnOne (RadixChunk cfin k fin) m2 c k one fin
  -> OnOne (RadixChunk cfin k fin) m2 c k two fin
  -> OnBoth m2 one two fin
  -> Maybe (OnSame (RadixChunk cfin k fin) m2 c cfin k one two fin)
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> m2 (RadixTree cfin k fin))
merge = mergeF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap)

-- suggestion: remove that
{-
sMerge :: Q Exp
sMerge = do
  strat <- newName "strat"
  one1 <- newName "one1"
  one2 <- newName "one2"
  both <- newName "both"
  sameM <- newName "sameM"
  [varP strat, varP one1, varP one2, varP both] `lamE` (
      sFreshI `appE` (
        varE 'merge `appE`
        varE strat `appE`
        varE one1 `appE`
        varE one2 `appE`
        varE both `appE`
        varE sameM)
    )
-}

onOneErase :: Applicative m => OnOne (RadixChunk c2 k1 a) m c1 k2 this fin
onOneErase = OnOne (const $ const $ pure $ wrapB sNothing) (const $ pure $ wrapB sNil)

-- TODO: get rid of alloc's, first of all by creating a Maybe (Rec a) ~ Rec (Maybe a) isomorphism?
onOneKeep :: Applicative m => OnOne (RadixChunk c k fin) m c k fin fin
onOneKeep = OnOne (const . pure) pure

onBothZip :: (Has AppIO sig m, Ser fin) => (one -> two -> Maybe fin) -> OnBoth m one two fin
onBothZip f = OnBoth \_ one _ two -> alloc $ f one two

onOneWitherFM ::
  (Has Fresh sig1 m1, MonadFix m1, Container c, AppWither strat m2 c cfin, Has AppIO sig2 m2,
  InferContainerT c, InferValT b, InferValT a, InferValT chunk, InferValT k, Typeable k,
  Ser a)
  => (cfin (Maybe b) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (Res (Maybe a) -> a -> m2 (Res (Maybe b))) -> m1 (OnOne chunk m2 c k a b)
onOneWitherFM onTree onBin onTip onNil strat f = do
  toFin <- fst <$> witherF onTree onBin onTip onNil strat \x y -> lift (f x y)
  pure $ OnOne f \chunk -> toFin (wrap chunk) >>= unwrap

onOneWitherM :: (Has Fresh sig m, MonadFix m, Container c, Has AppIO sig2 m2, AppWither strat m2 c cfin, Ser this, InferContainerT c, InferContainerT cfin, InferValT fin, InferValT this, InferValT k, Typeable k, Ser fin)
  => strat -> (Res (Maybe this) -> this -> m2 (Res (Maybe fin))) -> m (OnOne (RadixChunk cfin k fin) m2 c k this fin)
onOneWitherM = onOneWitherFM (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ wrapB sNil)

mergeWithUpdate :: forall c sig1 m1 sig2 m2 k fin upd.
  (Container c, Has Fresh sig1 m1, MonadFix m1, Has AppIO sig2 m2, Ser fin, InferValT k, InferValT upd, InferValT fin, InferContainerT c, Ser upd, Typeable k)
  => (Maybe fin -> upd -> fin)
  -> m1 (RadixTree c k fin
    -> RadixTree c k upd
    -> m2 (RadixTree c k fin))
mergeWithUpdate f = do
    w <- onOneWitherM AppForce $ const $ alloc . Just . f Nothing
    merge AppForce onOneKeep w
      (OnBoth \_ fin _ upd -> allocC $ Just $ f (Just fin) upd)
      Nothing

-- diff

diffF ::
  (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, AppWither strat m2 c cfin, Has AppIO sig2 m2, InferContainerT c, InferValT fin, InferValT a, InferValT chunk, InferValT k, Ser a, Typeable k)
  => (cfin (Maybe fin) -> cfin chunk -> m2 tree)
  -> (Bool -> Chunk -> cfin chunk -> cfin chunk -> m2 (Res chunk))
  -> (Chunk -> tree -> m2 (Res chunk))
  -> m2 (Res chunk)
  -> strat
  -> (MapDiffE a -> m2 (Res (Maybe fin)))
  -> m1 (RadixTree c k a -> RadixTree c k a -> m2 tree)
diffF onTree onBin onTip onNil strat f = do
  w1 <- onOneWitherFM onTree onBin onTip onNil strat \_ x -> f (MapDel x)
  w2 <- onOneWitherFM onTree onBin onTip onNil strat \_ x -> f (MapAdd x)
  mergeF onTree onBin onTip strat w1 w2
    (OnBoth \_ a _ b -> f (MapUpd a b))
    (Just $ OnSame (\_ _ -> pure $ wrapB sNothing) (\_ _ -> pure $ wrapB sNothing) (\_ _ -> wrap <$> onNil) (\_ _ -> onNil))

diff :: (Has Fresh sig1 m1, MonadFix m1, AppMerge strat m2 c cfin, AppWither strat m2 c cfin, Has AppIO sig2 m2, Ser a, InferContainerT c, InferContainerT cfin, InferValT fin, InferValT a, InferValT k, Typeable k, Ser fin)
  => strat
  -> (MapDiffE a -> m2 (Res (Maybe fin)))
  -> m1 (RadixTree c k a -> RadixTree c k a -> m2 (RadixTree cfin k fin))
diff = diffF (\a b -> pure $ RadixTree a b) (mkBin unwrap) (mkTip unwrap) (pure $ wrapB sNil)

diffId ::
  (Ser a, Ser (MapDiffE a), InferValT k, InferValT a, InferValT (MapDiffE a), InferContainerT cfin, InferContainerT c, AppWither strat m2 c cfin, AppMerge strat m2 c cfin, Has AppIO sig m2, Typeable k) =>
  strat -> RadixTree c k a -> RadixTree c k a -> m2 (RadixTree cfin k (MapDiffE a))
diffId strat = $sFreshI $ diff strat $ alloc . Just

intersection :: (AppMerge p m c2 c2, Has AppIO sig m, InferContainerT c2, InferValT two, InferValT fin,  InferValT k2, Ser two, Ser fin, Typeable k2) => p -> RadixTree c2 k2 fin -> RadixTree c2 k2 two -> m (RadixTree c2 k2 fin)
intersection strat = $sFreshI $ merge strat onOneErase onOneErase (OnBoth \a _ _ _ -> pure a) $ Just $
  OnSame (\l _ -> pure l) (\l _ -> pure l) (\l _ -> pure l) (\l _ -> pure l)

-- selectors

data family SelEq k t -- access equal to key

newtype instance SelEq k STree = SelEqT [Chunk]
data instance SelEq k SChunk = SelEqC !Chunk ![Chunk]

instance Applicative m => Selector SelEq m where
  selTree (SelEqT keys) _val = pure case keys of
    [] -> Nothing
    k:ks-> Just $ SelEqC k ks
  selBin (SelEqC key keys) mask = pure $ (, SelEqC key keys) <$> tryMask mask key
  selTip (SelEqC key keys) key2 = pure $ if key == key2 then Just (SelEqT keys) else Nothing
  selNil (SelEqC key keys) = pure (key, keys)

selEq :: IsRadixKey k => k -> SelEq k STree
selEq = SelEqT . toRadixKey

-- I'm writing this for the forth time or something.
-- Me, please, DO NOT DELETE THIS.
data family SelNonDet k t -- access existing value by choosing

data instance SelNonDet k STree = SelNonDetT
data instance SelNonDet k SChunk = SelNonDetC

-- I don't agree with how it is, but True refers to the left option
-- and False refers to the right option of Choose.
-- Why? I don't know.
instance Has (AppIO :+: Reduce :+: NonDet) sig m => Selector SelNonDet m where
  selTree SelNonDetT valM = do
    now <- send Choose
    if now
      then do
        exists <- isJust <$> fetchC valM
        unless exists E.empty
        pure Nothing
      else pure $ Just SelNonDetC
  selBin self _ = do
    left <- send Choose
    pure $ Just (not left, self)
  selTip SelNonDetC _chunk = pure $ Just SelNonDetT
  selNil _ = E.empty

selNonDet :: SelNonDet k STree
selNonDet = SelNonDetT

runNonDetMin :: Monad m => NonDetC m a -> m (Maybe a)
runNonDetMin = runNonDet
  (\l r -> l >>= \case
    Nothing -> r
    l' -> pure l')
  (pure . Just)
  (pure Nothing)

reverseNonDet :: NonDetC m a -> NonDetC m a -- Mi amas FP per tuta mia koro.
reverseNonDet act = NonDetC \choose p n -> runNonDet (flip choose) p n act
{-# INLINE reverseNonDet #-}

runNonDetMax :: Monad m => NonDetC m a -> m (Maybe a)
runNonDetMax = runNonDetMin . reverseNonDet

-- For each value produced by the NonDetC m a, run the function.
-- The function returns whether to continue consuming the NonDet computation.
forNonDet_ :: Algebra sig m => NonDetC m a -> (a -> m Bool) -> m ()
forNonDet_ gen f = void $ runNonDetMin do
  i <- gen
  lift (f i) >>= \case
    True -> E.empty -- Mark branch as "failed" and move on to the next one.
    False -> pure () -- Mark branch as successful, finishing the NonDet.

data family SelEqNonDet k t

data instance SelEqNonDet k STree = SelEqNonDetT ![Chunk] | SelEqNonDetOffT
data instance SelEqNonDet k SChunk = SelEqNonDetC !Chunk ![Chunk] | SelEqNonDetOffC

selEqChoose :: IsRadixKey k => k -> SelEqNonDet k STree
selEqChoose k =
  let k' = toRadixKey k
  in SelEqNonDetT k'

data ChooseL (m :: Type -> Type) a where -- newtype over Choose
  ChooseL :: ChooseL m Bool
data ChooseR (m :: Type -> Type) a where -- newtype over Choose
  ChooseR :: ChooseR m Bool
-- We could use labels, but it feels as a war crime for some reason
type NonDetLR = ChooseL :+: ChooseR :+: Empty

-- Actually, we're quite generous with making it a monad, since we probably could handle everything with just an applicative,
-- but I don't dare to try.
newtype NonDetLRC m a = NonDetLRC (forall b. (m b -> m b -> m b) -> (m b -> m b -> m b) -> (a -> m b) -> m b -> m b)
  deriving Functor

runNonDetLR :: (m b -> m b -> m b) -> (m b -> m b -> m b) -> (a -> m b) -> m b -> NonDetLRC m a -> m b
runNonDetLR l r p n (NonDetLRC f) = f l r p n

instance Applicative (NonDetLRC m) where
  pure x = NonDetLRC \_l _r p _n -> p x
  (NonDetLRC f) <*> (NonDetLRC a) = NonDetLRC \l r p n ->
    f l r (\f' -> a l r (p . f') n) n

instance Monad (NonDetLRC m) where
  (NonDetLRC a) >>= f = NonDetLRC \l r p n ->
    a l r (runNonDetLR l r p n . f) n

instance Algebra sig m => Algebra (NonDetLR :+: sig) (NonDetLRC m) where
  alg hdl sig ctx = NonDetLRC \l r p n -> case sig of
    -- Again, I don't like this, but to conform to how NonDet works...
    L (L ChooseL) -> p (False <$ ctx) `l` p (True <$ ctx)
    L (R (L ChooseR)) -> p (True <$ ctx) `r` p (False <$ ctx)
    L (R (R Empty)) -> n
    -- my brain went out of the chat somewhere here, *I hope* this is correct
    -- maybe I should patent brainless programming?
    R other -> thread (dst ~<~ hdl) other (pure ctx) >>= run . runNonDetLR (coerce l) (coerce r) (coerce p) (coerce n)
    where
    dst :: Applicative m => NonDetLRC Identity (NonDetLRC m a) -> m (NonDetLRC Identity a)
    dst = run . runNonDetLR
      (liftA2 pl)
      (liftA2 pr)
      (pure . runNonDetLRTranspose)
      (pure (pure $ NonDetLRC \_l _r _p n -> n))
    pl left main = (\(NonDetLRC left') (NonDetLRC main') -> NonDetLRC \l r p n -> left' l r p n `l` main' l r p n) <$> left <*> main
    pr main right = (\(NonDetLRC main') (NonDetLRC right') -> NonDetLRC \l r p n -> main' l r p n `r` right' l r p n) <$> main <*> right
    runNonDetLRTranspose :: Applicative f => NonDetLRC f a -> f (NonDetLRC m2 a)
    runNonDetLRTranspose = runNonDetLR pl pr (pure . pure) (pure $ NonDetLRC \_l _r _p n -> n)
  {-# INLINE alg #-}

lfork :: Has NonDetLR sig m => m a -> m a -> m a
lfork left main = send ChooseL >>= bool left main

rfork :: Has NonDetLR sig m => m a -> m a -> m a
rfork main right = send ChooseR >>= bool right main

-- | Reinterpret NonDetLRC m ~> NonDetC m,
-- only keeping choices between the main branch and the right branch.
runNonDetLREAfter :: Has NonDet sig m => NonDetLRC m a -> m a
runNonDetLREAfter = runNonDetLR
  (\_left main -> main)
  (<|>)
  pure
  E.empty

instance Has (AppIO :+: Reduce :+: NonDetLR :+: NonDet) sig m => Selector SelEqNonDet m where
  selTree (SelEqNonDetT k) valM = do
    main <- selTree (SelEqT k) valM
    case main of
      Nothing -> pure Nothing `rfork` pure (Just SelEqNonDetOffC)
      Just (SelEqC a b) -> pure Nothing `lfork` pure (Just $ SelEqNonDetC a b)
  selTree SelEqNonDetOffT valM = fmap (\SelNonDetC -> SelEqNonDetOffC) <$> selTree SelNonDetT valM

  selBin (SelEqNonDetC p ps) mask = do
    main <- selBin (SelEqC p ps) mask
    case main of
      Nothing -> E.empty
      Just (pickRight, (SelEqC p' ps')) -> Just <$> if pickRight
        then pure (False, SelEqNonDetOffC) `lfork` pure (True, SelEqNonDetC p' ps')
        else pure (False, SelEqNonDetC p' ps) `rfork` pure (True, SelEqNonDetOffC)
  selBin SelEqNonDetOffC mask = fmap (fmap \SelNonDetC -> SelEqNonDetOffC) <$> selBin SelNonDetC mask

  selTip (SelEqNonDetC p ps) mask = fmap (\(SelEqT a) -> SelEqNonDetT a) <$> selTip (SelEqC p ps) mask
  selTip SelEqNonDetOffC mask = fmap (\SelNonDetT -> SelEqNonDetOffT) <$> selTip SelNonDetC mask

  selNil (SelEqNonDetC p ps) = selNil $ SelEqC p ps
  selNil SelEqNonDetOffC = selNil SelNonDetC

selEqNonDet :: IsRadixKey k => k -> SelEqNonDet k STree
selEqNonDet = SelEqNonDetT . toRadixKey

{-
-- range

-- Something's wrong here.

-- `Maybe` stands for Unrestricted.
-- `Bool` stands for inclusive?
data Range = Range !(Maybe (Bool, NonEmpty Chunk)) !(Maybe (NonEmpty Chunk, Bool))

splitRange :: Chunk -> Range -> (Maybe Range, Maybe Range)
splitRange mask (Range lM rM) =
  let
    hasLeftSubrange = maybe True (maybe False (== False) . tryMask mask . NE.head . snd) lM
    hasRightSubrange = maybe True (maybe False (== True) . tryMask mask . NE.head . fst) rM
  in
    ( if hasLeftSubrange then Just (Range lM (if hasRightSubrange then Nothing else rM)) else Nothing
    , if hasRightSubrange then Just (Range (if hasLeftSubrange then Nothing else lM) rM) else Nothing)

unconsRange :: Chunk -> Range -> Either Bool Range
unconsRange key (Range lM rM) =
  let
    isWithinLeft = maybe True ((key >=) . NE.head . snd) lM
    isWithinRight = maybe True ((key <=) . NE.head . fst) rM
  in if isWithinLeft && isWithinRight -- uncons shouldn't handle all the Writes since, for example, there is a 
    then case rM of
      Just (x :| _, inclusive)
        | x == key -> Left inclusive
      _ -> Right $ Range
        (lM >>= \(inc, l) -> (inc,) <$> snd (NE.uncons l))
        (rM >>= \(r, inc) -> (,inc) <$> snd (NE.uncons r))
    else Left False
-}

-- construction

empty :: Container c => RadixTree c k a
empty = RadixTree (wrapB sNothing) (wrapB sNil)

fromListM :: forall c sig m k v. (Has AppIO sig m, Container c, IsRadixKey k, Typeable k, Ser v) => [(k, v)] -> m (RadixTree c k v)
fromListM = foldM (\t (k, v) -> insert (selEq k) v t) empty

toListM :: forall c sig m k v. (Has AppIO sig m, Container c, IsRadixKey k, Typeable k, Ser v) => RadixTree c k v -> m [(k, v)]
toListM = fmap catMaybes . runNonDetA . lookupKV selNonDet

-- data DiffE v = Add !v | Upd !v | Del !v

-- debug

-- Stupid String-based show for debug
tryFetchShow :: (Container c, Show a) => c a -> String
tryFetchShow = maybe "<>" show . tryFetchC

-- instance (Container c, Show a) => Show (RadixTree c k a) where
--   show (RadixTree val chunk) = "(RadixTree (" <> tryFetchShow val <> ") " <> tryFetchShow chunk <> ")"
-- instance (Container c, Show a) => Show (RadixChunk' c k a) where
--   show = \case
--     Nil -> "Nil"
--     Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
--     Bin mask l r -> "(Bin " <> show mask <> " " <> tryFetchShow l <> " " <> tryFetchShow r <> ")"
