{-# LANGUAGE RecursiveDo, PatternSynonyms #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (lookup, Set, Map, mask, toList, catch)
import Data.Bits (countTrailingZeros, (.&.), unsafeShiftR, complement, xor, finiteBitSize, unsafeShiftL, (.|.), countLeadingZeros)
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Data.Foldable (foldrM)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Control.Monad.Fix (MonadFix)
import Data.Monoid (First(..))
import Control.Effect.NonDet (NonDet)
import Control.Effect.Choose (Choose(..))
import qualified Control.Effect.Empty as E
import GHC.Exts (IsList(..))
import Control.Carrier.NonDet.Church (runNonDet, NonDetC, runNonDetA)
import RIO.List (uncons)
import Control.Effect.Fresh (Fresh)

$(moduleId 1)

-- TODO: here, many type annotations reference WriterC Reduced. Probably this could be avoided, if it even should be?

type Chunk = Word32

class IsRadixKey key where
  toRadixKey :: key -> [Chunk]
  fromRadixKey :: [Chunk] -> key

instance IsRadixKey [Chunk] where
  toRadixKey = id
  fromRadixKey = id
instance IsRadixKey (ResPOC a) where
  toRadixKey (ResPOC i) = [fromIntegral $ i `div` 4294967296, fromIntegral $ i `mod` 4294967296]
  fromRadixKey = \case
    [a, b] -> ResPOC $ fromIntegral a * 4294967296 + fromIntegral b
    _nonTwo -> error "key corrupted" -- this is okay. But, the problem is, `fromRadixKey` is exposed.
    -- So it's better to tie this to some newtype'd [Chunk]?

tryMask :: Chunk -> Chunk -> Maybe Bool
tryMask mask key =
  if prefixBits .&. mask == prefixBits .&. key
  then Just $ 1 .&. (key `unsafeShiftR` countTrailingZeros mask) == 1
  else Nothing
  where
    prefixBits = complement $ mask - 1 `xor` mask

makeMask :: Chunk -> Chunk -> (Chunk, Bool)
makeMask l r =
  let maskBit = unsafeShiftL 1 (finiteBitSize (0 :: Chunk) - 1 - countLeadingZeros (l `xor` r))
  in (maskBit .|. (l .&. complement (maskBit-1)), r .&. maskBit /= 0)

-- task: better key support
-- build "key" marker into the RadixTree datatype, allow different keys to be used, implement min/max view.

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.
data RadixTree c k a = RadixTree !(c (Maybe a)) !(c (RadixChunk c k a)) -- both element and next is containerized, both can be left unwrapped.
type RadixChunk c k a = Reducible (RadixChunk' c k a)
data RadixChunk' c k a
  = Nil
  | Tip !Chunk !(RadixTree c k a) -- RadixTree is the only possible branch. Still could be containerized, but I'm not sure it's worth it
  | Bin !Chunk !(c (RadixChunk c k a)) !(c (RadixChunk c k a)) -- Either branch can be accessed, so containerization

sNil :: Container c => c (RadixChunk c2 k a)
sNil = $sRunEvalFresh $ allocC $ mkReducible Nil

-- -- TODO: Don't know how effective is this
reduceChunk'' :: (Container c, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a, Maybe (c (RadixChunk c k a)))
reduceChunk'' (Proxy @s) = \case
  Tip _ (RadixTree (tryFetchC -> Just Nothing) (tryFetchC -> Just (readReducible -> Nil))) -> reduce' (Proxy @s) $> (Nil, Just sNil)
  Bin _ left'@(tryFetchC -> Just (readReducible -> left)) right'@(tryFetchC -> Just (readReducible -> right))
    | Nil <- left -> reduce' (Proxy @s) $> (right, Just right') -- hopefully no need to reduceChunk left/right
    | Nil <- right -> reduce' (Proxy @s) $> (left, Just left')
  nonReducible -> pure (nonReducible, Nothing)
{-# INLINE reduceChunk'' #-}

reduceChunk' :: (Container c, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk' p v = fst <$> reduceChunk'' p v
{-# INLINE reduceChunk' #-}

reduceChunk :: (Container c, Has (FreshIO :+: Reduce) sig m) => RadixChunk' c k a -> m (RadixChunk' c k a)
reduceChunk = reduceChunk' (Proxy @"")
{-# INLINE reduceChunk #-}

allocReducedChunk :: (Container c1, Container c2, Has FreshIO sig m) => (forall b. c2 b -> ReduceC m (c1 b)) -> RadixChunk' c2 k a -> m (c1 (RadixChunk c2 k a))
allocReducedChunk f c = runReduce $ reduceChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v
{-# INLINE allocReducedChunk #-}

-- This is hilarious, but probably should be rewritten as
-- class Selector m chunk tree where
--   ...
-- --
-- newtype sel k "tree" = SelTree (m (Maybe (sel k "chunk")))
-- data sel k "chunk" = SelChunk
--   { selTip :: !(Chunk -> m (Maybe (sel k "tree")))
--   , selBin :: !(Chunk -> m (Maybe (Bool, sel k "chunk")))
--   , selNil :: !(m (Chunk, [Chunk]))
--   }

-- selEq :: Applicative m => IsRadixKey k => k -> sel k "tree"
-- selEq =
--   let
--     t keys = SelTree $ pure case keys of
--       [] -> Nothing
--       k:ks -> Just $ c k ks
--     c key keys = SelChunk
--       (\key2 -> pure $ if key == key2 then Just (t keys) else Nothing)
--       (\mask -> pure $ (, c key keys) <$> tryMask mask key)
--       (pure (key, keys))
--   in t . toRadixKey

data SChunk
data STree

-- in SelBin, returning new seelector is superfluous, we could just use previous one
newtype FinalPath = FinalPath [Chunk]
class Selector s m where
  selTree :: Container c => s k STree -> c (Maybe a) -> m (Maybe (s k SChunk))
  selBin :: s k SChunk -> Chunk -> m (Maybe (Bool, s k SChunk))
  selTip :: s k SChunk -> Chunk -> m (Maybe (s k STree))
  selNil :: s k SChunk -> m (Chunk, [Chunk])

accessRadix :: forall sel c k a tree chunk sig m. (Selector sel m, Container c, Has (FreshIO :+: Reduce) sig m)
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

mkBin :: (Container c1, Container c2, Has FreshIO sig m)  => (forall b. c2 b -> ReduceC m (c1 b)) -> Bool -> Chunk -> c2 (RadixChunk c2 k a) -> c2 (RadixChunk c2 k a) -> m (c1 (RadixChunk c2 k a))
mkBin f a b c d = allocReducedChunk f $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

mkTipNonRe :: Chunk -> RadixTree c k a -> RadixChunk' c k a
mkTipNonRe = Tip

mkTip :: (Container c1, Container c2, Has FreshIO sig m) => (forall b. c2 b -> ReduceC m (c1 b)) -> Chunk -> RadixTree c2 k a -> m (c1 (RadixChunk c2 k a))
mkTip f k v = allocReducedChunk f $ mkTipNonRe k v
{-# INLINE mkTip #-}

internalLookup :: (Has (FreshIO :+: Reduce) sig m, Selector sel m, Container c, IsRadixKey k) => (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (Maybe (k, a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (Maybe (k, a))))
internalLookup = accessRadix
  (\_ -> id)
  (\(FinalPath k) (RadixTree a _) -> ((fromRadixKey k,) <$>) <$> fetchC a)
  (\_ _ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookupKV :: (Has FreshIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k) => sel k STree -> RadixTree c k a -> m (Maybe (k, a))
lookupKV k tr = runReduce $ join $ snd internalLookup [] k tr

lookup :: (Has FreshIO sig m, Selector sel (ReduceC m), Container c, IsRadixKey k) => sel k STree -> RadixTree c k a -> m (Maybe a)
lookup k tr = fmap snd <$> lookupKV k tr

internalInsert :: forall sel c k sig m a. (Selector sel m, Container c, Has (FreshIO :+: Reduce) sig m) => a -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalInsert val = accessRadix
  (\a b -> RadixTree a <$> b)
  (\_ (RadixTree _oldVal b) -> (`RadixTree` b) <$> allocC (Just val))
  (\key1 keys2 _ -> do
    finalVal <- allocC $ Just val
    (_state, res) <- foldrM
      (\key (subval, subchunk) ->
        (sNothing,) <$> allocC (mkReducible $ mkTipNonRe key $ RadixTree subval subchunk)) -- unlikely reduced
      (finalVal, sNil)
      (key1:keys2)
    pure res)
  (\k v -> allocC . mkReducible . mkTipNonRe k =<< v)
  (\k r a b -> allocC . mkReducible . mkBinNonRe k r a =<< b)
{-# INLINE internalInsert #-}

-- short-circuit
insert :: (Selector sel (ReduceC m), Container c, Has FreshIO sig m) => sel k STree -> p -> RadixTree c k p -> m (RadixTree c k p)
insert k v tr = runReduce $ join $ snd (internalInsert v) [] k tr

-- could be m (f (...)), but I don't think it's worth it
internalUpdate :: (Selector sel m, Container c, Has (FreshIO :+: Reduce) sig m)
  => (c (Maybe a) -> m (c (Maybe a))) -> (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (c (RadixChunk c k a))), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (RadixTree c k a)))
internalUpdate f = accessRadix
  (\a b -> RadixTree a <$> b) -- on sub, tree
  (\_ (RadixTree updated sub) -> (`RadixTree` sub) <$> f updated) -- on found, tree
  (\_ _ _ -> pure sNil) -- on missing, chunk
  (\key tree -> mkTip pure key =<< tree) -- on Tip, chunk
  (\k r a b -> mkBin pure k r a =<< b) -- on branch, chunk
{-# INLINE internalUpdate #-}

-- short-circuit?
update :: (Selector sel (ReduceC m), Container c, Has FreshIO sig m) => (c (Maybe a) -> ReduceC m (c (Maybe a))) -> sel k STree -> RadixTree c k a -> m (RadixTree c k a)
update f k tr = runReduce $ join $ snd (internalUpdate f) [] k tr

-- short-circuit
delete :: (Selector sel (ReduceC m), Container c, Has FreshIO sig m) => sel k STree -> RadixTree c k a -> m (RadixTree c k a)
delete = update (\_ -> pure sNothing)

pop :: (Selector sel (ReduceC (WriterC (First a) m)), Container c, Has FreshIO sig m) => sel k STree -> RadixTree c k a -> m (Maybe a, RadixTree c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure sNothing
  )
  k rt

sEmpty :: Container c => c (RadixTree c k a)
sEmpty = $sRunEvalFresh $ allocC empty

-- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

-- misc

-- TODO: prepF hurts performance, we should get rid of it if possible.
class Container c => AppWither strat c where
  stratWither :: strat -> Res (Res a -> ReduceC FreshIOC (Res b)) -> c a -> ReduceC FreshIOC (c b)

instance Container c => AppWither AppForce c where
  stratWither _ f a = do
    f' <- fetch f
    a' <- unwrap a
    wrap <$> f' a'

appWitherDelayPrepF :: Delay (Res (Res a -> ReduceC FreshIOC (Res b)) -> Res a -> FreshIOC (Res b))
appWitherDelayPrepF = $sRunEvalFresh $ allocC \f a -> do
  f' <- fetch f
  runReduce $ f' a
instance AppWither AppDelay Delay where
  stratWither _ f a = mkDelayFresh $ (appWitherDelayPrepF `DelayApp` wrap f) `DelayApp` a

wither :: forall sig m strat c k a b. (Has Fresh sig m, MonadFix m, AppWither strat c)
  => strat
  -> (Res (Maybe a) -> a -> ReduceC FreshIOC (Res (Maybe b)))
  -> m (c (RadixChunk c k a) -> FreshIOC (c (RadixChunk c k b)), RadixTree c k a -> FreshIOC (RadixTree c k b)) -- impredicativity
wither strat f = mdo
  goVal <- allocC \vR -> do
    vM <- fetch vR
    case vM of
      Nothing -> pure sNothing
      Just v -> f vR v
  goChunk <- allocC \chunkRes -> do
    chunkRed <- fetch chunkRes
    reducible reduceChunk chunkRed \case
      Tip mask v -> allocReducedChunk unwrap . Tip mask =<< goTree v
      Bin mask l r -> do
        l' <- stratWither strat goChunk l
        r' <- stratWither strat goChunk r
        allocReducedChunk unwrap $ Bin mask l' r'
      Nil -> pure sNil
  let 
    goTree :: RadixTree c k a -> ReduceC FreshIOC (RadixTree c k b)
    goTree (RadixTree vC subC) = RadixTree
        <$> stratWither strat goVal vC
        <*> stratWither strat goChunk subC
  pure (runReduce . stratWither strat goChunk, runReduce . goTree)

data OnOne c this fin = OnOne
  { onOneVal :: !(Res (Maybe this) -> this -> FreshIOC (Res (Maybe fin))) -- this must be unwrapped for this conclusion
  , onOneSubtree :: !(forall k. Res (RadixChunk c k this) -> FreshIOC (Res (RadixChunk c k fin))) }
newtype OnBoth one two fin = OnBoth
  { onBothVal :: Res (Maybe one) -> one -> Res (Maybe two) -> two -> FreshIOC (Res (Maybe fin)) }

class AppMerge strat c where
  stratMerge :: strat -> Res (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" FreshIOC) (Res z)) -> c x -> c y -> Reduce'C "1" (Reduce'C "2" FreshIOC) (c z)

instance Container c => AppMerge AppForce c where
  stratMerge _ f a b = do
    f' <- fetch f
    wrap <$> join (f' <$> unwrap' (Proxy @"1") a <*> unwrap' (Proxy @"2") b)

appMergeDelayPrepF :: Delay (Res (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" FreshIOC) (Res z)) -> Res x -> Res y -> FreshIOC (Res z))
appMergeDelayPrepF = $sRunEvalFresh $ allocC \f a b -> do
  f' <- fetch f
  runReduce' @"2" $ runReduce' @"1" $ f' a b
instance AppMerge AppDelay Delay where
  stratMerge _ f a b = mkDelayFresh $ DelayApp (DelayApp (DelayApp appMergeDelayPrepF $ wrap f) a) b

merge :: forall c k one two fin strat. forall sig1 m1. (Container c, Has Fresh sig1 m1, MonadFix m1, AppMerge strat c)
  => strat
  -> OnOne c one fin
  -> OnOne c two fin
  -> OnBoth one two fin
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> FreshIOC (RadixTree c k fin)) -- impredicativity...
merge strat one1 one2 both = mdo
  mergeVal <- alloc \r1 r2 -> do
    v1 <- fetch r1
    v2 <- fetch r2
    lift $ lift $ case (v1, v2) of
      (Just a , Just b ) -> onBothVal both r1 a r2 b
      (Just a , Nothing) -> onOneVal one1 r1 a
      (Nothing, Just b ) -> onOneVal one2 r2 b
      (Nothing, Nothing) -> pure sNothing
  mergeChunk <- alloc \res1 res2 -> do
    v1 <- fetch res1
    v2 <- fetch res2
    let binOfMerges mask a1 a2 b1 b2 = do
          a <- stratMerge strat mergeChunk a1 a2
          b <- stratMerge strat mergeChunk b1 b2
          mkBin unwrap True mask a b
        unrelated key1 key2 = do
          let (mask, pickRight) = makeMask key1 key2
          a <- lift $ lift $ onOneSubtree one1 res1
          b <- lift $ lift $ onOneSubtree one2 res2
          mkBin unwrap pickRight mask (wrap a) (wrap b)
        oneContainsTwo mask1 key2 l1 r1 = case tryMask mask1 key2 of
          Just True  -> binOfMerges mask1 l1 sNil r1 (wrap res2)
          Just False -> binOfMerges mask1 l1 (wrap res2) r1 sNil
          Nothing -> unrelated mask1 key2
        twoContainsOne key1 mask2 l2 r2 = case tryMask mask2 key1 of
          Just False -> binOfMerges mask2 (wrap res1) l2 sNil r2
          Just True  -> binOfMerges mask2 sNil l2 (wrap res1) r2
          Nothing -> unrelated mask2 key1
    reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) v1 \v1' ->
      reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) v2 \v2' ->
        case (v1', v2') of
          (_, Nil) -> lift $ lift $ onOneSubtree one1 res1
          (Nil, _) -> lift $ lift $ onOneSubtree one2 res2
          (Bin mask1 l1 r1, Bin mask2 l2 r2)
            | mask1 == mask2 -> binOfMerges mask1 l1 l2 r1 r2
            | otherwise -> if countTrailingZeros mask1 >= countTrailingZeros mask2
              then oneContainsTwo mask1 mask2 l1 r1
              else twoContainsOne mask1 mask2 l2 r2
          (Bin mask1 l1 r1, Tip key2 _) -> oneContainsTwo mask1 key2 l1 r1
          (Tip key1 _, Bin mask2 l2 r2) -> twoContainsOne key1 mask2 l2 r2
          (Tip key1 l, Tip key2 r)
            | key1 == key2 -> mkTip unwrap key1 =<< mergeTree l r
            | otherwise -> unrelated key1 key2
  let mergeTree (RadixTree k1 s1) (RadixTree k2 s2) =
        RadixTree
          <$> stratMerge strat mergeVal k1 k2
          <*> stratMerge strat mergeChunk s1 s2
  pure \a b -> runReduce' @"2" $ runReduce' @"1" $ mergeTree a b

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
selEq k =
  let k' = toRadixKey k
  in SelEqT k'

-- I'm writing this for the forth time or something.
-- Me, please, DO NOT DELETE THIS.
newtype RevList a = UnsafeRevList [a]

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

data family SelChoose k t -- access existing value by choosing

data instance SelChoose k STree = SelChooseT
data instance SelChoose k SChunk = SelChooseC

-- I don't agree with how it is, but True refers to the left option
-- and False refers to the right option of Choose.
-- Why? I don't know.
instance Has (FreshIO :+: Reduce :+: NonDet) sig m => Selector SelChoose m where
  selTree SelChooseT valM = do
    now <- send Choose
    if now
      then do
        exists <- isJust <$> fetchC valM
        unless exists E.empty
        pure Nothing
      else pure $ Just SelChooseC
  selBin self _ = do
    left <- send Choose
    pure $ Just (not left, self)
  selTip SelChooseC _chunk = pure $ Just SelChooseT
  selNil _ = E.empty

selChoose :: SelChoose k STree
selChoose = SelChooseT

min :: Monad m => NonDetC m a -> m (Maybe a)
min = runNonDet
  (\l r -> l >>= \case
    Nothing -> r
    l' -> pure l')
  (pure . Just)
  (pure Nothing)

max :: Monad m => NonDetC m a -> m (Maybe a)
max = runNonDet
  (\l r -> r >>= \case
    Nothing -> l
    r' -> pure r')
  (pure . Just)
  (pure Nothing)

-- construction

empty :: Container c => RadixTree c k a
empty = RadixTree sNothing sNil

fromListM :: forall c sig m k v. (Has FreshIO sig m, Container c, IsRadixKey k) => [(k, v)] -> m (RadixTree c k v)
fromListM = foldM (\t (k, v) -> insert (selEq k) v t) empty

toListM :: forall c sig m k v. (Has FreshIO sig m, Container c, IsRadixKey k) => RadixTree c k v -> m [(k, v)]
toListM = fmap catMaybes . runNonDetA . lookupKV selChoose

-- aliases

type Map = RadixTree
type MapR = Map Res
type Set = RadixTree
type SetR k = MapR k ()

-- debug

-- Stupid String-based show for debug
tryFetchShow :: (Container c, Show a) => c a -> String
tryFetchShow = maybe "<>" show . tryFetchC

instance (Container c, Show a) => Show (RadixTree c k a) where
  show (RadixTree val chunk) = "(RadixTree (" <> tryFetchShow val <> ") " <> tryFetchShow chunk <> ")"
instance (Container c, Show a) => Show (RadixChunk' c k a) where
  show = \case
    Nil -> "Nil"
    Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
    Bin mask l r -> "(Bin " <> show mask <> " " <> tryFetchShow l <> " " <> tryFetchShow r <> ")"
