{-# LANGUAGE RecursiveDo, PatternSynonyms #-}
module Dentrado.POC.Data.RadixTree where
import RIO hiding (mask, toList, catch)
import Data.Bits
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
import Control.Carrier.NonDet.Church (runNonDet, NonDetC)
import RIO.List (uncons)

$(moduleId 1)

-- TODO: here, many type annotations reference WriterC Reduced. Probably this could be avoided, if it even should be?

type Chunk = Word32

class IsRadixKey key where
  toRadixKey :: key -> [Chunk]
  -- fromRadixKey :: [Chunk] -> key

instance IsRadixKey [Chunk] where
  toRadixKey = id

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

sNil :: Container c => c (RadixChunk c k a)
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

internalLookup :: (Selector sel m, Container c, Has (FreshIO :+: Reduce) sig m) => (RevList Chunk -> sel k SChunk -> c (RadixChunk c k a) -> m (m (Maybe a)), RevList Chunk -> sel k STree -> RadixTree c k a -> m (m (Maybe a)))
internalLookup = accessRadix
  (\_ -> id)
  (\_ (RadixTree a _) -> fetchC a)
  (\_ _ _ -> pure Nothing)
  (\_ -> id)
  (\_ _ _ -> id)
{-# INLINE internalLookup #-}

lookup :: (Selector sel (ReduceC m), Has FreshIO sig m) => Container c => sel k STree -> RadixTree c k a -> m (Maybe a)
lookup k tr = runReduce $ join $ snd internalLookup [] k tr

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

empty :: Container c => RadixTree c k a
empty = RadixTree sNothing sNil

sEmpty :: Container c => c (RadixTree c k a)
sEmpty = $sRunEvalFresh $ allocC empty

-- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

data OnOne c other fin = OnOne
  { onOneVal :: !(Res (Maybe other) -> other -> FreshIOC (Res (Maybe fin))) -- other must be unwrapped for this conclusion
  , onOneSubtree :: !(forall k. Res (RadixChunk c k other) -> FreshIOC (Res (RadixChunk c k fin))) }
newtype OnBoth one two fin = OnBoth
  { onBothVal :: Res (Maybe one) -> one -> Res (Maybe two) -> two -> FreshIOC (Res (Maybe fin)) }
newtype MergeStrategy c = MergeStrategy
  { _apply :: forall x y z. Res (Res x -> Res y -> Reduce'C "1" (Reduce'C "2" FreshIOC) (Res z)) -> c x -> c y -> Reduce'C "1" (Reduce'C "2" FreshIOC) (c z) }

merge :: forall one two fin c k. forall sig1 m1. (Container c, Has FreshIO sig1 m1, MonadFix m1)
  => MergeStrategy c
  -> OnOne c one fin
  -> OnOne c two fin
  -> OnBoth one two fin
  -> m1 (RadixTree c k one
    -> RadixTree c k two
    -> FreshIOC (RadixTree c k fin))
merge (MergeStrategy apply) one1 one2 both = mdo
  mergeVal <- alloc \r1 r2 -> do
    v1 <- fetch r1
    v2 <- fetch r2
    lift $ lift $ case (v1, v2) of
      (Just a , Just b ) -> onBothVal both r1 a r2 b
      (Just a , Nothing) -> onOneVal one1 r1 a
      (Nothing, Just b ) -> onOneVal one2 r2 b
      (Nothing, Nothing) -> pure sNothing
  let unsafeMask = \case
        Nil -> error "impossible"
        Tip mask _ -> mask
        Bin mask _ _ -> mask
  mergeChunk <- alloc \res1 res2 -> do
    v1 <- fetch res1
    v2 <- fetch res2
    reducible' (Proxy @"1") (reduceChunk' (Proxy @"1")) v1 \v1' ->
      reducible' (Proxy @"2") (reduceChunk' (Proxy @"2")) v2 \v2' ->
        case (v1', v2') of
          (_, Nil) -> lift $ lift $ onOneSubtree one1 res1
          (Nil, _) -> lift $ lift $ onOneSubtree one2 res2
          (Bin mask1 l1 r1, Bin mask2 l2 r2)
            | mask1 == mask2 -> do
              a <- apply mergeChunk l1 l2
              b <- apply mergeChunk r1 r2
              mkBin unwrap True mask1 a b
          (Bin mask1 l1 r1, unsafeMask -> mask2)
            | Just pickRight <- tryMask mask1 mask2
              -> if pickRight
                  then do
                    a <- apply mergeChunk l1 sNil
                    b <- apply mergeChunk r1 (wrap res2)
                    mkBin unwrap True mask1 a b
                  else do
                    a <- apply mergeChunk l1 (wrap res2)
                    b <- apply mergeChunk r1 sNil
                    mkBin unwrap True mask1 a b
          (unsafeMask -> mask1, Bin mask2 l2 r2)
            | Just pickRight <- tryMask mask2 mask1
              -> if pickRight
                  then do
                    a <- apply mergeChunk sNil l2
                    b <- apply mergeChunk (wrap res1) r2
                    mkBin unwrap True mask1 a b
                  else do
                    a <- apply mergeChunk (wrap res1) l2
                    b <- apply mergeChunk sNil r2
                    mkBin unwrap True mask1 a b
          (Tip mask1 l, Tip mask2 r)
            | mask1 == mask2 -> mkTip unwrap mask1 =<< mergeTree l r
          (unsafeMask -> mask1, unsafeMask -> mask2) -> do
            let (mask, pickRight) = makeMask mask1 mask2
            a <- lift $ lift $ onOneSubtree one1 res1
            b <- lift $ lift $ onOneSubtree one2 res2
            mkBin unwrap pickRight mask (wrap a) (wrap b)
  let mergeTree (RadixTree k1 s1) (RadixTree k2 s2) =
        RadixTree
          <$> apply mergeVal k1 k2
          <*> apply mergeChunk s1 s2
  pure \a b -> runReduce' @"2" $ runReduce' @"1" $ mergeTree a b


-- merge = runWriter @(Reduced' "one") (\_ -> pure) $ runWriter @(Reduced' "two") (\_ -> pure) $ getCompose $ mergeTree [] a b where
--   merger = _
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = _
-- valid, but non-streaming
-- merge :: forall f c one two fin. (Applicative f, Container c)
--   => OnOne f one fin
--   -> OnOne f two fin
--   -> OnBoth f one two fin
--   -> RadixTree c k one
--   -> RadixTree c k two
--   -> f (RadixTree c k fin)
-- merge one1 one2 match = \a b -> runIdentity $ runWriter @(Reduced' "one") (\_ -> pure) $ runWriter @(Reduced' "two") (\_ -> pure) $ getCompose $ mergeTree [] a b where
--   mergeVal p v1M v2M = Compose do
--     v1 <- extract' (Proxy @"one") v1M
--     v2 <- extract' (Proxy @"two") v2M
--     pure case (v1, v2) of
--       (Just a , Just b ) -> onBothVal match p a b
--       (Just a , Nothing) -> onOneVal one1 p a
--       (Nothing, Just b ) -> onOneVal one2 p b
--       (Nothing, Nothing) -> pure Nothing
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = RadixTree <$> (construct <$> mergeVal p v1 v2) <*> mergeChunk p s1 s2
--   mergeChunk p s1RM s2RM = Compose do
--     s1R <- extract' (Proxy @"one") s1RM
--     s2R <- extract' (Proxy @"two") s2RM
--     reducible' (Proxy @"one") (reduceChunk' (Proxy @"one")) s1R \s1 ->
--       reducible' (Proxy @"two") (reduceChunk' (Proxy @"two")) s2R \s2 ->
        -- _
-- mergeVal = construct \p v1 v2 -> case (v1, v2) of
--   (Just a , Just b ) -> runIdentity $ onBothVal both p a b
--   (Just a , Nothing) -> runIdentity $ onOneVal one1 p a
--   (Nothing, Just b ) -> runIdentity $ onOneVal one2 p b
--   (Nothing, Nothing) -> Nothing

-- sMerge :: Container c
--   => OnOne Identity one fin
--   -> OnOne Identity two fin
--   -> OnBoth Identity one two fin
--   -> RadixTree c k one
--   -> RadixTree c k two
--   -> RadixTree c k fin
-- sMerge one1 one2 both = mergeTree [] where
--   mergeTree p (RadixTree v1 s1) (RadixTree v2 s2) = RadixTree (mergeVal <*> p <*> v1 <*> v2) _

-- TODO: monadic... monadic

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
