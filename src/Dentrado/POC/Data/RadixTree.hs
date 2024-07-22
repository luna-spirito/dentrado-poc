module Dentrado.POC.Data.RadixTree where
import RIO hiding (mask, toList, catch)
import Data.Bits
import Control.Algebra
import Data.Monoid (Any(..))
import Control.Effect.Writer
import Dentrado.POC.Data.Container

type Chunk = Word32

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

-- TODO: Implement Zebra simply by adding metadata field to Nil
-- Justification: RadixTree stores discrete and continuous data,
-- with discrete data being saved in Tip and continuous data being
-- saved in Nil. Typically the only continuous data that we work with
-- is "there's nothing here in this continuous region".
-- But this could be repurposed to store more cases.
data RadixTree c a = RadixTree !(c (Maybe a)) !(c (RadixChunk c a)) -- both element and next is containerized, both can be left unwrapped.
type RadixChunk c a = Reducible (RadixChunk' c a)
data RadixChunk' c a
  = Nil
  | Tip !Chunk !(RadixTree c a) -- There's no way you access Tip and don't want to know what's coming next, so no containerization
  | Bin !Chunk !(c (RadixChunk c a)) !(c (RadixChunk c a)) -- Either branch can be accessed, so containerization

-- -- TODO: Don't know how effective is this
reduceChunk :: (Container c, Has (Writer Any) sig m) => RadixChunk' c a -> m (RadixChunk' c a)
reduceChunk = \case
  Tip _ (RadixTree (tryExtract -> Just Nothing) (tryExtract -> Just (readReducible -> Nil))) -> tell (Any True) $> Nil
  Bin _ (tryExtract -> Just (readReducible -> left)) (tryExtract -> Just (readReducible -> right))
    | Nil <- left -> tell (Any True) $> right -- hopefully no need to reduceChunk left/right
    | Nil <- right -> tell (Any True) $> left
  nonReducible -> pure nonReducible

-- -- Let's make accessRadix and accessRadix1?
accessRadix1 :: forall c a tree chunk. forall sig m. (Container c, Has (Writer Any) sig m)
  => (forall sig1 m1. Has (Writer Any) sig1 m1 => c (Maybe a) -> chunk -> m1 tree) -- ^ on sub, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => RadixTree c a -> m1 tree) -- ^ on found, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> m1 chunk) -- ^ on missing, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> tree -> m1 chunk) -- ^ on Tip, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Bool -> Chunk -> c (RadixChunk c a) -> chunk -> m1 chunk) -- ^ on branch, chunk
  -> Chunk
  -> [Chunk]
  -> c (RadixChunk c a)
  -> m chunk
accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC =
  let
    goChunk :: forall. forall sig m. Has (Writer Any) sig m => Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    goChunk key keys chunkM =
      let
        newBranch :: forall sig m. Has (Writer Any) sig m => Chunk -> m chunk
        newBranch exKey =
          let (mask, placeRight) = makeMask exKey key
          in onBranchC placeRight mask chunkM =<< onMissingC key keys
      in extract chunkM >>= \chunk -> reducible reduceChunk chunk \case
        Nil -> onMissingC key keys
        (Tip key2 subtree)
          | key == key2 -> onTipC key =<< goTree keys subtree
          | otherwise -> newBranch key2
        (Bin mask l r)
          | Just pickRight <- tryMask mask key
            -> onBranchC pickRight mask (if pickRight then l else r) =<< goChunk key keys (if pickRight then r else l)
          | otherwise -> newBranch mask
    goTree :: forall. forall sig m. Has (Writer Any) sig m => [Chunk] -> RadixTree c a -> m tree
    goTree [] = onFoundT
    goTree (key:keys) = \(RadixTree val chunk) -> onSubT val =<< goChunk key keys chunk
  in goChunk
{-# INLINE accessRadix1 #-}

-- TODO: use same m everywhere
-- Constructs both accessRadix1 and accessRadix versions
accessRadix :: forall c a tree chunk sig m. (Container c, Has (Writer Any) sig m)
  => (forall sig1 m1. Has (Writer Any) sig1 m1 => c (Maybe a) -> chunk -> m1 tree) -- ^ on sub, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => RadixTree c a -> m1 tree) -- ^ on found, tree
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> m1 chunk) -- ^ on missing, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> tree -> m1 chunk) -- ^ on Tip, chunk
  -> (forall sig1 m1. Has (Writer Any) sig1 m1 => Bool -> Chunk -> c (RadixChunk c a) -> chunk -> m1 chunk) -- ^ on branch, chunk
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk, [Chunk] -> RadixTree c a -> m tree)
accessRadix onSubT onFoundT onMissingC onTipC onBranchC =
  let
    var1 :: Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk
    var1 = accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC
  in (var1, \case
    [] -> onFoundT
    (key:keys) -> \(RadixTree val chunk) -> onSubT val =<< var1 key keys chunk
  )
  -- \case
  -- [] -> onFoundT
  -- (key:keys) -> \(RadixTree val chunk) -> onSubT val =<< accessRadix1 onSubT onFoundT onMissingC onTipC onBranchC key keys chunk
{-# INLINE accessRadix #-}

mkBinNonRe :: Container c => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> RadixChunk' c a
mkBinNonRe right mask a b = Bin mask (if right then a else b) (if right then b else a)
{-# INLINE mkBinNonRe #-}

mkBin :: (Container c, Has (Writer Any) sig m) => Bool -> Chunk -> c (RadixChunk c a) -> c (RadixChunk c a) -> m (RadixChunk' c a)
mkBin a b c d = reduceChunk $ mkBinNonRe a b c d
{-# INLINE mkBin #-}

internalLookup :: (Container c, Has (Writer Any) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (Maybe a), [Chunk] -> RadixTree c a -> m (Maybe a))
internalLookup = accessRadix
  (\_ -> pure)
  (\(RadixTree a _) -> extract a)
  (\_ _ -> pure Nothing)
  (\_ -> pure)
  (\_ _ _ -> pure)
{-# INLINE internalLookup #-}

lookup :: Container c => [Chunk] -> RadixTree c a -> Maybe a
lookup k tr = nonRe $ snd internalLookup k tr

internalInsert :: (Container c, Has (Writer Any) sig m) => a -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (c (RadixChunk c a)), [Chunk] -> RadixTree c a -> m (RadixTree c a))
internalInsert val = accessRadix
  (\a b -> pure $ RadixTree a b)
  (\(RadixTree _oldVal b) -> pure $ RadixTree (construct $ Just val) b)
  (\key1 keys2 -> pure $ snd $ foldr
    (\key sub -> (construct Nothing, construct $ mkReducible $ Tip key $ uncurry RadixTree sub))
    (construct (Just val), construct (mkReducible Nil))
    (key1:keys2))
  (\k v -> pure $ construct $ mkReducible $ Tip k v)
  (\k r a b -> pure $ construct $ mkReducible $ mkBinNonRe k r a b)
{-# INLINE internalInsert #-}

insert :: Container c => [Chunk] -> p -> RadixTree c p -> RadixTree c p
insert k v tr = nonRe $ snd (internalInsert v) k tr

internalDelete :: (Container c, Has (Writer Any) sig m) => (Chunk -> [Chunk] -> c (RadixChunk c a) -> m (c (RadixChunk c a)), [Chunk] -> RadixTree c a -> m (RadixTree c a))
internalDelete = accessRadix
  (\a b -> pure $ RadixTree a b) -- on sub, tree
  (\(RadixTree _deleted sub) -> pure $ RadixTree (construct Nothing) sub) -- on found, tree
  (\_key1 _keys2 -> pure $ construct $ mkReducible Nil) -- on missing, chunk
  (\key tree -> pure $ construct $ mkReducible $ Tip key tree) -- on Tip, chunk
  (\k r a b -> pure $ construct $ mkReducible $ nonRe $ mkBin k r a b) -- on branch, chunk
{-# INLINE internalDelete #-}

delete :: Container c => [Chunk] -> RadixTree c p -> RadixTree c p
delete k tr = nonRe $ snd internalDelete k tr

-- -- 

-- -- TODO: monadical extract, separate RadixTree and RadixZipper into different modules, `merge`, `adjust`

empty :: Container c => RadixTree c a
empty = RadixTree (construct Nothing) (construct $ mkReducible Nil)

-- debug

-- Stupid String-based show for debug
tryExtractShow :: (Container c, Show a) => c a -> String
tryExtractShow = maybe "<>" show . tryExtract

instance (Container c, Show a) => Show (RadixTree c a) where
  show (RadixTree val chunk) = "(RadixTree (" <> tryExtractShow val <> ") " <> tryExtractShow chunk <> ")"
instance (Container c, Show a) => Show (RadixChunk' c a) where
  show = \case
    Nil -> "Nil"
    Tip key val -> "(Tip " <> show key <> " " <> show val <> ")"
    Bin mask l r -> "(Bin " <> show mask <> " " <> tryExtractShow l <> " " <> tryExtractShow r <> ")"
