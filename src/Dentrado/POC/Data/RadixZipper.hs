{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Dentrado.POC.Data.RadixZipper where
import RIO hiding (mask, toList, catch)
import Control.Algebra
import Data.Monoid (Any(..))
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Dentrado.POC.Data.RadixTree (RadixChunk, Chunk, RadixTree)
import qualified Dentrado.POC.Data.RadixTree as RT

data InvRadixTree c a
  = InvRadixCons !(c (Maybe a)) !(c (InvRadixChunk c a)) !(c (InvRadixTree c a))
  | InvRadixNil
type InvRadixChunk c a = Reducible (InvRadixChunk' c a)
data InvRadixChunk' c a
  = ITop
  | IBin !Bool !Chunk !(c (InvRadixChunk c a)) !(c (RadixChunk c a)) -- Bool stands or if the taken path is right

data RadixZipper c a = RadixZipper { radixPathToChunk :: ![Chunk], radixSuper :: !(c (InvRadixTree c a)), radixSub :: !(c (RadixTree c a)) }

reduceInvChunk :: (Container c, Has (Writer Any) sig m) => InvRadixChunk' c a -> m (InvRadixChunk' c a)
reduceInvChunk = \case
  IBin _ _ (tryExtract -> Just (readReducible -> supertree)) (tryExtract -> Just (readReducible -> RT.Nil)) -> tell (Any True) $> supertree
  nonReducible -> pure nonReducible

accessInvRadix :: forall c a invtree sig m. (Container c, Has (Writer Any) sig m)
  => m invtree -- ^ impossible, on missing super invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> m invtree) -- ^ on skip invchunk
  -> (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> m invtree) -- ^ on invchunk
  -> [Chunk] -- current full path
  -> Int
  -> InvRadixTree c a
  -> m invtree
accessInvRadix onMissingInvTree onSkip onInvchunk =
  let
    goTree :: [Chunk] -> Int -> InvRadixTree c a -> m invtree
    goTree _  _ InvRadixNil = onMissingInvTree
    goTree [] _ _           = onMissingInvTree
    goTree _ 0 (InvRadixCons el invchunk superInvchunks) = onInvchunk el invchunk superInvchunks
    goTree (x:xs) n (InvRadixCons el invchunk superInvchunks) = onSkip x el invchunk =<< goTree xs (n-1) =<< extract superInvchunks
  in goTree . reverse
{-# INLINE accessInvRadix #-}

accessInvChunk :: forall c invchunk a sig m. (Container c, Has (Writer Any) sig m)
  => (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> m invchunk) -- ^ on super
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> m invchunk) -- ^ on sub
  -> Chunk -- key
  -> Chunk -- ex key
  -> c (InvRadixChunk c a)
  -> m invchunk
accessInvChunk onSuper onSub key =
  let
    goChunk :: Has (Writer Any) sig m => Chunk -> c (InvRadixChunk c a) -> m invchunk
    goChunk exKey chunkM =
      let
        newBranch :: Has (Writer Any) sig m => m invchunk
        newBranch =
          let (mask, placeRight) = RT.makeMask exKey key
          in onSub (not placeRight) mask chunkM (construct $ mkReducible RT.Nil)
      in extract chunkM >>= \chunk -> reducible reduceInvChunk chunk \case
        ITop -> newBranch
        IBin pickRight mask super sub
          | Just wasRight <- RT.tryMask mask key ->
            if wasRight == pickRight -- we're guided the same way we came
              then newBranch
              else onSub pickRight mask super sub
          | otherwise -> onSuper pickRight mask sub =<< goChunk mask super
  in goChunk
{-# INLINE accessInvChunk #-}

accessRadixZipper :: forall c a chunk invchunk invtree tree zipper. forall sig m. (Container c, Has (Writer Any) sig m)
  => ([Chunk] -> c (InvRadixTree c a) -> tree -> m zipper) -- ^ on sub, zipper
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> m chunk)
  -> ([Chunk] -> RadixTree c a -> m tree)
  -> ([Chunk] -> c (RadixTree c a) -> invtree -> m zipper) -- ^ on super, zipper
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> m invtree) -- ^ on super skip, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> m invtree) -- ^ on found value, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixTree c a) -> invchunk -> m invtree) -- ^ on found invchunk, invtree
  -> (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> m invchunk) -- ^ on super, invchunk
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> chunk    -> m invchunk) -- ^ on sub, invchunk
  --
  -> [Chunk]
  -> RadixZipper c a
  -> m zipper
accessRadixZipper onSub onChunk onTree onSuper onSkip onFoundValue onFoundInvchunk onSuperInvchunk onSubInvchunk absPath zipper =
  let
    diffFor (x:xs) (y:ys)
      | x == y = diffFor xs ys
    diffFor p1 p2 = (p1, p2)
    (backSteps, relPath) = diffFor zipper.radixPathToChunk absPath
  in case backSteps of
    [] -> onSub zipper.radixPathToChunk zipper.radixSuper =<< onTree relPath =<< extract zipper.radixSub
    (exKey:_) -> onSuper zipper.radixPathToChunk zipper.radixSub =<< accessInvRadix
      (error "imposible")
      onSkip
      (case relPath of
        [] -> onFoundValue exKey
        (key:keys) -> \val chunk super -> onFoundInvchunk exKey val super =<< accessInvChunk
          onSuperInvchunk
          (\a b c d -> onSubInvchunk a b c =<< onChunk key keys d)
          key exKey chunk)
      zipper.radixPathToChunk
      (length backSteps - 1)
      (nonRe (extract zipper.radixSuper))
{-# INLINE accessRadixZipper #-}

mkIBinNonRe :: Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> InvRadixChunk' c a
mkIBinNonRe = IBin
{-# INLINE mkIBinNonRe #-}

mkIBin :: (Container c, Has (Writer Any) sig m) => Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> m (InvRadixChunk' c a)
mkIBin a b c d = reduceInvChunk $ mkIBinNonRe a b c d

lookup :: Container c => [Chunk] -> RadixZipper c a -> Maybe a
lookup path zipper = nonRe $ accessRadixZipper
  (\_ _ -> pure)
  (fst RT.internalLookup)
  (snd RT.internalLookup)
  (\_ _ -> pure)
  (\_ _ _ -> pure)
  (\_ val _ _ -> extract val)
  (\_ _ _ -> pure)
  (\_ _ _ -> pure)
  (\_ _ _ -> pure)
  path zipper

insert :: Container c => [Chunk] -> a -> RadixZipper c a -> RadixZipper c a
insert path val zipper = nonRe $ accessRadixZipper
  (\a b c -> pure $ RadixZipper a b (construct c))
  (fst $ RT.internalInsert val)
  (snd $ RT.internalInsert val)
  (\a b c -> pure $ RadixZipper a (construct c) b)
  (\_tipOfSkipped a b c -> pure $ InvRadixCons a b $ construct c)
  (\_tipOfSkipped _ b c -> pure $ InvRadixCons (construct $ Just val) b c)
  (\_ a b c -> pure $ InvRadixCons a c b)
  (\a b c d -> pure $ construct $ mkReducible $ mkIBinNonRe a b d c)
  (\a b c d -> pure $ construct $ mkReducible $ mkIBinNonRe a b c d) -- (not a)?
  path zipper

delete :: Container c => [Chunk] -> RadixZipper c a -> RadixZipper c a
delete path zipper = nonRe $ accessRadixZipper
  (\a b c -> pure $ RadixZipper a b (construct c))
  (fst RT.internalDelete)
  (snd RT.internalDelete)
  (\a b c -> pure $ RadixZipper a (construct c) b)
  (\_tipOfSkipped a b c -> pure $ InvRadixCons a b $ construct c) -- on super skip, invtree
  (\_tipOfSkipped _deleted b c -> pure $ InvRadixCons (construct Nothing) b c) -- on found invchunk, invtree
  (\_ a b c -> pure $ InvRadixCons a c b)
  (\a b c d -> pure $ construct $ mkReducible $ nonRe $ mkIBin a b d c)
  (\a b c d -> pure $ construct $ mkReducible $ nonRe $ mkIBin a b c d)
  path
  zipper

focus :: forall c a. Container c => [Chunk] -> RadixZipper c a -> RadixZipper c a
focus targetPath =
  let
    applyN 0 _ x = x
    applyN n f x = applyN (n-1) f (f x)

    -- focusRadix1 :: forall sig1 m1. Has (Writer Any) sig1 m1 => Chunk -> [Chunk] -> c (RadixChunk c a) -> m1 (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> RadixZipper c a)
    focusRadix =
      let onTipInv topval invchunk invtree = construct $ InvRadixCons topval invchunk invtree in
      RT.accessRadix
        (\val chunk -> pure $ chunk val $ construct $ mkReducible ITop) -- on sub, tree
        (\rt -> pure \b -> RadixZipper targetPath b $ construct rt) -- on found, tree
        (\_key1 (length -> leftToPass) -> pure \topval invchunk invtree -> RadixZipper -- on missing
            targetPath
            (applyN leftToPass
              (construct . InvRadixCons (construct Nothing) (construct $ mkReducible ITop)) -- add empty trees 'length keys2' times
              (onTipInv topval invchunk invtree)) -- finish this chunk
            (construct $ RT.RadixTree (construct Nothing) (construct $ mkReducible RT.Nil)))
        (\_key tree -> pure \topval invchunk invtree -> tree (onTipInv topval invchunk invtree)) -- on Tip
        (\pickRight mask other picked -> pure \topval invchunk -> picked topval (construct $ mkReducible $ IBin pickRight mask invchunk other))

    revInvChunk :: Chunk -> RadixTree c a -> c (Maybe a) -> c (InvRadixChunk c a) -> RadixTree c a
    revInvChunk chunkName oldTree topval oldInvchunk =
      let
        revInvChunk' :: c (RadixChunk c a) -> c (InvRadixChunk c a) -> RadixTree c a
        revInvChunk' chunk = (readReducible . nonRe . extract) >>> \case
          ITop -> RT.RadixTree topval chunk
          IBin pickRight mask super other -> revInvChunk' (construct $ mkReducible $ nonRe $ RT.mkBin pickRight mask other chunk) super
      in revInvChunk' (construct $ mkReducible $ RT.Tip chunkName oldTree) oldInvchunk
  in
    nonRe . accessRadixZipper
      (\_ initialInvT tree -> pure $ tree initialInvT) -- on sub, zipper
      (fst focusRadix)
      (snd focusRadix)
      (\_ initialT invtree -> pure $ invtree (nonRe $ extract initialT)) -- on super, zipper
      -- when we go up, we save the initial tree in a Tip. So eventually it needs to be extracted, unfortunately
      -- alternatively, we could save pointer on Tip, but the problem doesn't sound to worth it
      (\key topval invchunk invtree -> pure \tree -> invtree $ revInvChunk key tree topval invchunk) -- on skip
      (\key topval invchunk invtreeM -> pure \oldTree -> -- on found value, invtree
        RadixZipper targetPath invtreeM (construct $ revInvChunk key oldTree topval invchunk))
      (\key topval invtree invchunk -> pure $ invchunk topval invtree . construct . mkReducible . RT.Tip key) -- on found invchunk, invtree
      (\pickRight mask other super -> pure \topval invtree chunk -> super topval invtree (construct $ mkReducible $ nonRe $ RT.mkBin pickRight mask other chunk)) -- on super, invchunk
      (\pickRight mask super other -> pure \topval invtree chunk -> other topval (construct $ mkReducible $ nonRe $ mkIBin (not pickRight) mask super chunk) invtree) -- on sub, invchunk
      targetPath

empty :: Container c => RadixZipper c a
empty = RadixZipper [] (construct InvRadixNil) (construct RT.empty)

-- debug

instance (Container c, Show a) => Show (InvRadixTree c a) where
  show = \case
    InvRadixNil -> "InvRadixNil"
    InvRadixCons topval super other -> "(InvRadixCons (" <> RT.tryExtractShow topval <> ") " <> RT.tryExtractShow super <> " " <> RT.tryExtractShow other <> ")"
instance (Container c, Show a) => Show (InvRadixChunk' c a) where
  show = \case
    ITop -> "ITop"
    IBin pickRight mask super other -> "(IBin " <> show pickRight <> " " <> show mask <> " " <> RT.tryExtractShow super <> " " <> RT.tryExtractShow other <> ")"
instance (Container c, Show a) => Show (RadixZipper c a) where
  show (RadixZipper a b c) = "RADIX ZIPPER:\n" <> show a <> "\n" <> RT.tryExtractShow b <> "\n" <> RT.tryExtractShow c

showRadixZipperLookup :: (Container c, Show a) => [Chunk] -> RadixZipper c a -> String
showRadixZipperLookup = showRadixZipperLookup' where
  showRadixLookup = RT.accessRadix
    (\val chunk -> pure $ "(onSubT " <> RT.tryExtractShow val <> " " <> chunk <> ")")
    (\rt -> pure $ "(onFoundT " <> show rt <> ")")
    (\key keys -> pure $ "(onMissingC " <> show key <> " " <> show keys <>")")
    (\key tree -> pure $ "(onTipC " <> show key <> " " <> tree <> ")")
    (\pickRight mask other curr -> pure $ "(onBranchC " <> show pickRight <> " " <> show mask <> "" <> RT.tryExtractShow other <> " " <> curr <> ")")
  showRadixZipperLookup' path zipper = nonRe $ accessRadixZipper
    (\k v t -> pure $ "(onSubZ " <> show k <> " " <> RT.tryExtractShow v <> " " <> t <> ")")
    (fst showRadixLookup)
    (snd showRadixLookup)
    (\k v t -> pure $ "(onSuperZ" <> " " <> show k <> " " <> RT.tryExtractShow v <> " " <> t <> ")")
    (\k v ic it -> pure $ "(onSkipIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow ic <> " " <> it <> ")")
    (\k v ic it -> pure $ "(onFoundIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow ic <> " " <> RT.tryExtractShow it <> ")")
    (\k v it ic -> pure $ "(onFoundInvchunkIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow it <> " " <> ic <> ")")
    (\pickRight mask other super -> pure $ "(onSuperIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryExtractShow other <> " " <> super <> ")")
    (\pickRight mask super other -> pure $ "(onSubIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryExtractShow super <> " " <> other <> ")")
    path
    zipper
 
 
