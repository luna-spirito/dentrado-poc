{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
module Dentrado.POC.Data.RadixZipper where
import RIO hiding (mask, toList, catch)
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Dentrado.POC.Data.RadixTree (RadixChunk, Chunk, RadixTree)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Effect.Fresh (Fresh)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC)

$(moduleId 2)

data InvRadixTree c a
  = InvRadixCons !(c (Maybe a)) !(c (InvRadixChunk c a)) !(c (InvRadixTree c a))
  | InvRadixNil
type InvRadixChunk c a = Reducible (InvRadixChunk' c a)
data InvRadixChunk' c a
  = ITop
  | IBin !Bool !Chunk !(c (InvRadixChunk c a)) !(c (RadixChunk c a)) -- Bool stands or if the taken path is right

data RadixZipper c a = RadixZipper { radixPathToChunk :: ![Chunk], radixSuper :: !(c (InvRadixTree c a)), radixSub :: !(c (RadixTree c a)) }

reduceInvChunk :: (Container c, Has (Writer Reduced) sig m) => InvRadixChunk' c a -> m (InvRadixChunk' c a)
reduceInvChunk = \case
  IBin _ _ (tryExtract -> Just (readReducible -> supertree)) (tryExtract -> Just (readReducible -> RT.Nil)) -> tell (Reduced' @"" True) $> supertree
  nonReducible -> pure nonReducible

accessInvRadix :: forall c a invtree sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => invtree -- ^ impossible, on missing super invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> invtree) -- ^ on skip invchunk
  -> (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> invtree) -- ^ on invchunk
  -> [Chunk] -- current full path
  -> Int
  -> InvRadixTree c a
  -> m invtree
accessInvRadix onMissingInvTree onSkip onInvchunk =
  let
    goTree :: [Chunk] -> Int -> InvRadixTree c a -> m invtree
    goTree _  _ InvRadixNil = pure onMissingInvTree
    goTree [] _ _           = pure onMissingInvTree
    goTree _ 0 (InvRadixCons el invchunk superInvchunks) = pure $ onInvchunk el invchunk superInvchunks
    goTree (x:xs) n (InvRadixCons el invchunk superInvchunks) = onSkip x el invchunk <$> (goTree xs (n-1) =<< extract superInvchunks)
  in goTree . reverse
{-# INLINE accessInvRadix #-}

accessInvChunk :: forall c invchunk a sig m. (Container c, Has (Fresh :+: Writer Reduced) sig m)
  => (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> invchunk) -- ^ on super
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> invchunk) -- ^ on sub
  -> Chunk -- key
  -> Chunk -- ex key
  -> c (InvRadixChunk c a)
  -> m invchunk
accessInvChunk onSuper onSub key =
  let
    goChunk :: Chunk -> c (InvRadixChunk c a) -> m invchunk
    goChunk exKey chunkM =
      let
        newBranch :: invchunk
        newBranch =
          let (mask, placeRight) = RT.makeMask exKey key
          in onSub (not placeRight) mask chunkM RT.sNil
      in extract chunkM >>= \chunk -> reducible reduceInvChunk chunk \case
        ITop -> pure newBranch
        IBin pickRight mask super sub
          | Just wasRight <- RT.tryMask mask key ->
            if wasRight == pickRight -- we're guided the same way we came
              then pure newBranch
              else pure $ onSub pickRight mask super sub
          | otherwise -> onSuper pickRight mask sub <$> goChunk mask super
  in goChunk
{-# INLINE accessInvChunk #-}

accessRadixZipper :: forall c a chunk invchunk invtree tree zipper sig m. (Container c, Has Fresh sig m)
  => ([Chunk] -> c (InvRadixTree c a) -> tree -> zipper) -- ^ on sub, zipper
  -> (Chunk -> [Chunk] -> c (RadixChunk c a) -> chunk)
  -> ([Chunk] -> RadixTree c a -> tree)
  -> ([Chunk] -> c (RadixTree c a) -> invtree -> zipper) -- ^ on super, zipper
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> invtree -> invtree) -- ^ on super skip, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> invtree) -- ^ on found value, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixTree c a) -> invchunk -> invtree) -- ^ on found invchunk, invtree
  -> (Bool -> Chunk -> c (RadixChunk c a)    -> invchunk -> invchunk) -- ^ on super, invchunk
  -> (Bool -> Chunk -> c (InvRadixChunk c a) -> chunk    -> invchunk) -- ^ on sub, invchunk
  --
  -> [Chunk]
  -> RadixZipper c a
  -> m zipper
accessRadixZipper onSub onChunk onTree onSuper onSkip onFoundValue onFoundInvchunk onSuperInvchunk onSubInvchunk absPath zipper = nonRe
  let
    diffFor (x:xs) (y:ys)
      | x == y = diffFor xs ys
    diffFor p1 p2 = (p1, p2)
    (backSteps, relPath) = diffFor zipper.radixPathToChunk absPath
  in case backSteps of
    [] -> onSub zipper.radixPathToChunk zipper.radixSuper . onTree relPath <$> extract zipper.radixSub
    (exKey:_) -> do
      radixSuper' <- extract zipper.radixSuper
      invRadix' <- join $ accessInvRadix
        (error "impossible")
        (\a b c d -> onSkip a b c <$> d)
        (\val chunk super -> case relPath of
          [] -> pure $ onFoundValue exKey val chunk super
          (key:keys) -> onFoundInvchunk exKey val super <$> accessInvChunk
            onSuperInvchunk
            (\a b c d -> onSubInvchunk a b c $ onChunk key keys d)
            key exKey chunk)
        zipper.radixPathToChunk
        (length backSteps - 1)
        radixSuper'
      pure $ onSuper zipper.radixPathToChunk zipper.radixSub invRadix'
{-# INLINE accessRadixZipper #-}

mkIBinNonRe :: Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> InvRadixChunk' c a
mkIBinNonRe = IBin
{-# INLINE mkIBinNonRe #-}

mkIBin :: (Container c, Has (Writer Reduced) sig m) => Bool -> Chunk -> c (InvRadixChunk c a) -> c (RadixChunk c a) -> m (InvRadixChunk' c a)
mkIBin a b c d = reduceInvChunk $ mkIBinNonRe a b c d

lookup :: (Container c, Has Fresh sig m) => [Chunk] -> RadixZipper c a -> m (Maybe a)
lookup keys zipper = nonRe =<< accessRadixZipper
  (\_ _ -> id)
  (\a b c -> join $ fst RT.internalLookup a b c)
  (\a b -> join $ snd RT.internalLookup a b)
  (\_ _ -> id)
  (\_ _ _ -> id)
  (\_ val _ _ -> extract val)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  keys zipper

insert :: (Container c, Has Fresh sig m) => [Chunk] -> a -> RadixZipper c a -> m (RadixZipper c a)
insert path val zipper = nonRe =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (construct =<< c))
  (\a b c -> join $ fst (RT.internalInsert val) a b c)
  (\a b -> join $ snd (RT.internalInsert val) a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (construct =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (construct =<< c))
  (\_tipOfSkipped _ b c -> (\val' -> InvRadixCons val' b c) <$> construct (Just val))
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    construct $ mkReducible $ mkIBinNonRe a b d' c)
  (\a b c d -> construct . mkReducible . mkIBinNonRe a b c =<< d)
  path zipper

delete :: (Container c, Has Fresh sig m) => [Chunk] -> RadixZipper c a -> m (RadixZipper c a)
delete path zipper = nonRe =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (construct =<< c))
  (\a b c -> join $ fst RT.internalDelete a b c)
  (\a b -> join $ snd RT.internalDelete a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (construct =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (construct =<< c))
  (\_tipOfSkipped _deleted b c -> pure $ InvRadixCons sNothing b c)
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    construct . mkReducible =<< mkIBin a b d' c)
  (\a b c d -> construct . mkReducible =<< mkIBin a b c =<< d)
  path
  zipper

sITop :: Container c => c (InvRadixChunk c a)
sITop = $sRunEvalFresh $ construct $ mkReducible ITop

focus :: forall c a sig m. Has Fresh sig m => Container c => [Chunk] -> RadixZipper c a -> m (RadixZipper c a)
focus targetPath =
  let
    applyNM :: forall m1 a1. Monad m1 => Int -> (a1 -> m1 a1) -> a1 -> m1 a1
    applyNM 0 _ x = pure x
    applyNM n f x = applyNM (n-1) f =<< f x

    -- focusRadix :: Chunk -> [Chunk] -> c (RadixChunk c a) -> m (c (Maybe a) -> c (InvRadixChunk c a) -> c (InvRadixTree c a) -> m (RadixZipper c a))
    focusRadix = --fst $
      let onTipInv topval invchunk invtree = construct $ InvRadixCons topval invchunk invtree
      in RT.accessRadix
        (\val chunk -> chunk val sITop)
        (\rt invtree -> RadixZipper targetPath invtree <$> construct rt) -- on found, tree
        (\_key1 (length -> leftToPass) topval invchunk invtree -> do -- on missing
          super' <- applyNM leftToPass
            (construct . InvRadixCons sNothing sITop) -- add empty trees 'length keys2' times
            =<< onTipInv topval invchunk invtree -- finish this chunk
          pure $ RadixZipper -- on missing
            targetPath
            super'
            RT.sEmpty)
        (\_key tree topval invchunk invtree -> tree =<< onTipInv topval invchunk invtree)
        (\pickRight mask other picked topval invchunk invtree -> (\invchunk' -> picked topval invchunk' invtree) =<< construct . mkReducible =<< mkIBin pickRight mask invchunk other)

    revInvChunk :: Chunk -> RadixTree c a -> c (Maybe a) -> c (InvRadixChunk c a) -> WriterC Reduced m (RadixTree c a)
    revInvChunk chunkName oldTree topval oldInvchunk =
      let
        revInvChunk' :: c (RadixChunk c a) -> c (InvRadixChunk c a) -> WriterC Reduced m (RadixTree c a)
        revInvChunk' chunk invchunk = do
          invchunk' <- extract invchunk
          reducible reduceInvChunk invchunk' \case
            ITop -> pure $ RT.RadixTree topval chunk
            IBin pickRight mask super other -> (`revInvChunk'` super) =<< construct . mkReducible =<< RT.mkBin pickRight mask other chunk
      in (`revInvChunk'` oldInvchunk) =<< construct . mkReducible =<< RT.mkTip chunkName oldTree
  in nonRe <=< accessRadixZipper
    (\_ initialInvT tree -> tree initialInvT) -- on sub, zipper
    (\k ks chunk topval invchunk invtree ->
      fst focusRadix k ks chunk >>= \f -> f topval invchunk invtree)
    (\ks tree invtree ->
      snd focusRadix ks tree >>= \f -> f invtree)
    (\_ initialT invtree -> invtree =<< extract initialT) -- on super, zipper
    --   -- when we go up, we save the initial tree in a Tip. So eventually it needs to be extracted, unfortunately
    --   -- alternatively, we could save pointer on Tip, but the problem doesn't sound to worth it
    (\key topval invchunk invtree tree -> invtree =<< revInvChunk key tree topval invchunk) -- on skip
    (\key topval invchunk invtreeM oldTree -> -- on found value, invtree
      RadixZipper targetPath invtreeM <$> (construct =<< revInvChunk key oldTree topval invchunk))
    (\key topval invtree invchunk rt -> invchunk topval invtree =<< construct . mkReducible =<< RT.mkTip key rt)
    (\pickRight mask other super topval invtree chunk -> super topval invtree =<< construct . mkReducible =<< RT.mkBin pickRight mask other chunk) -- on super, invchunk
    (\pickRight mask super other topval invtree chunk -> (\invchunk' -> other topval invchunk' invtree)  =<< construct . mkReducible =<< mkIBin (not pickRight) mask super chunk) -- on sub, invchunk
    targetPath

empty :: Container c => RadixZipper c a
empty = RadixZipper [] ($sRunEvalFresh $ construct InvRadixNil) RT.sEmpty

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

showRadixZipperLookup :: forall c a sig m. (Container c, Show a, Has Fresh sig m) => [Chunk] -> RadixZipper c a -> m String
showRadixZipperLookup = showRadixZipperLookup' where
  showRadixLookup :: (Chunk -> [Chunk] -> c (RadixChunk c a) -> WriterC Reduced m String, [Chunk] -> RadixTree c a -> WriterC Reduced m String)
  showRadixLookup = RT.accessRadix
    (\val chunk -> "(onSubT " <> RT.tryExtractShow val <> " " <> chunk <> ")")
    (\rt -> "(onFoundT " <> show rt <> ")")
    (\key keys -> "(onMissingC " <> show key <> " " <> show keys <>")")
    (\key tree -> "(onTipC " <> show key <> " " <> tree <> ")")
    (\pickRight mask other curr -> "(onBranchC " <> show pickRight <> " " <> show mask <> "" <> RT.tryExtractShow other <> " " <> curr <> ")")

  showRadixZipperLookup' path zipper = nonRe =<< accessRadixZipper
    (\k v t -> t <&> \t' -> "(onSubZ " <> show k <> " " <> RT.tryExtractShow v <> " " <> t' <> ")")
    (fst showRadixLookup)
    (snd showRadixLookup)
    (\k v t -> t <&> \t' -> "(onSuperZ" <> " " <> show k <> " " <> RT.tryExtractShow v <> " " <> t' <> ")")
    (\k v ic it -> it <&> \it' -> "(onSkipIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow ic <> " " <> it' <> ")")
    (\k v ic it -> pure $ "(onFoundIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow ic <> " " <> RT.tryExtractShow it <> ")")
    (\k v it ic -> ic <&> \ic' -> "(onFoundInvchunkIT " <> show k <> " " <> RT.tryExtractShow v <> " " <> RT.tryExtractShow it <> " " <> ic' <> ")")
    (\pickRight mask other super -> super <&> \super' ->"(onSuperIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryExtractShow other <> " " <> super' <> ")")
    (\pickRight mask super other -> other <&> \other' -> "(onSubIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryExtractShow super <> " " <> other' <> ")")
    path zipper

