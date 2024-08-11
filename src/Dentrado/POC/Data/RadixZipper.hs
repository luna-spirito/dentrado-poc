{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use uncurry" #-}
{-# LANGUAGE DeriveFunctor #-}
{-# HLINT ignore "Use if" #-}
module Dentrado.POC.Data.RadixZipper where
import RIO hiding (mask, toList, catch)
import Control.Algebra
import Control.Effect.Writer
import Dentrado.POC.Data.Container
import Dentrado.POC.Data.RadixTree (RadixChunk, Chunk, RadixTree)
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Effect.Fresh (Fresh)
import Dentrado.POC.TH (moduleId, sRunEvalFresh)
import Control.Carrier.Writer.Church (WriterC, runWriter)
import Data.Monoid (First(..))
import qualified Control.Applicative as A
import Control.Monad.Free
import Data.Functor.Compose
import Control.Effect.NonDet (NonDet)
import Control.Effect.Labelled (HasLabelled, sendLabelled, Labelled, runLabelled)
import Control.Effect.Choose (Choose(..))
import Control.Effect.Empty (Empty (..))
import GHC.Base (Type)
import Data.Coerce (coerce)
import Control.Effect.Sum (inj)
import GHC.IsList (fromList, toList)
import Control.Carrier.NonDet.Church (NonDetC)
import qualified RIO.Seq as Seq
import qualified RIO.Partial as P

$(moduleId 2)

data InvRadixTree c k a
  = InvRadixCons !(c (Maybe a)) !(c (InvRadixChunk c k a)) !(c (InvRadixTree c k a))
  | InvRadixNil
type InvRadixChunk c k a = Reducible (InvRadixChunk' c k a)
data InvRadixChunk' c k a
  = ITop
  | IBin !Bool !Chunk !(c (InvRadixChunk c k a)) !(c (RadixChunk c k a)) -- Bool stands or if the taken path is right

data RadixZipper c k a = RadixZipper { radixPathToChunk :: ![Chunk], radixSuper :: !(c (InvRadixTree c k a)), radixSub :: !(c (RadixTree c k a)) }

reduceInvChunk'' :: (Container c, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> InvRadixChunk' c k a -> m (InvRadixChunk' c k a, Maybe (c (InvRadixChunk c k a)))
reduceInvChunk'' proxy = \case
  IBin _ _ supertree'@(tryFetchC -> Just (readReducible -> supertree)) (tryFetchC -> Just (readReducible -> RT.Nil)) -> reduce' proxy $> (supertree, Just supertree')
  nonReducible -> pure (nonReducible, Nothing)

reduceInvChunk' :: (Container c, Has (FreshIO :+: Reduce' s) sig m) => Proxy s -> InvRadixChunk' c k a -> m (InvRadixChunk' c k a)
reduceInvChunk' p v = fst <$> reduceInvChunk'' p v

reduceInvChunk :: (Container c, Has (FreshIO :+: Reduce) sig m) => InvRadixChunk' c k a -> m (InvRadixChunk' c k a)
reduceInvChunk = reduceInvChunk' (Proxy @"")

-- Problem: copy-paste from RadixTree
allocReducedInvChunk :: (Container c1, Container c2, Has FreshIO sig m) => (forall b. c2 b -> ReduceC m (c1 b)) -> InvRadixChunk' c2 k a -> m (c1 (InvRadixChunk c2 k a))
allocReducedInvChunk f c = runReduce $ reduceInvChunk'' (Proxy @"") c >>= \case
  (v, Nothing) -> allocC $ mkReducible v
  (_, Just v) -> f v

data SInvtree
data SInvchunk
data SZipper

class RT.Selector s m => SelectorZipper s m where
  selZipper :: s k SZipper -> [Chunk] -> m (Either (s k SInvtree) (s k RT.STree))
  selInvtreeNil :: s k SInvtree -> m Void
  selInvtreeCons :: s k SInvtree -> m (Either (Maybe (s k SInvchunk)) (s k SInvtree))
  selIBin :: s k SInvchunk -> Chunk -> Bool -> m (Either (Maybe (s k RT.SChunk)) (s k SInvchunk))
  selINil :: s k SInvchunk -> m (s k RT.SChunk) -- welp, this is awkward

accessInvtree :: forall sel c k a invtree sig m. (SelectorZipper sel m, Container c, Has (FreshIO :+: Reduce) sig m)
  => (Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> invtree -> invtree) -- ^ on skip invchunk
  -> (RT.RevList Chunk -> Chunk -> Maybe (sel k SInvchunk) -> c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> invtree) -- ^ on invchunk
  -> RT.RevList Chunk
  -> sel k SInvtree
  -> InvRadixTree c k a
  -> m invtree
accessInvtree onSkip onInvChunk =
  let
    goTree :: RT.RevList Chunk -> sel k SInvtree -> InvRadixTree c k a -> m invtree
    goTree _ sel1 InvRadixNil = absurd <$>  selInvtreeNil sel1
    goTree (RT.revUnsnoc -> Nothing) sel1 _ = absurd <$> selInvtreeNil sel1
    goTree (RT.revUnsnoc -> Just (xs, x)) sel1 (InvRadixCons el invchunk superInvChunks) =
      selInvtreeCons sel1 >>= \case
        Left sel2  -> pure $ onInvChunk xs x sel2 el invchunk superInvChunks
        Right sel2 -> onSkip x el invchunk <$> (goTree xs sel2 =<< fetchC superInvChunks)
  in goTree
{-# INLINE accessInvtree #-}

accessInvChunk :: forall sel c k invchunk a sig m. (SelectorZipper sel m, Container c, Has (FreshIO :+: Reduce) sig m)
  => (Bool -> Chunk -> c (RadixChunk c k a)    -> invchunk -> invchunk) -- ^ on super
  -> (sel k RT.SChunk -> Bool -> Chunk -> c (InvRadixChunk c k a) -> c (RadixChunk c k a) -> invchunk) -- ^ on sub
  -> Chunk
  -> sel k SInvchunk
  -> c (InvRadixChunk c k a)
  -> m invchunk
accessInvChunk onSuper onSub exKey =
  let
    goChunk :: sel k SInvchunk -> c (InvRadixChunk c k a) -> m invchunk
    goChunk sel1 chunkM =
      let
        newBranch :: m invchunk
        newBranch = do
          sel2 <- selINil sel1
          (key, _) <- RT.selNil sel2 -- well, this is awkward
          let (mask, placeRight) = RT.makeMask exKey key
          pure $ onSub sel2 (not placeRight) mask chunkM RT.sNil
      in fetchC chunkM >>= \chunk -> reducible reduceInvChunk chunk \case
        ITop -> newBranch
        IBin pickRight mask super sub -> selIBin sel1 mask pickRight >>= \case
          Left Nothing -> newBranch
          Left (Just sel2) -> pure $ onSub sel2 pickRight mask super sub
          Right sel2 -> onSuper pickRight mask sub <$> goChunk sel2 super
  in goChunk
{-# INLINE accessInvChunk #-}

accessRadixZipper :: forall sel c k a chunk invchunk invtree tree zipper sig m. (SelectorZipper sel (ReduceC m), Container c, Has (FreshIO :+: Fresh) sig m)
  => ([Chunk] -> c (InvRadixTree c k a) -> tree -> zipper) -- ^ on sub, zipper
  -> (RT.RevList Chunk -> sel k RT.SChunk -> c (RadixChunk c k a) -> chunk)
  -> (RT.RevList Chunk -> sel k RT.STree -> RadixTree c k a -> tree)
  -> ([Chunk] -> c (RadixTree c k a) -> invtree -> zipper) -- ^ on super, zipper
  -> (Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> invtree -> invtree) -- ^ on super skip, invtree
  -> (RT.FinalPath -> Chunk -> c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> invtree) -- ^ on found value, invtree
  -> (Chunk -> c (Maybe a) -> c (InvRadixTree c k a) -> invchunk -> invtree) -- ^ on found invchunk, invtree
  -> (Bool -> Chunk -> c (RadixChunk c k a)    -> invchunk -> invchunk) -- ^ on super, invchunk
  -> (Bool -> Chunk -> c (InvRadixChunk c k a) -> chunk    -> invchunk) -- ^ on sub, invchunk
  --
  -> sel k SZipper
  -> RadixZipper c k a
  -> m zipper
accessRadixZipper onSub onChunk onTree onSuper onSkip onFoundValue onFoundInvChunk onSuperInvChunk onSubInvChunk sel1 zipper = runReduce $
  selZipper sel1 zipper.radixPathToChunk >>= \case
    Right sel2 -> onSub zipper.radixPathToChunk zipper.radixSuper . onTree (fromList zipper.radixPathToChunk) sel2 <$> fetchC zipper.radixSub
    Left sel2 -> do
      radixSuper' <- fetchC zipper.radixSuper
      invRadix' <- join $ accessInvtree
        (\a b c d -> onSkip a b c <$> d)
        (\keys exKey sel3 val chunk super -> case sel3 of
          Nothing -> pure $ onFoundValue (RT.FinalPath $ toList keys) exKey val chunk super
          Just sel4 -> onFoundInvChunk exKey val super <$> accessInvChunk
            onSuperInvChunk
            (\sel5 a b c d -> onSubInvChunk a b c $ onChunk keys sel5 d)
            exKey sel4 chunk)
        (fromList zipper.radixPathToChunk)
        sel2
        radixSuper'
      pure $ onSuper zipper.radixPathToChunk zipper.radixSub invRadix'
{-# INLINE accessRadixZipper #-}

mkIBinNonRe :: Bool -> Chunk -> c (InvRadixChunk c k a) -> c (RadixChunk c k a) -> InvRadixChunk' c k a
mkIBinNonRe = IBin
{-# INLINE mkIBinNonRe #-}

mkIBin :: (Container c1, Container c2, Has FreshIO sig m) => (forall b. c2 b -> ReduceC m (c1 b)) -> Bool -> Chunk -> c2 (InvRadixChunk c2 k a) -> c2 (RadixChunk c2 k a) -> m (c1 (InvRadixChunk c2 k a))
mkIBin f a b c d = allocReducedInvChunk f $ mkIBinNonRe a b c d

lookup :: (SelectorZipper sel (ReduceC m), Container c, Has FreshIO sig m) => sel k SZipper -> RadixZipper c k a -> m (Maybe a)
lookup sel zipper = runReduce =<< accessRadixZipper
  (\_ _ -> id)
  (\p a b -> join $ fst RT.internalLookup p a b)
  (\p a b -> join $ snd RT.internalLookup p a b)
  (\_ _ -> id)
  (\_ _ _ -> id)
  (\_ _ val _ _ -> fetchC val)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  (\_ _ _ -> id)
  sel zipper

insert :: (SelectorZipper sel (ReduceC m), Container c, Has FreshIO sig m) => sel k SZipper -> a -> RadixZipper c k a -> m (RadixZipper c k a)
insert path val zipper = runReduce =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (allocC =<< c))
  (\p a b -> join $ fst (RT.internalInsert val) p a b)
  (\p a b -> join $ snd (RT.internalInsert val) p a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (allocC =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (allocC =<< c))
  (\_tipOfSkipped _ _ b c -> (\val' -> InvRadixCons val' b c) <$> allocC (Just val))
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    allocC $ mkReducible $ mkIBinNonRe a b d' c)
  (\a b c d -> allocC . mkReducible . mkIBinNonRe a b c =<< d)
  path zipper

update :: (SelectorZipper sel (ReduceC m), Container c, Has FreshIO sig m) => (c (Maybe a) -> ReduceC m (c (Maybe a))) -> sel k SZipper -> RadixZipper c k a -> m (RadixZipper c k a)
update f sel zipper = runReduce =<< accessRadixZipper
  (\a b c -> RadixZipper a b <$> (allocC =<< c))
  (\p a b -> join $ fst (RT.internalUpdate f) p a b)
  (\p a b -> join $ snd (RT.internalUpdate f) p a b)
  (\a b c -> (\c' -> RadixZipper a c' b) <$> (allocC =<< c))
  (\_tipOfSkipped a b c -> InvRadixCons a b <$> (allocC =<< c))
  (\_tipOfSkipped _ _deleted b c -> pure $ InvRadixCons sNothing b c)
  (\_ a b c -> (\c' -> InvRadixCons a c' b) <$> c)
  (\a b c d -> do
    d' <- d
    mkIBin pure a b d' c)
  (\a b c d -> mkIBin pure a b c =<< d)
  sel
  zipper

delete :: (SelectorZipper sel (ReduceC m), Container c, Has FreshIO sig m) => sel k SZipper -> RadixZipper c k a -> m (RadixZipper c k a)
delete = update (\_ -> pure sNothing)

pop :: (SelectorZipper sel (ReduceC (WriterC (First a) m)), Container c, Has FreshIO sig m) => sel k SZipper -> RadixZipper c k a -> m (Maybe a, RadixZipper c k a)
pop k rt = runWriter (\(First a) b -> pure (a, b)) $ update
  (\v -> do
    v' <- fetchC v
    tell $ First v'
    pure sNothing
  )
  k rt

sITop :: Container c => c (InvRadixChunk c k a)
sITop = $sRunEvalFresh $ allocC $ mkReducible ITop

focus :: forall c k a sig m sel. (SelectorZipper sel (ReduceC m), Container c, Has FreshIO sig m) => sel k SZipper -> RadixZipper c k a -> m (RadixZipper c k a)
focus =
  let
    applyNM :: forall m1 a1. Monad m1 => Int -> (a1 -> m1 a1) -> a1 -> m1 a1
    applyNM 0 _ x = pure x
    applyNM n f x = applyNM (n-1) f =<< f x

    -- focusRadix :: Chunk -> [Chunk] -> c (RadixChunk c k a) -> m (c (Maybe a) -> c (InvRadixChunk c k a) -> c (InvRadixTree c k a) -> m (RadixZipper c k a))
    focusRadix = --fst $
      let onTipInv topval invchunk invtree = allocC $ InvRadixCons topval invchunk invtree
      in RT.accessRadix
        (\val chunk -> chunk val sITop)
        (\(RT.FinalPath finalPath) rt invtree -> RadixZipper finalPath invtree <$> allocC rt) -- on found, tree
        (\_key1 (length -> leftToPass) (RT.FinalPath finalPath) topval invchunk invtree -> do -- on missing
          super' <- applyNM leftToPass
            (allocC . InvRadixCons sNothing sITop) -- add empty trees 'length keys2' times
            =<< onTipInv topval invchunk invtree -- finish this chunk
          pure $ RadixZipper -- on missing
            finalPath
            super'
            RT.sEmpty)
        (\_key tree topval invchunk invtree -> tree =<< onTipInv topval invchunk invtree)
        (\pickRight mask other picked topval invchunk invtree -> (\invchunk' -> picked topval invchunk' invtree) =<< mkIBin pure pickRight mask invchunk other)

    revInvChunk :: Chunk -> RadixTree c k a -> c (Maybe a) -> c (InvRadixChunk c k a) -> ReduceC m (RadixTree c k a)
    revInvChunk chunkName oldTree topval oldInvChunk =
      let
        revInvChunk' :: c (RadixChunk c k a) -> c (InvRadixChunk c k a) -> ReduceC m (RadixTree c k a)
        revInvChunk' chunk invchunk = do
          invchunk' <- fetchC invchunk
          reducible reduceInvChunk invchunk' \case
            ITop -> pure $ RT.RadixTree topval chunk
            IBin pickRight mask super other -> (`revInvChunk'` super) =<< RT.mkBin pure pickRight mask other chunk
      in (`revInvChunk'` oldInvChunk) =<< RT.mkTip pure chunkName oldTree
  in \selOr -> runReduce <=< accessRadixZipper
    (\_ initialInvT tree -> tree initialInvT) -- on sub, zipper
    (\p sel chunk topval invchunk invtree ->
      fst focusRadix p sel chunk >>= \f -> f topval invchunk invtree)
    (\p sel tree invtree ->
      snd focusRadix p sel tree >>= \f -> f invtree)
    (\_ initialT invtree -> invtree =<< fetchC initialT) -- on super, zipper
    --   -- when we go up, we save the initial tree in a Tip. So eventually it needs to be fetchCed, unfortunately
    --   -- alternatively, we could save pointer on Tip, but the problem doesn't sound to worth it
    (\key topval invchunk invtree tree -> invtree =<< revInvChunk key tree topval invchunk) -- on skip
    (\(RT.FinalPath fp) key topval invchunk invtreeM oldTree -> -- on found value, invtree
      RadixZipper fp invtreeM <$> (allocC =<< revInvChunk key oldTree topval invchunk))
    (\key topval invtree invchunk rt -> invchunk topval invtree =<< RT.mkTip pure key rt)
    (\pickRight mask other super topval invtree chunk -> super topval invtree =<< RT.mkBin pure pickRight mask other chunk) -- on super, invchunk
    (\pickRight mask super other topval invtree chunk -> (\invchunk' -> other topval invchunk' invtree)  =<< mkIBin pure (not pickRight) mask super chunk) -- on sub, invchunk
    selOr

empty :: Container c => RadixZipper c k a
empty = RadixZipper [] ($sRunEvalFresh $ allocC InvRadixNil) RT.sEmpty

-- selectors

data instance RT.SelEq k SZipper = SelEqZ ![Chunk]
data instance RT.SelEq k SInvtree = SelEqIT !Int ![Chunk]
data instance RT.SelEq k SInvchunk = SelEqIC !Chunk ![Chunk]

instance Applicative m => SelectorZipper RT.SelEq m where
  selZipper (SelEqZ targetPath) currPath =
    let
      diffFor (x:xs) (y:ys)
        | x == y = diffFor xs ys
      diffFor p1 p2 = (p1, p2)
      (backSteps, relPath) = diffFor currPath targetPath
    in pure $ case backSteps of
      [] -> Right $ RT.SelEqT relPath
      _nonEmptyFindBranch -> Left $ SelEqIT (length backSteps - 1) relPath
  selInvtreeNil _ = error "impossible, hopefully"
  selInvtreeCons (SelEqIT skip relPath) = pure case skip of
    0 -> Left case relPath of
      [] -> Nothing
      (x:xs) -> Just $ SelEqIC x xs
    _ -> Right $ SelEqIT (skip - 1) relPath
  selIBin s@(SelEqIC k ks) mask pickRight = pure case RT.tryMask mask k of
    Just guidesRight-> Left $
      if pickRight == guidesRight -- we're guided the same way we came from
        then Nothing
        else Just $ RT.SelEqC k ks
    Nothing -> Right s
  selINil (SelEqIC k ks) = pure $ RT.SelEqC k ks

selEq :: RT.IsRadixKey k => k -> RT.SelEq k SZipper
selEq k = SelEqZ $ RT.toRadixKey k

-- We use two nondets, one to capture turns to the left in Invtree and one to capture turn to the right in Invtree (as well as to search in RT)

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
    L (L ChooseL) -> p (True <$ ctx) `l` p (False <$ ctx)
    L (R (L ChooseR)) -> p (False <$ ctx) `r` p (True <$ ctx)
    L (R (R Empty)) -> n
    -- my brain went out of the chat somewhere here, *I hope* this is correct
    -- maybe I should patent brainless programming?
    R other -> thread (dst ~<~ hdl) other (pure ctx) >>= run . runNonDetLR (coerce l) (coerce r) (coerce p) (coerce n)
    where
    dst :: Applicative m => NonDetLRC Identity (NonDetLRC m a) -> m (NonDetLRC Identity a)
    dst = run . runNonDetLR
      (liftA2 pl)
      (liftA2 pr)
      (pure . runNonDetLRA)
      (pure (pure $ NonDetLRC \_l _r _p n -> n))
    pl left main = (\(NonDetLRC left') (NonDetLRC main') -> NonDetLRC \l r p n -> left' l r p n `l` main' l r p n) <$> left <*> main 
    pr main right = (\(NonDetLRC main') (NonDetLRC right') -> NonDetLRC \l r p n -> main' l r p n `r` right' l r p n) <$> main <*> right
    runNonDetLRA :: Applicative f => NonDetLRC f a -> f (NonDetLRC m2 a)
    runNonDetLRA = runNonDetLR pl pr (pure . pure) (pure $ NonDetLRC \_l _r _p n -> n)
  {-# INLINE alg #-}  

-- Run NonDeLRC, moving from bottom to top of the tree and collecting result into an alternative
runNonDetLRInvA :: forall f m a. (Applicative m, Alternative f) => NonDetLRC m a -> Free (Compose m f) a
runNonDetLRInvA act = pack $ runNonDetLR
    (\left main -> (\f x -> f (pure (pack left) <|> x)) <$> main)
    (\main right -> (\f x -> f (x <|> pure (pack right))) <$> main)
    (\a -> pure \x -> pure (pure a) <|> x)
    (pure id) act
  where
    pack :: m (f (Free (Compose m f) a) -> f (Free (Compose m f) a)) -> Free (Compose m f) a
    pack act2 = Free $ Compose $ ($ A.empty) <$> act2

-- TODO: tests for NonDetLRC
data instance RT.SelChoose k SZipper = SelChooseZ
data instance RT.SelChoose k SInvtree = SelChooseIT
data instance RT.SelChoose k SInvchunk = SelChooseIC

instance (HasLabelled "stray" NonDet sig m, HasLabelled "invtree" NonDetLR sig m, Has NonDet sig m) => SelectorZipper RT.SelChoose m where
  selZipper SelChooseZ _currPath = do
    goSub <- sendLabelled @"invtree" $ inj ChooseL
    pure case goSub of
      False -> Left SelChooseIT
      True -> Right RT.SelChooseT
  selInvtreeNil SelChooseIT = sendLabelled @"invtree" $ inj Empty
  selInvtreeCons SelChooseIT = do
    continue <- sendLabelled @"stray" $ inj Choose
    case continue of
      False -> pure $ Left $ Just SelChooseIC
      True -> do
        found <- sendLabelled @"invtree" $ inj ChooseL
        pure case found of
          False -> Right SelChooseIT
          True -> Left Nothing
  selIBin SelChooseIC _mask pickRight = do
    goBranch <- sendLabelled @"invtree" $
      if pickRight
        then inj ChooseL -- if we're right, the other one is left
        else inj ChooseR -- if we're left, the other one is right
    pure case goBranch of
      False -> Right SelChooseIC
      True -> Left $ Just $ RT.SelChooseC
  selINil _sel = sendLabelled @"stray" $ inj Empty

min :: Monad m => NonDetC (Labelled "stray" NonDetC (Labelled "invtree" NonDetLRC m)) a -> m (Maybe a)
min act = extract $ runNonDetLRInvA $ runLabelled @"invtree" $ fmap P.fromJust $ RT.min $ runLabelled @"stray" $ RT.min act
  where
    extract :: Monad m => Free (Compose m Seq) (Maybe a) -> m (Maybe a)
    extract = \case
      Pure a -> pure a
      Free (Compose act2) ->
        act2 >>= fix
          (\rec oldS -> case Seq.viewr oldS of
            Seq.EmptyR -> pure Nothing
            newS Seq.:> x -> extract x >>= \case
              Nothing -> rec newS
              r -> pure r)

-- debug

instance (Container c, Show a) => Show (InvRadixTree c k a) where
  show = \case
    InvRadixNil -> "InvRadixNil"
    InvRadixCons topval super other -> "(InvRadixCons (" <> RT.tryFetchShow topval <> ") " <> RT.tryFetchShow super <> " " <> RT.tryFetchShow other <> ")"
instance (Container c, Show a) => Show (InvRadixChunk' c k a) where
  show = \case
    ITop -> "ITop"
    IBin pickRight mask super other -> "(IBin " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow super <> " " <> RT.tryFetchShow other <> ")"
instance (Container c, Show a) => Show (RadixZipper c k a) where
  show (RadixZipper a b c) = "RADIX ZIPPER:\n" <> show a <> "\n" <> RT.tryFetchShow b <> "\n" <> RT.tryFetchShow c

-- showRadixZipperLookup :: forall c k a sig m. (Container c, Show a, Has Fresh sig m) => [Chunk] -> RadixZipper c k a -> m String
-- showRadixZipperLookup = showRadixZipperLookup' where
--   showRadixLookup :: (Chunk -> [Chunk] -> c (RadixChunk c k a) -> ReduceC m String, [Chunk] -> RadixTree c k a -> ReduceC m String)
--   showRadixLookup = RT.accessRadix
--     (\val chunk -> "(onSubT " <> RT.tryFetchShow val <> " " <> chunk <> ")")
--     (\rt -> "(onFoundT " <> show rt <> ")")
--     (\key keys -> "(onMissingC " <> show key <> " " <> show keys <>")")
--     (\key tree -> "(onTipC " <> show key <> " " <> tree <> ")")
--     (\pickRight mask other curr -> "(onBranchC " <> show pickRight <> " " <> show mask <> "" <> RT.tryFetchShow other <> " " <> curr <> ")")

--   showRadixZipperLookup' path zipper = nonRe =<< accessRadixZipper
--     (\k v t -> t <&> \t' -> "(onSubZ " <> show k <> " " <> RT.tryFetchShow v <> " " <> t' <> ")")
--     (fst showRadixLookup)
--     (snd showRadixLookup)
--     (\k v t -> t <&> \t' -> "(onSuperZ" <> " " <> show k <> " " <> RT.tryFetchShow v <> " " <> t' <> ")")
--     (\k v ic it -> it <&> \it' -> "(onSkipIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow ic <> " " <> it' <> ")")
--     (\k v ic it -> pure $ "(onFoundIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow ic <> " " <> RT.tryFetchShow it <> ")")
--     (\k v it ic -> ic <&> \ic' -> "(onFoundInvChunkIT " <> show k <> " " <> RT.tryFetchShow v <> " " <> RT.tryFetchShow it <> " " <> ic' <> ")")
--     (\pickRight mask other super -> super <&> \super' ->"(onSuperIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow other <> " " <> super' <> ")")
--     (\pickRight mask super other -> other <&> \other' -> "(onSubIC " <> show pickRight <> " " <> show mask <> " " <> RT.tryFetchShow super <> " " <> other' <> ")")
--     path zipper

