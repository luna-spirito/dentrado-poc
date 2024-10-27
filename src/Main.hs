{-# LANGUAGE ApplicativeDo #-}

module Main where

import RIO

{-
import Dentrado.POC.Db
import RIO
import Dentrado.POC.Data
import Control.Algebra (Has, send)
import qualified RIO.HashMap as HM
import Data.Monoid (Sum(..))
import qualified GHC.Exts as Exts
import qualified Data.Map.Internal as Map.In
import qualified RIO.Partial as P

-- | Timestamp of the Event
newtype Timestamp = Timestamp Word32
  deriving (Eq, Ord)
-- | ID of the server that registered the Event.
-- In real implementation, each server will assign different
-- ids to different known servers
newtype SourceId = Source Word32
  deriving (Eq, Ord)
-- | Internal ID of the Event within the server that registered it
newtype Epoch = Epoch Word32
  deriving (Eq, Ord)
-- | Full Event ID
type EventId = (Timestamp, SourceId, Epoch)

-- | Insert action just contains the value we need to insert
newtype ActInsert a = ActInsert a
-- | Overwrite action optionall contains the value we need to insert instead
newtype ActOverwrite a = ActOverwrite (Maybe a)

-- | Create/Update event
data CU f = Create (f ActInsert) | Update (EventId, f ActOverwrite)

-- Account management.
data AccountData act = AccountData { nickname :: act Text, password :: act () }
data UserState = UserAdmin | UserNormal | UserBanned

-- | Who performs the action. Refers to the login event.
data ActorLogin = ActorUser EventId | ActorRoot

-- | Post made by the user
-- "locked" is a special field that should't be actually updated by mere mortals
data PostData act = PostData { answers :: act EventId, title :: act Text, message :: act Text, locked :: act Text }

data EventData
  -- | Create user, issued by root.
  = CreateUser (AccountData ActInsert)
  -- | Update user. Unfortunately, that's a separate operation, because user can be created only by the root,
  -- ... but it can be updated by the same user.
  | UpdateUser ActorLogin (EventId, AccountData ActOverwrite)
  -- | Confirm user login, assigning some login token to the user.
  -- () is placeholder for login token assigned to the user.
  | Login () EventId
  -- | Admin/root can set user's permissions. Self included.
  | SetUserPerms ActorLogin EventId UserState
  -- | Create/update post
  | Post ActorLogin (CU PostData)
  -- Root can revoke any event
  | Revoke EventId
type Events = Map EventId EventData

-- boilerplate instances

-- utils

newtype Comb f k v = Comb { unComb :: f k v }
instance (Ord k, Semigroup v) => Semigroup (Comb Map k v) where
  a <> b = Comb $ Map.unionWith (<>) (unComb a) (unComb b)
instance (Hashable k, Semigroup v) => Semigroup (Comb HashMap k v) where
  a <> b = Comb $ HM.unionWith (<>) (unComb a) (unComb b)
instance (Monoid (f k v), Semigroup (Comb f k v)) => Monoid (Comb f k v) where
  mempty = Comb mempty

mapMaybeSetUpd :: Ord b => (a -> Maybe b) -> SetUpd a -> SetUpd b
mapMaybeSetUpd f (SetUpd a b) =
  let f' = Set.fromList . mapMaybe f . Set.toList
  in SetUpd (f' a) (f' b)

groupSetUpd :: (Hashable k, Ord v) => (a -> (k, v)) -> SetUpd a -> HashMap k (SetUpd v)
groupSetUpd f (SetUpd added removed) =
  let f' con = (con <$>) . unComb . foldMap \a ->
        let (k, v) = f a
        in Comb $ HM.singleton k (Set.singleton v)
  in HM.unionWith (<>)
    (f' (`SetUpd` mempty) added)
    (f' (mempty `SetUpd`) removed)

-- f' :: (Set a1 -> SetUpd a1) -> Set a -> HashMap k (SetUpd v)
-- f' = _

mapKVDiff :: Map k v -> Map k v -> SetUpd (k, v)
mapKVDiff = _

-- setToMap :: Set a -> Map a ()
-- setToMap = Map.fromSet $ const ()

{-
TimeState — непустой список состояний. Тупо хранит состояния в разные точки времени.
-}
newtype TimeState a = TimeState (Map EventId a)

restate :: SetUpd (EventId, v) -> TimeState v -> TimeState v
restate = _

{-
Когда пользователь хочет изменить настройки аккаунта, он
запихивает в систему патч. То есть исключительно само изменение.
-}

-- accumMap :: Map k v -> Map k v -> Map k v -> Map k v
-- accumMap oldInput newInput oldAccum = _

-- https://hackage.haskell.org/package/unordered-containers-0.2.20/docs/src/Data.HashMap.Internal.html#ptrEq
-- ptrEq :: a -> a -> Bool
-- ptrEq !x !y = Exts.isTrue# (Exts.reallyUnsafePtrEquality# x y Exts.==# 1#)

-- https://hackage.haskell.org/package/containers-0.7/docs/src/Data.Map.Internal.html#lookup
lookupSubmap :: Ord k => k -> Map k a -> Maybe (Map k a)
lookupSubmap = go
  where
    go !_ Map.In.Tip = Nothing
    go k x@(Map.In.Bin _ kx _ l r) = case compare k kx of
      LT -> go k l
      GT -> go k r
      EQ -> Just x

newtype AggTree k v = AggTree (Map k v)

reagg :: (Ord k, Monoid a) => Map k a -> Map k a -> AggTree k a -> AggTree k a
reagg oldInput newInputOr (AggTree oldCache) = AggTree $ f newInputOr where
  top = \case
    Map.In.Tip -> mempty
    Map.In.Bin _ _ v _ _ -> v

  f newInput = case newInput of
    Map.In.Tip -> newInput
    Map.In.Bin s k _ l r
      | maybe False (ptrEq newInput) $ lookupSubmap k oldInput
        -> P.fromJust $ lookupSubmap k oldCache
      | otherwise ->
        let l' = f l
            r' = f r
        in Map.In.Bin s k (top l' <> top r') l' r'

-- Gears

-- Int ~ Maybe Int Iso'morphism

-- | @0 -> Nothing@
-- @x -> Just x@
toUsesEntry :: Int -> Maybe Int
toUsesEntry = \case
  0 -> Nothing
  x -> Just x

fromUsesEntry :: Maybe Int -> Int
fromUsesEntry = fromMaybe 0

-- | List of events after all the revocations.
events :: Has (Snapshot Events m) sig m => Assembly Events m (m Events)
events = (getConst <$>) <$> withCache (mempty, mempty) (pure \(oldInput, oldRevocations) -> do
    newInput <- snapshotEvents
    let updInput = oldInput `mapKVDiff` newInput & mapMaybeSetUpd \case
          (_, Revoke x) -> Just x
          _nonRevoke -> Nothing
        updRevocations =
          let process val = foldMap (`Map.singleton` Sum val)
          in process 1 (setUpdAdd updInput) <> process (-1) (setUpdAdd updInput)
        newRevocations = cascadeUpdate
            (\origUpd rev -> Map.maxViewWithKey origUpd & fmap \((eventId, Sum eventUpdRevs), interUpd) ->
                let eventOldRevs = fromUsesEntry $ Map.lookup eventId rev
                    eventNewRevs = eventOldRevs + eventUpdRevs in
                (unComb $ Comb interUpd <> Comb case Map.lookup eventId newInput of
                  Just (Revoke targetEventId)
                    | eventOldRevs <= 0 && eventNewRevs > 0 -> Map.singleton targetEventId (Sum 1)
                    | eventOldRevs > 0 && eventNewRevs <= 0 -> Map.singleton targetEventId (Sum $ -1)
                  _ -> mempty
                , Map.alter (\_ -> toUsesEntry eventNewRevs) eventId rev))
            updRevocations
            oldRevocations
        filtered = Map.difference newInput newRevocations -- This is not optimal
        -- as it is computed on each call, but this could be drastically improved:
        -- 1) Spine-lazy `Map.difference`. This way, only accessed elements are filtered out.
        -- 2) On the other hand, `Map.difference` could optimized by unifying spine structure of both maps.
        -- ... so we can traverse both trees at the same time while filtering.
    pure ((newInput, newRevocations), Const filtered))

userByLogin :: Assembly Events m (m (HashMap EventId (TimeState EventId)))
userByLogin = (getConst <$>) <$> withCache (mempty, mempty) do
  queryEvents <- events
  pure \(oldInput, oldOutput) -> do
    newInput <- queryEvents
    let updInput = _
    _
    -- let updInput = map
    -- `mapKVDiff`

-- userByLogin :: Assembly Events m (m (HashMap EventId (TimeState EventId)))
-- userByLogin = (getConst <$>) <$> withCache (mempty, mempty) do
--   queryEvents <- events
--   pure \(oldInput, oldOutput) -> do
--     newInput <- queryEvents
--     let updInput

-- userByLogin/identify user by login: HashMap <Login> (TimeState <User>)
--  <- events
-- actsByUser/acts per user: HashMap <User> (Set EventId)
--  <- events + userByLogin
-- profileByUser
--  <- actsByUser + events
--

{-
Проблема в том, что Patch, в своём ядре, является штукой,
которую можно применить 1 раз
-}

-- newtype Stateful a = Stateful (Map EventId )

-- users :: Assembly Events m (m (HashMap EventId (TimeState EventId AccountData)))
-- users = _
-}

main ∷ IO ()
main = pure ()
