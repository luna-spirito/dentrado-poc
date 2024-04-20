module Main where

import Db
import RIO
import Control.Algebra (Has, send)
import qualified RIO.Set as Set
import qualified RIO.HashMap as HM
import Data.Monoid (Sum(..))
import qualified RIO.Map as Map

-- | Timestamp of the Event
newtype Timestamp = Timestamp Int
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
data PostData f = PostData { answers :: f EventId, title :: f Text, message :: f Text, locked :: f Text }

data EventData
  -- | Create user, issued by root.
  = CreateUser (AccountData ActInsert)
  -- | Update user. Unfortunately, that's a separate operation, because user can created only by the root,
  -- ... but it can be updated by the same user.
  | UpdateUser ActorLogin EventId (AccountData ActOverwrite)
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

-- instance Eq Event where
--   (Event a _) == (Event b _) = a == b

-- setDiff :: Ord a => Set a -> Set a -> SetUpd a
-- setDiff a b = SetUpd { setUpdAdd = b `Set.difference` a, setUpdRemove = a `Set.difference` b }

-- hmapDiff :: HashMap k v -> HashMap k v -> HashMap k (Maybe v)
-- hmapDiff = _


-- mapDiff :: Map k v -> Map k v -> Map k (Maybe v)
-- mapDiff = _

mapValDiff :: Map k v -> Map k v -> SetUpd v
mapValDiff = _

mapKeyDiff :: Map k v -> Map k v -> SetUpd k
mapKeyDiff = _

-- Int ~ Maybe Int Iso'morphism

-- | @0 -> Nothing@
-- @x -> Just x@
toUsesEntry :: Int -> Maybe Int
toUsesEntry = \case
  0 -> Nothing
  x -> Just x

fromUsesEntry :: Maybe Int -> Int
fromUsesEntry = fromMaybe 0

cascadeUpdate :: (u -> a -> Maybe (u, a)) -> u -> a -> a
cascadeUpdate f origU origA = case f origU origA of
  Nothing -> origA
  Just (u, a) -> cascadeUpdate f u a

setToMap :: Set a -> Map a ()
setToMap = Map.fromSet $ const ()

refilter :: Ord k => SetUpd k -> Map k v -> Map k v -> Map k v
refilter upd new filtered =
  Map.intersectionWith (const id) (setToMap $ setUpdRemove upd) new
  <> Map.difference filtered (setToMap $ setUpdRemove upd)

-- | List of events after all the revocations
events :: Has (Snapshot Events m) sig m => Assembly Events m (m Events)
events = (getConst <$>) <$> withCache (mempty, mempty, mempty) (pure \(oldInput, oldRevocations, oldFiltered) -> do
    newInput <- snapshotEvents
    let updInput = oldInput `mapValDiff` newInput
        updRevocations =
          let process val = foldMap \case
                Revoke x -> Map.singleton x (Sum val)
                _ -> mempty
          in process 1 (setUpdAdd updInput) <> process (-1) (setUpdAdd updInput)
        newRevocations = cascadeUpdate
            (\origUpd rev -> Map.maxViewWithKey origUpd & fmap \((eventId, Sum eventUpdRevs), interUpd) ->
                let eventOldRevs = fromUsesEntry $ Map.lookup eventId rev
                    eventNewRevs = eventOldRevs + eventUpdRevs in
                (interUpd <> case Map.lookup eventId newInput of
                  Just (Revoke targetEventId)
                    | eventOldRevs <= 0 && eventNewRevs > 0 -> Map.singleton targetEventId (Sum 1)
                    | eventOldRevs > 0 && eventNewRevs <= 0 -> Map.singleton targetEventId (Sum $ -1)
                  _ -> mempty
                , Map.alter (\_ -> toUsesEntry eventNewRevs) eventId rev))
            updRevocations
            oldRevocations
        newFiltered = refilter (oldRevocations `mapKeyDiff` newRevocations) newInput oldFiltered
    pure ((newInput, newRevocations, newFiltered), Const newFiltered))


--   )
-- events :: Has (Snapshot Event m) sig m => Assembly Event m (m (Set Event))
-- events = (getConst <$>) <$> withCache (mempty, mempty, mempty) (pure \(oldInput, oldRevocations, oldFiltered) -> do
--     newInput <- snapshotEvents
--     let newRevocations = foldl' (\rev x -> Map.adjus)
--     -- let revocChanged = runWriter $
--     --   let f = foldl' (\revocations  ) oldRevocations (setDiff oldInput newInput)
--     _

main :: IO ()
main = pure ()
