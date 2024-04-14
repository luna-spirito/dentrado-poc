module Main where

import Db
import RIO

-- | Timestamp of the Event
newtype Timestamp = Timestamp Int
-- | ID of the server that registered the Event
newtype SourceId = Source Int
-- | Internal ID of the Event within the server that registered it
newtype Epoch = Epoch Int
-- | Full Event ID
type EventId = (Epoch, SourceId)

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
data Event = Event (Timestamp, EventId) EventData

-- List of events after all the revocations
events :: forall s. Assembly Event s (Set Event)
events = fixGear $ simpleGear 
-- data Await a where
-- logins :: forall s. Assembly Event s 
-- users :: forall s. Assembly Event s ( EventId)
  

main :: IO ()
main = pure ()
