module Dentrado.POC.Types where -- probably should be moved to Dentrado.POC.Data.Types?

import RIO
import System.IO.Unsafe (unsafePerformIO)
import qualified Type.Reflection as T
import Data.Kind (Type)
import Control.Carrier.Empty.Church (EmptyC, runEmpty, Empty, empty)
import Control.Algebra

data Dynamic1 f = forall a. Dynamic1 !(T.TypeRep a) !(f a)
data Any1 f = forall a. Any1 !(f a)

type Chunk = Word32 -- WARNING: `Serialized a` & IsRadixKey assumes 4 bytes.

-- | Presence of Delay fields in some types interferes with construction of the most optimal spine.
-- Reducible is a potential fix that allows to "reduce" the spine as more Delayed computations
-- are resolved.
newtype Reducible a = Reducible (IORef a)

readReducible :: Reducible a -> a
readReducible (Reducible x) = unsafePerformIO $ readIORef x

instance Show a => Show (Reducible a) where
  show = show . readReducible

data RadixTree c (k :: Type) a = RadixTree !(c (Maybe a)) !(c (RadixChunk c k a)) -- both element and next is containerized, both can be left unwrapped.
  deriving Generic
type RadixChunk c (k :: Type) a = Reducible (RadixChunk' c k a)
data RadixChunk' c (k :: Type) a
  = Nil
  | Tip !Chunk !(RadixTree c k a) -- RadixTree is the only possible branch. Still could be containerized, but I'm not sure it's worth it
  | Bin !Chunk !(c (RadixChunk c k a)) !(c (RadixChunk c k a)) -- Either branch can be accessed, so containerization
  deriving Generic

data MapDiffE v = MapAdd !v | MapUpd !v !v | MapDel !v
  deriving Generic
data StateGraphEntry v = StateGraphEntrySampled | StateGraphEntryModified !v
  deriving Generic

newtype Timestamp = Timestamp Word32
  deriving (Eq, Ord, Generic)

-- | Event id, local to the timestamp.
-- 8 highest bits represent id of the source cluster server.
-- 24 lowest bit represent "epoch", monotonic id of event within the source cluster server within the second.
newtype LocalId = LocalId Word32
  deriving (Eq, Ord, Generic)
-- | Full Event ID
data EventId = EventId !Timestamp !LocalId
  deriving (Eq, Ord, Generic)

data SiteAccessLevel = SalNone | SalUser | SalModerator | SalAdmin
  deriving Generic

-- let Event =
--   < Admin:
--       < SetAccessLevel: { user: UserId, level: SiteAccessLevel }
--       | Revoke: EventId
--       >
--   | User:
--       < CreateMessage: { owned: Bool } -- Обобщённое создание пустого поста/страницы.
--       | EditMessage:
--           { message: MessageId
--           , update:
--             < Delete: {} -- удалить сообщение
--             | Update: -- обновить отдельные поля сообщения
--               { titleUpdate: Optional Text
--               , contentUpdate: Optional Text
--               , subUpdate: Optional (Text :-> Optional MessageId)
--               }
--             >
--           }
--       | UpdateAttachment:
--           { what: MessageId
--           , to: MessageId
--           , relation: Optional < Like | Info | Dislike >
--           } 
--       | Merge: BranchId
--       >
--   >


data Event
  = AdminSetAccessLevel !EventId !EventId !SiteAccessLevel -- #0: admin, user, level
  -- | AdminRevoke !EventId !EventId -- #1: admin, user event
  | UserCreateMessage !EventId !Bool -- #2: user, owned?
  | UserEditMessage !EventId !EventId !(Maybe (Maybe Text, (Maybe Text, [(Text, Maybe EventId)]))) -- #3: user, message, new content?: update title?, update content?, update-set subpages
  deriving Generic

-- Util functions
-- TODO: Move them.

-- Just like from maye
fromEmpty :: Applicative m => a -> EmptyC m a -> m a
fromEmpty def = runEmpty (pure def) pure
{-# INLINE fromEmpty #-}

maybeToEmpty :: Has Empty sig m => Maybe a -> m a
maybeToEmpty = maybe empty pure
{-# INLINE maybeToEmpty #-}
