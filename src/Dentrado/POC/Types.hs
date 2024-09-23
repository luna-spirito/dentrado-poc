module Dentrado.POC.Types where -- probably should be moved to Dentrado.POC.Data.Types?

import RIO
import System.IO.Unsafe (unsafePerformIO)
import qualified Type.Reflection as T
import Data.Kind (Type)

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

data Event
  = Register
  | Login EventId -- user's registration
  | CreateSite EventId -- user's login
  | SetSiteAccessLevel EventId EventId EventId SiteAccessLevel -- admin's login, site's creation, user's registration
  | CreateArticle EventId EventId -- user's login, site's creation
  | UpdateArticle EventId EventId Text -- user's login, article's creation, content
  deriving Generic
