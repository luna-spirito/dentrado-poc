module Dentrado.POC.Types where

import Control.Algebra
import Control.Carrier.Empty.Church (Empty, EmptyC, empty, runEmpty)
import Data.Kind (Type)
import RIO
import System.IO.Unsafe (unsafePerformIO)
import qualified Type.Reflection as T

{-
This module exists due to the fact that Haskell disallows circular imports.
It defines basic some basic types used in the Dentrado.
-}

-- Types for dynamically typed & untyped values. Needed to type operations related to external memory (disk).
data Dynamic1 f = ∀ a. Dynamic1 !(T.TypeRep a) !(f a)
data Any1 f = ∀ a. Any1 !(f a)

-- Type alias to 4-byte unsigned integer.
-- This type alias is related to the RadixTree, which splits each binary key in a series of Chunk's.
type Chunk = Word32 -- WARNING: `Serialized a` & IsRadixKey assumes 4 bytes.

{-
Dentrado contains laziness functionality, meaning that it can operate with data structure which are not
fully evaluated.

Reducible is a transparent (and omittable) wrapper that allows to possibly automatically reduce the spine of the
reduced data structure. Related to `Delay`.

TODO: This idea is not so bad in concept, but such reduction may not fire in non-linear context.
At the same time, if linear access is enforced, there's no need for such wrapper to perform the optimisation
(example: Higher Order Virtual Machine: Bend: Map/get)
However, Haskell does not support linear types*.
(* it actually does, but this will instantly get unbearable, since all the constructs in Haskell are not designed for linearity)
-}
newtype Reducible a = Reducible (IORef a)

readReducible ∷ Reducible a → a
readReducible (Reducible x) = unsafePerformIO $ readIORef x

instance (Show a) ⇒ Show (Reducible a) where
  show = show . readReducible

-- | No-op wrapper. Used to simplify Haskell type inference.
newtype W a = W {unW ∷ a}
  deriving newtype (Eq, Ord, Show)

{-
In Dentrado, the border between memory and disk data is blurred.
Some data structures could be so large that they are only partially loaded into RAM, while the rest stays on disk.
Current iteration of Dentrado uses special data type — Res — which is union/enum that is used to describe both disk and RAM data.
Conventional huge data structures (lists, dictionaries, ...) need to be revised to support Res.

Other possible implementation is to avoid defining such structures in Haskell and store objects directly in memory-mapped regions.
-}

{- |
RadixTree is hypothesized to be the best general dictionary/map implementation for the needs of an immutable reactive database.
It features:
1) Stable structure, which allows to efficiently perform merge/diff operations and quickly identify changed subparts of the tree.
2) Ordering, which allows to perform scan operations, relevant to the time-based operations.

`c` stands for the generalized container type: either Res (regular container) or Delay (lazy container, which holds possibly non-evaluated values).
-}
data RadixTree c (k ∷ Type) a = RadixTree !(c (W (Maybe a))) !(c (RadixChunk c k a)) -- both element and next is containerized, both can be left unwrapped.
  deriving (Generic)

type RadixChunk c (k ∷ Type) a = W (Reducible (RadixChunk' c k a))
data RadixChunk' c (k ∷ Type) a
  = Nil
  | Tip !Chunk !(RadixTree c k a) -- RadixTree is the only possible branch. Still could be containerized, but I'm not sure it's worth it
  | Bin !Chunk !(c (RadixChunk c k a)) !(c (RadixChunk c k a)) -- Either branch can be accessed, so containerization
  deriving (Generic)

-- | Timestamp is 4 unsigned bytes.
newtype Timestamp = Timestamp Word32
  deriving (Eq, Ord, Show, Generic)

{- | Event id, local to the timestamp.
8 highest bits represent id of the source cluster server.
24 lowest bit represent "epoch", monotonic id of event within the source cluster server within the second.
-}
newtype LocalEventId = LocalEventId Word32
  deriving (Eq, Ord, Show, Generic)

-- | Full Event ID is a combination of timestamp and local event id.
data EventId = EventId !Timestamp !LocalEventId
  deriving (Eq, Ord, Generic)

instance Show EventId where
  show (EventId (Timestamp a) (LocalEventId b)) = "#" <> show a <> "-" <> show b

-- {-
-- The rest of the file should be moved as soon as possible, but this requires to invent the functionality for
-- Dentrado to work with custom type.
-- Currently, we just hardcode all the types used in tests.
-- -}

-- {- | Model: SiteAccessLevel: enum that defines priviliges of the site's user.
-- Either user is an admin, or a moderator, or a regular user, or is simply banned (None).
-- -}
-- data SiteAccessLevel = SalNone | SalUser | SalModerator | SalAdmin
--   deriving (Eq, Show, Generic)

-- type UserId = EventId -- Users/other entities could be represnted as events that created them.
-- type LoginId = EventId

-- -- | Model: Event: enum that defines list of events that are being processed to construct a site.
-- data Event
--   = CreateUser -- #0: Marker. Is sent when a new user is created.
--   | -- | admin?, user, level
--     -- UNUSED: | | AdminRevoke !EventId !EventId -- #2: admin, user event
--     -- UNUSED: | UserCreateMessage !EventId !Bool -- #3: user, owned?
--     -- UNUSED: | UserEditMessage !EventId !EventId !(Maybe (Maybe Text, (Maybe Text, [(Text, Maybe EventId)]))) -- #3: user, message, new content?: update title?, update content?, update-set subpages
--     AdminSetAccessLevel !(Maybe UserId) !UserId !SiteAccessLevel -- #1: Is sent when some admin (or superuser) assignes new SiteAccessLevel to the user.
--   deriving (Show, Generic)

-- Util functions
-- TODO: Move them.

-- Just like from maybe
fromEmpty ∷ (Applicative m) ⇒ a → EmptyC m a → m a
fromEmpty def = runEmpty (pure def) pure
{-# INLINE fromEmpty #-}

maybeToEmpty ∷ (Has Empty sig m) ⇒ Maybe a → m a
maybeToEmpty = maybe empty pure
{-# INLINE maybeToEmpty #-}
