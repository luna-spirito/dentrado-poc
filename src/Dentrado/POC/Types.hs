module Dentrado.POC.Types where -- probably should be moved to Dentrado.POC.Data.Types?

import RIO
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection (TypeRep)
import Data.Kind (Type)

data Dynamic1 f = forall a. Dynamic1 !(Type.Reflection.TypeRep a) !(f a)
data Any1 f = forall a. Any1 !(f a)
data Any2 f = forall a b. Any2 !(f a b)

type Chunk = Word32

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

