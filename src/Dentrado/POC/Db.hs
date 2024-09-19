{-# LANGUAGE DeriveFunctor #-}
module Dentrado.POC.Db where

import RIO
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Control.Applicative.Free (Ap, liftAp, runAp_, runAp)
import Control.Effect.Fresh (Fresh)
import Control.Carrier.State.Church (StateC)
import Data.Kind (Type)
import Control.Effect.State (get, put)
import qualified Data.Data as D
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)
import Dentrado.POC.Memory (AppIOC, (:->), Res, ValT, Val, M)
import Dentrado.POC.Types (Any1)
import Data.Dynamic (Dynamic)
import Control.Carrier.Reader (ReaderC)

$(moduleId 3)

{-
We need a way to substitute sources of Gear without modifying the gear itself.
So, uh, yes, AsmCtx, but how is it implemented?
It would have been great to actually use Reader AsmCtx, so you're able to make global source
substitutions, but "globality" could pose some issues in the long run.

When speaking of sources, do you mean "dynamic/external resources"?
I believe yes, since they are changeable and the Gear already must have the functionality to
handle the changes. However, this sounds more of a coincidence than some specific rule.
For now, let's make it so only the dynamic sources are controlled by AsmCtx, later we'll rethink this approach if needed.

To better understand the structure, let's assume the following dynamic resources:
* Gear (???)
* Multi-source events. Specifically, cluster sources and bridges. Bridges later as replicating event stores.
* External web data scraping & snapshotting

---:

okay... the idea of a global reader env sounds great and blah-blah, but, the problem is, different modules
need different CTX, you know.
Fine-grained ctx data is needed for better control anyways, whether right now or aas additional overlay.
Also, if we make ctx fine-grained, we could make an assumption that each gear *is* sensitive to the CTX, and, on any change of the structure,
Switch the underlying storage for saving the results.
-}

-- data AsmCtx = AsmCtx !(RT.Map Res (Res (Any1 Gear)) (Any1 Val)) -- TODO: does not update accordingly on ctx updates!
--   , eventSources :: ![Word8]
--   , }
-- newtype Asm m a = Asm (ReaderC AsmCtx m a)

-- data Gear out where
--   Gear :: ValT state -> state -> (state :-> Asm AppIOC (state, out)) -> Gear out

{-

So, there are two things.
First of all, there are actual gears that power the specific parts of the system.
I. e. actual reactive cells.

Second of all, there are templates, which could be provided with context (settings) to generate Gears.
THEREFORE, factory is just a function CTX -> Gear ...
That's it for the core of Dentrado, it could definitely work just this way.
However, it's worth noting that Gears satisfy a law that they are pure in terms of input, so making a CTX -> Gear is not the most performant approach
when there are quite a few similar Gears instantiated in the system.

So, therefore, we could try to model gear as this:

-}
data GearBuilder ctx out where
  UnsafeGearBuilder :: ctx :-> M AppIOC (state :-> M AppIOC (state, out)) -> GearBuilder ctx out
-- this is a normal, storeable value.

-- A "cached" version of GearBuilder, which still can be used as GearBuilder, but holds specific instantiation of ctx.
-- data Gear ctx out where
--   UnsafeGear ::
--     GearBuilder ctx out ->
--     Int {- pointer to the "external" resource being the state -} ->
--     (state :-> M AppIOC (state, out)) -> Gear ctx out

-- however, it's much better to not separate the "cache" from the Gear, making a built Gear an external resource in itself.
data Gear ctx out where
  UnsafeGear ::
    GearBuilder ctx out ->
    Int {- pointer to the external resource that stores (effective gear fn := cache) pair. -} ->
    Gear ctx out

-- Therefore, external resources:
-- 1) Can be indexed by multiple "full-formed" keys
-- 2) Can be indexed by 1 and only 1 integer-based key, which gives access to a concrete kv-pair.






-- I will strat prototyping things here, will move them out later. Thanks.

-- Желательно всё уместить в StateGraph, чтобы он был монолитным объектом.
-- Это позволит сохранить чистую семантику
-- Так что...
-- 1) Мы или делаем его полностью монолитным, включая в StateGraph информацию о самих данных и зависимостях
-- 2) Мы храним данные о сателлитах всё же отдельно
-- Временное решение: две структры, полная и расширенная
-- type DepId = Word32
-- data StateEntry s v = StateEntry !s !(RadixSet (DepId, _)) !v -- signal, dependencies and the final value
-- data StateGraph k s v = StateGraph !v !(RadixTree k (RadixZipper EventId StateEntry)) -- initial value and updates for each object
-- newtype StateGraphDeps k = StateGraphDeps (RadixTree DepId (RadixTree EventId (RadixSet k))

-- stateGraph do
--   dep1 <- _
--   dep2 <- _
--   pure
--     (_functionGetsSamplerReturnsV
--     , )

newtype Timestamp = Timestamp Word32 deriving (Eq, Ord)
-- | Event id, local to the timestamp.
-- 8 highest bits represent id of the source cluster server.
-- 24 lowest bit represent "epoch", monotonic id of event within the source cluster server within the second.
newtype LocalId = LocalId Word32 deriving (Eq, Ord)
-- | Full Event ID
data EventId = EventId !Timestamp !LocalId deriving (Eq, Ord)

instance RT.IsRadixKey EventId where
  toRadixKey (EventId (Timestamp a) (LocalId b)) = [a, b]
  fromRadixKey = \case
    [a, b] -> EventId (Timestamp a) (LocalId b)
    _ -> error "key corrupted"

{-



-}


