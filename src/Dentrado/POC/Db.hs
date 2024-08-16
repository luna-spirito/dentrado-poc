{-# LANGUAGE DeriveFunctor #-}
module Dentrado.POC.Db where

import RIO
import qualified Dentrado.POC.Data.RadixTree as RT
import Control.Algebra
import Dentrado.POC.Data.Container (Res (..), FreshIOC, ResPOC (..), alloc, Cast (cast), FreshIO, fetch)
import Control.Applicative.Free (Ap, liftAp, runAp_, runAp)
import Control.Effect.Fresh (Fresh)
import Control.Carrier.State.Church (StateC)
import Data.Kind (Type)
import Control.Effect.State (get, put)
import qualified Data.Data as D
import qualified RIO.Partial as P
import Dentrado.POC.TH (moduleId)

$(moduleId 3)

-- To avoid problems with impredicativity, I'll try using monomorphic SnapshotC here.
data AnyValue = forall a. Typeable a => AnyValue a

data Gear e a where
  UnsafeGear :: forall cache e a. Typeable cache
    => FreshIOC (cache, RT.SetR (GearId e))
    -> (forall s. cache -> SnapshotC e s (cache, a))
    -> (cache -> cache -> FreshIOC (RT.SetR (GearId e)) -> FreshIOC (Maybe (RT.SetR (GearId e))))
    -> Gear e a

data AnyGear e = forall b. Typeable b => AnyGear (Gear e b)
instance Cast (Res (Gear e a)) (GearId e) where -- I have many questions, but probably not the best time to ask them
  cast (Res i _) = ResPOC i
type GearId e = ResPOC (AnyGear e)

data Snapshot e s (m :: Type -> Type) a where
  SnapshotEvents :: Snapshot e s m e
  SnapshotUnsafeReadGear :: Res (Gear e a) -> Snapshot e s m a

data StorePOC e = StorePOC { events :: !e, gears :: !(RT.MapR (GearId e) AnyValue), gearsPins :: !(RT.MapR (GearId e) (RT.SetR (GearId e))) }
newtype SnapshotC e s a = SnapshotC { runSnapshotC :: StateC (StorePOC e) FreshIOC a } -- Use RT
  deriving (Functor, Applicative, Monad)

instance Algebra (Snapshot e s :+: FreshIO) (SnapshotC e s) where
  alg hdl sig ctx = case sig of
      L SnapshotEvents -> do
        store <- SnapshotC $ get @(StorePOC e)
        pure $ ctx $> store.events
      L (SnapshotUnsafeReadGear gearR) -> do
        store <- SnapshotC $ get @(StorePOC e)
        let gearId = cast @_ @(GearId e) gearR
        UnsafeGear initial upd getPinsUpd <- fetch gearR
        (oldCache, initialPins) <- SnapshotC $
          RT.lookup (RT.selEq gearId) store.gears >>= \case
            Just x -> pure (P.fromJust $ D.cast x, Nothing)
            Nothing -> second Just <$> lift initial
        (newCache, output) <- upd oldCache
        newGears <- RT.insert (RT.selEq gearId) (AnyValue newCache) store.gears
        newPins <- SnapshotC $ lift $ getPinsUpd oldCache newCache (maybe (P.fromJust <$> RT.lookup (RT.selEq gearId) store.gearsPins) pure initialPins)
        newGearsPins <- case newPins <|> initialPins of
          Nothing -> pure store.gearsPins
          Just x -> RT.insert (RT.selEq gearId) x store.gearsPins
        SnapshotC $ put $ store { gears = newGears, gearsPins = newGearsPins }
        pure $ ctx $> output
      R other -> SnapshotC $ alg (runSnapshotC . hdl) (R other) ctx

-- TODO: RT/DAG garbage collection & reachability
-- collectGarbage :: (RT.RadixTree

-- Monopair is used to perform monadic actions with two results.
-- It tries its best to share parts of the computation, but >>= could break sharing pretty quickly.

-- TODO: Evaluate performance... I believe it's not good. Check that places where Monopair is used don't break it.
newtype Monopair m a = Monopair (forall b. (a -> m b) -> ((a, a) -> m b) -> m b)
  deriving Functor

runMonopair :: (a -> m b) -> ((a, a) -> m b) -> Monopair m a -> m b
runMonopair p c (Monopair r) = r p c

instance Applicative (Monopair m) where
  pure x = Monopair \p _ -> p x
  {-# INLINE pure #-}
  Monopair r1 <*> Monopair r2 = Monopair \p choice -> r1
    (\f -> r2 (p . f) (\(a1, a2) -> choice (f a1, f a2)))
    (\(f1, f2) -> r2 (\a -> choice (f1 a, f2 a)) (\(a1, a2) -> choice (f1 a1, f2 a2)))
  {-# INLINE (<*>) #-}

monGetLRAnd :: ((a, a) -> a) -> Monopair m a -> (a -> m b) -> m b
monGetLRAnd f m c = runMonopair c (c . f) m

monTwo :: (a, a) -> Monopair m a
monTwo a = Monopair \_ c -> c a

instance Monad (Monopair m) where
  Monopair aM >>= f = Monopair \p choice -> aM
    (runMonopair p choice . f)
    (\(a1, a2) -> monGetLRAnd fst (f a1) \b1 -> monGetLRAnd snd (f a2) \b2 -> choice (b1, b2))
  {-# INLINE (>>=) #-}

{-
instance Algebra sig m => Algebra (Choose :+: sig) (Monopair m) where
  alg hdl sig ctx = Monopair \p choice -> case sig of
      L Choose -> choice (ctx $> True, ctx $> False)
      R other -> thread (dst ~<~ hdl) other (pure ctx) >>= run . runMonopair (coerce p) (coerce choice)
    where
      two :: (a, a) -> Monopair Identity a
      two a = Monopair \_ c -> c a
      dst :: Monopair Identity (Monopair m x1) -> m (Monopair Identity x1)
      dst = run . runMonopair
        (pure . runMonopair (pure . pure) (pure . two))
        (pure . \(l, r) -> monGetLRAnd fst l \l' -> monGetLRAnd snd r \r' -> pure $ two (l', r'))
  {-# INLINE alg #-}

cascadeUpdate :: Monad m => (u -> a -> m (Maybe (u, a))) -> u -> a -> m a
cascadeUpdate f origU origA = f origU origA >>= \case
  Nothing -> pure origA
  Just (u, a) -> cascadeUpdate f u a

-- invariant: keysOf origPins == keysOf oldUses
collectGarbage :: forall sig m k. Has FreshIO sig m => RT.MapR k (RT.SetR k) -> RT.MapR k (RT.SetR k) -> RT.MapR k Int -> m (RT.MapR k (RT.SetR k), RT.MapR k Int)
collectGarbage origPins newPins oldUses = do
    _
  where
    mergePinUpds :: Res (RT.MapR k Integer) -> Res (RT.MapR k Integer) -> Monopair m (RT.MapR k Integer)
    mergePinUpds = _
    getRemovesAdds :: m (RT.MapR k Integer, RT.MapR k Integer)
    getRemovesAdds = runMonopair (\x -> pure (x, x)) pure $
      ($sFreshI $ RT.diffF
        (\a b -> do
          a' <- fetch a -- TODO: something needs to be done with Res (Maybe a)
          case a' of
            Nothing -> fetch b
            Just a'' -> alloc a'' >>= \a''' -> mergePinUpds a''' b)
        (const $ const \a b -> alloc =<< mergePinUpds a b)
        (const alloc)
        (pure RT.sEmpty)
        AppForce
        (alloc . Just <=< uncurry getUniquesInSets . RT.mapDiffEToPair RT.empty)
      ) origPins newPins
    getUniquesInSets :: RT.SetR k -> RT.SetR k -> Monopair m (RT.MapR k Integer)
    getUniquesInSets = $sFreshI $ RT.diff AppForce \mapDiffE ->
      case cast mapDiffE of
        Nothing -> pure sNothing
        Just RT.SetAdd -> monTwo (sNothing, sJust1)
        Just RT.SetDel -> monTwo (sJust1, sNothing)
    sJust1 = $sFreshI $ alloc (Just 1)
    sSNil = $sFreshI $ alloc RT.sEmpty
-}
collectGarbage :: forall sig m k. Has FreshIO sig m => RT.MapR k (RT.SetR k) -> RT.MapR k (RT.SetR k) -> RT.MapR k Int -> m (RT.MapR k (RT.SetR k), RT.MapR k Int)
collectGarbage _origPins newPins oldUses = traceM "gc unimplemented" $> (newPins, oldUses)

data AssemblyF e s a where
  AssemblyF :: Res (Gear e a) -> AssemblyF e s (SnapshotC e s a)
type Assembly e s = Ap (AssemblyF e s)

liftGear :: Res (Gear e a) -> Assembly e s (SnapshotC e s a)
liftGear = liftAp . AssemblyF

newtype EndoM m a = EndoM { appEndoM :: a -> m a }
instance Monad m => Semigroup (EndoM m a) where
  EndoM a <> EndoM b = EndoM (a <=< b)
instance Monad m => Monoid (EndoM m a) where
  mempty = EndoM pure

withGear :: forall cache e s2 a sig1 m1. (Typeable cache, Has Fresh sig1 m1) => FreshIOC cache -> (forall s1. Assembly e s1 (cache -> SnapshotC e s1 (cache, a))) -> m1 (Assembly e s2 (SnapshotC e s2 a))
withGear cacheM asm =
  let deps = appEndoM
        (runAp_
          (\(AssemblyF gear) -> EndoM $ RT.insert (RT.selEq $ cast gear) ())
          asm)
        RT.empty
      bodyf :: forall s3. cache -> SnapshotC e s3 (cache, a)
      bodyf = run (runAp (\(AssemblyF gear) -> pure (send (SnapshotUnsafeReadGear @_ @_ @s3 gear))) asm)
  in liftGear <$> alloc (UnsafeGear
    ((,) <$> cacheM <*> deps)
    bodyf
    (const $ const $ const $ pure Nothing)
  )

{-
Предположение: никакие два сервера и не имеют один и тот же ServerId.
Если это всё же происходит, события с дублирующимся идентификатром сохраняются отдельно и не учитываются.

Существует ли понятие кластера?
Я думаю, что да. Физические устройства кому-то принадлежат. Следовательно, в конечном итоге
они подчинены лицу, ими владеющими, а не "друг другу"
Подобная система не предполагает, что различными устройствами кластера владеют разные личности, но подобный подход
изначально небезопасный и его нужно избегать.

Следовательно, существует кластер. В кластер входят устройства. Устройства подчиняются командам кластера.
Команды управления кластером отдельны от иных событий и используются строго для того, чтобы *обновлять* текущее состояние
кластера. Существует исключительно сейчас, следовательно, команды по типу Revoke/Inject не применимы к событиям-операциям над кластером.

Всякое событие или помещается под тем идентификатором, под которым оно было задано источником, или вообще не размещается.
По возможности используем ссылки не на EventId, а на Id (простые глобальные Fresh'ы), чтобы минимизировать проблемы с поражением истории

Каждый новый запуск сервера создаёт новый лог, привязан к Timestamp.

SERVERID = 0 IS RESERVED FOR CLUSTER OPERATIONS

let Event = type < ClusterEvent : ClusterEvent | DataEvent : DataEvent >
let ClusterEvent = type < Trust : { server : ServerId, do : Boolean } >
type User = type < Core : {} | User : Id >
let DataEvent = type 
  { senderUser : Maybe User
  , event :
    < Now : SiteEvent
    | Revoke : { event : EventId } 
    | Inject : { time: Timestamp, event : SiteEvent } >}
let SiteEvent = type
  < SetUserLevel : { constrainedToThread : Id, level : < None | Member | Admin > }
  | UpdateUser : { forceUser : User, val : { name : Maybe Text, password: Maybe () } }
  | UpdatePost : { id : Id, val : { title : Maybe Text, value : Maybe Text, answers : Maybe Id } }>
-}


