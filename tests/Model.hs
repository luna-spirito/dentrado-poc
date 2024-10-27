import Control.Carrier.Reader (ask, runReader)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Gear (GearTemplate', asmGear, builtinAsmGearTemplate, confNewGear, events, runGear)
import Dentrado.POC.Memory (AppIOC (..), Env (..), EnvLoad (..), EnvStore (..), Val (..), ValT (..), sendAI)
import Dentrado.POC.StateGraph (StateGraphDeps (..))
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (Any1 (..), Event (..), EventId (..), LocalEventId (..), SiteAccessLevel (..), Timestamp (..), UserId)
import GHC.Exts (IsList (..))
import Language.Haskell.TH (newDeclarationGroup)
import RIO hiding (ask, runReader)
import RIO.List (inits)
import System.IO.Unsafe (unsafePerformIO)
import Test.QuickCheck

$(moduleId 102)

unsafeRunAppIO ∷ AppIOC a → a
unsafeRunAppIO act = unsafePerformIO do
  env ←
    Env
      <$> newIORef 0
      <*> pure mempty
      <*> newMVar mempty
      <*> pure (EnvLoad \_ → fail "not available")
      <*> pure (EnvStore \_ → fail "not available")
      <*> newMVar RT.empty
      <*> newMVar mempty
      <*> newMVar ([], 0)
  runReader env $ unAppIOC act

putEventList ∷ [(EventId, Event)] → AppIOC ()
putEventList evs = do
  evsM ← envEvents <$> ask
  sendAI $ void $ swapMVar evsM (fmap (Any1 . Val ValTEvent) <$> fromList evs, length evs)

e ∷ Word32 → EventId
e = EventId (Timestamp 0) . LocalEventId

{- | Test input: set of events, modeling the site with the concept of user access level.
Admin users can change the level of other users, including other admins.
-}
test1 ∷ [(EventId, Event)]
test1 =
  zipWith
    (\i v → (e i, v))
    [0 ..]
    [ CreateUser
    , CreateUser
    , CreateUser
    , CreateUser
    , AdminSetAccessLevel Nothing (e 0) SalAdmin -- 0 is now admin
    , AdminSetAccessLevel (Just $ e 0) (e 1) SalModerator -- 1 is now moderator
    , AdminSetAccessLevel (Just $ e 1) (e 1) SalAdmin -- denied
    , AdminSetAccessLevel (Just $ e 1) (e 3) SalModerator -- denied
    , AdminSetAccessLevel (Just $ e 0) (e 2) SalAdmin -- 2 is now admin
    , AdminSetAccessLevel (Just $ e 2) (e 1) SalNone -- 1 is now banned
    , AdminSetAccessLevel (Just $ e 2) (e 4) SalModerator -- 4 is now moderator
    ]

{- | The Gear that processes the test input, returning the StateGraph
which associates SiteAccessLevel to each UserId throughout all points of time.
-}
status ∷ GearTemplate' () (SG.StateGraph UserId SiteAccessLevel)
status =
  $sFreshI
    $ builtinAsmGearTemplate
    $ SG.mkStateGraph
      (asmGear events)
      ( StateGraphDepsNil
      , \case
          AdminSetAccessLevel adminM target level → do
            hasAccess ← case adminM of
              Nothing → pure True
              Just admin →
                SG.query admin <&> \case
                  Just SalAdmin → True
                  _ → False
            when hasAccess $ SG.update target $ pure level
          _ → pure ()
      )

-- | Test expected result.
test1Res ∷ [(UserId, [(EventId, SiteAccessLevel)])]
test1Res =
  [ (e 0, [(e 4, SalAdmin)])
  , (e 1, [(e 5, SalModerator), (e 9, SalNone)])
  , (e 2, [(e 8, SalAdmin)])
  , (e 4, [(e 10, SalModerator)])
  ]

prop_test1_oneshot_correct =
  withMaxSuccess 1
    $ test1Res
    == unsafeRunAppIO do
      status' ← confNewGear status ()
      putEventList test1
      SG.toLists =<< runGear status'

{- | This test shuffles the list of events and provides events to Dentrado one by one.
It is expected that any shuffle of the input events yields the same result, since
all events are associated with some point in time.
Dentrado, being reactive, processes these events incrementally, but might
perform expensive history rewrites to keep the result consistent.
-}
prop_test1_multishot_correct = withMaxSuccess 100 $ forAll
  (shuffle test1)
  \test1' →
    test1Res == unsafeRunAppIO do
      status' ← confNewGear status ()
      for_ @[] (inits test1') \curr → do
        _ ← runGear status'
        putEventList curr
      SG.toLists =<< runGear status'

$(newDeclarationGroup)
main ∷ IO ()
main = do
  ok ← $quickCheckAll
  unless ok exitFailure
