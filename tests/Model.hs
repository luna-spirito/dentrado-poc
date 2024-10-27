import Control.Carrier.Reader (ask, runReader)
import Data.List (head)
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Gear (GearTemplate', asmGear, builtinAsmGearTemplate, confNewGear, events, runGear)
import Dentrado.POC.Memory (AppIOC (..), Env (..), EnvLoad (..), EnvStore (..), Val (..), ValT (..), sendAI)
import Dentrado.POC.StateGraph (StateGraphDeps (..))
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (Any1 (..), Event (..), EventId (..), LocalId (..), SiteAccessLevel (..), Timestamp (..))
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
e = EventId (Timestamp 0) . LocalId

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

type UserId = EventId
type LoginId = EventId

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

prop_test1_multishot_correct = withMaxSuccess 100 $ forAll
  (shuffle test1) -- TODO: SHUFFLE!!!
  \test1' →
    test1Res == unsafeRunAppIO do
      -- traceM "running new"
      status' ← confNewGear status ()
      for_ @[] (inits test1') \curr → do
        _ ← runGear status'
        putEventList curr
      res ← SG.toLists =<< runGear status'
      -- traceShowM res
      pure res

-- prop_
-- unsafeRunAppIO testSuite (runGear =<< confNewGear status ())

$(newDeclarationGroup)
main ∷ IO ()
main = do
  ok ← $quickCheckAll
  unless ok exitFailure
