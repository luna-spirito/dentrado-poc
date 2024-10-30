import Dentrado.POC.Gear (confNewGear, runGear)
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.Types (Event (..), EventId (..), SiteAccessLevel (..), UserId)
import Language.Haskell.TH (newDeclarationGroup)
import RIO hiding (ask, runReader)
import RIO.List (inits)
import Test.QuickCheck
import Shared.Model
import Shared.Util
import Dentrado.POC.Memory (AppIOC)

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

-- | Test expected result.
test1Res ∷ [(UserId, [(EventId, SiteAccessLevel)])]
test1Res =
  [ (e 0, [(e 4, SalAdmin)])
  , (e 1, [(e 5, SalModerator), (e 9, SalNone)])
  , (e 2, [(e 8, SalAdmin)])
  , (e 4, [(e 10, SalModerator)])
  ]

oneshot :: [(EventId, Event)] -> (SG.StateGraph EventId SiteAccessLevel -> AppIOC r) -> r --[(UserId, [(EventId, SiteAccessLevel)])]
oneshot t renderer = unsafeRunAppIO do
  status' <- confNewGear status ()
  putEventList t
  renderer =<< runGear status'

prop_test1_oneshot_correct =
  withMaxSuccess 1
    $ test1Res
    == oneshot test1 SG.toLists

multishot :: [(EventId, Event)] -> (SG.StateGraph UserId SiteAccessLevel -> AppIOC a) -> a
multishot t renderer = unsafeRunAppIO do
  status' ← confNewGear status ()
  for_ @[] (inits t) \curr → do
    _ ← runGear status'
    putEventList curr
  renderer =<< runGear status'

{- | This test shuffles the list of events and provides events to Dentrado one by one.
It is expected that any shuffle of the input events yields the same result, since
all events are associated with some point in time.
Dentrado, being reactive, processes these events incrementally, but might
perform expensive history rewrites to keep the result consistent.
-}
prop_test1_multishot_correct = withMaxSuccess 100 $ forAllShrink
  (shuffle test1)
  (shrinkList shrinkNothing)
  \test1' →
    oneshot test1' SG.toLists == multishot test1' SG.toLists

$(newDeclarationGroup)
main ∷ IO ()
main = do
  ok ← $quickCheckAll
  unless ok exitFailure
