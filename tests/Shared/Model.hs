module Shared.Model where

import Data.Constraint (Dict (..))
import qualified Dentrado.POC.Data.RadixTree as RT
import Dentrado.POC.Gear (GearTemplate', asmGear, builtinAsmGearTemplate, events')
import Dentrado.POC.Memory (InferValT, ValT, ValTWrapped' (..), builtin, inferValT, struct, unstruct, builtinValTWrapped)
import Dentrado.POC.StateGraph (Same)
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (EventId, W1 (..), W (..))
import RIO

$(moduleId 102)

{- | Model: SiteAccessLevel: enum that defines priviliges of the site's user.
Either user is an admin, or a moderator, or a regular user, or is simply banned (None).
-}
data SiteAccessLevel = SalNone | SalUser | SalModerator | SalAdmin
  deriving (Eq, Show, Generic)

instance Same SiteAccessLevel where
  same = (==)

valTSiteAccessLevel ∷ ValT (W SiteAccessLevel)
valTSiteAccessLevel = $sFreshI $ builtinValTWrapped

instance InferValT 'True (W SiteAccessLevel) where
  inferValT = valTSiteAccessLevel

type UserId = EventId -- Users/other entities could be represnted as events that created them.
type LoginId = EventId

valTEvent ∷ ValT (W Event)
valTEvent = $sFreshI builtinValTWrapped

instance InferValT 'True (W Event) where
  inferValT = valTEvent

events ∷ GearTemplate' () (RT.MapR EventId (W Event))
events = $sFreshI $ builtinAsmGearTemplate $ events' @(W Event)

-- | Model: Event: enum that defines list of events that are being processed to construct a site.
data Event
  = CreateUser -- #0: Marker. Is sent when a new user is created.
  | AdminSetAccessLevel !(W1 Maybe UserId) !UserId !(W SiteAccessLevel) -- #1: Is sent when some admin (or superuser) assignes new SiteAccessLevel to the user.
  deriving (Show, Generic)

{- | The Gear that processes the test input, returning the StateGraph
which associates SiteAccessLevel to each UserId throughout all points of time.
-}
status ∷ GearTemplate' () (SG.StateGraph UserId (W SiteAccessLevel))
status =
  $sFreshI
    $ builtinAsmGearTemplate
    $ SG.mkStateGraph
      (asmGear events)
      ( SG.StateGraphDepsNil
      , unW >>> \case
          AdminSetAccessLevel (W1 adminM) target level → do
            hasAccess ← case adminM of
              Nothing → pure True
              Just admin →
                SG.query admin <&> \case
                  Just (W SalAdmin) → True
                  _ → False
            when hasAccess $ SG.update target $ pure level
          _ → pure ()
      )
