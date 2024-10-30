module Shared.Model where

import Dentrado.POC.Gear (GearTemplate', asmGear, builtinAsmGearTemplate, events)
import qualified Dentrado.POC.StateGraph as SG
import Dentrado.POC.TH (moduleId, sFreshI)
import Dentrado.POC.Types (Event (..), SiteAccessLevel (..), UserId)
import RIO

$(moduleId 102)

{- | The Gear that processes the test input, returning the StateGraph
which associates SiteAccessLevel to each UserId throughout all points of time.
-}
status ∷ GearTemplate' () (SG.StateGraph UserId SiteAccessLevel)
status =
  $sFreshI
    $ builtinAsmGearTemplate
    $ SG.mkStateGraph
      (asmGear events)
      ( SG.StateGraphDepsNil
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
