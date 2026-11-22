module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.BasicNotions.V1

open IsLocalRing MvPowerSeries
open scoped Classical

attribute [instance] IsCNL.noeth IsCNL.complete IsCNL.localHom

attribute [instance] TR.cr TR.lr TR.al TR.cnl

end Formalism.BasicNotions.V1

namespace Formalism.BasicNotions.V1

open IsLocalRing MvPowerSeries
open scoped Classical

attribute [instance] LiftProb.oR LiftProb.oD LiftProb.oV LiftProb.oC LiftProb.o0 LiftProb.oF
  LiftProb.oP LiftProb.gG LiftProb.gT LiftProb.gTG LiftProb.gC LiftProb.gTD LiftProb.lF LiftProb.qF
  LiftProb.rF

end Formalism.BasicNotions.V1

namespace Formalism.MainNotions.UnusedSlot38

open Formalism.BasicNotions.V1 IsLocalRing MvPowerSeries
open scoped Classical

section Prob

variable (P : LiftProb)

end Prob

end Formalism.MainNotions.UnusedSlot38
