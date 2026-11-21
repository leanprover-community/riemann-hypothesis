import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdentityCellAdmissibleOfLift
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.IdLift

noncomputable section

namespace Formalism.MainNotions.BridgeLemma

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

section Rec

variable {D : D7}


end Rec

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))

end Formalism.MainNotions.BridgeLemma

end
