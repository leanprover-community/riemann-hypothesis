import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FrameDeterminant.FrameA

noncomputable section

open NumberField

namespace PI.FlagFrameDeterminants

open Formalism.MainNotions.S Formalism.MainNotions.S.Lat PI.IsoDetDefs

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}




theorem e_mem_xa (F : FlagG S r T) {j : ℕ} (a : Fin r) (ha : a.val < j) : F.e a ∈ F.Xa j :=
  Submodule.subset_span ⟨a, ha, rfl⟩


end Gen

end PI.FlagFrameDeterminants
