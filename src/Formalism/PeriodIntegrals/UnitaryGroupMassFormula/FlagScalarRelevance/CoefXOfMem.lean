import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FlagScalarRelevance.DualExists

noncomputable section

namespace PI.FRS

open NumberField Formalism.BasicNotions Formalism.MainNotions.S

section Local

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}




theorem e_mem_X (F : FlagG S r T) (j : Fin r) : F.e j ∈ F.X :=
  Submodule.subset_span ⟨j, rfl⟩



theorem Xa_le_X (F : FlagG S r T) (a : ℕ) : F.Xa a ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (by rintro _ ⟨i, _, rfl⟩; exact ⟨i, rfl⟩)


end Local





end PI.FRS
