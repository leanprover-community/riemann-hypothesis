import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsDiscreteOfIsNormalised

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DiscSpec.ResidualModel





theorem isDiscrete_of_isNormalised (H : GlobalTheory.Published.DiscreteSpectrumResidual) {E : Type} [Field E] [NumberField E]
    [IsTotallyComplex E] {a : ℕ} (ha : 1 ≤ a) (π : CuspSub E a) (hn : IsNormalised π) :
    ∃ V : Submodule ℂ (Sm E a), IsDiscrete V ∧ IsSpehOf V π 1 :=
  ((H E a ha).2.1 a 1 π (one_mul a) hn).exists

end GlobalTheory.DiscSpec.ResidualModel

end
