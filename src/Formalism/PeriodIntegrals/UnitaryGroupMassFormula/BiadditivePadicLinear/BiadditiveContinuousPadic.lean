import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BiadditivePadicLinear.Cont2
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.ConstantCoeffSubstEqZero

noncomputable section

open Classical

namespace PI.BiaddZpLinW

open PI.BiaddZpLin PI.BeDiagZp.ContPf

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime]


theorem zc_continuous' : Continuous (zc : ℤ_[p] → ℂ_[p]) := by
  unfold zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val


end SlopeTestRemainingChoices


end PI.BiaddZpLinW
