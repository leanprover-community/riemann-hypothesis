import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProjectionRows.Pieces

noncomputable section

namespace PI.DvRows

open NumberField IsDedekindDomain Formalism.BasicNotions PI.Dv Formalism.LFunctionChainParameters.LLcv

section Gen

variable {K : Type} [Field K] [NumberField K]

def hosEquiv : HeightOneSpectrum (𝓞 K) ≃ {p : Ideal (𝓞 K) // p.IsMaximal} where
  toFun w := ⟨w.asIdeal, w.isMaximal⟩
  invFun p := ⟨p.1, p.2.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField p.2 (RingOfIntegers.not_isField K)⟩
  left_inv w := by cases w; rfl
  right_inv p := rfl



end Gen

section Deg

variable {K : Type} [Field K] [NumberField K] [StarRing K] [NumberField.IsTotallyComplex K]




end Deg


end PI.DvRows
