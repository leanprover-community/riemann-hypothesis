import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Theta

open NumberField

section Statement

def ClassLogPeriodMean.Statement : Prop :=
  ∀ (d : ℕ) [Fact d.Prime], d % 16 = 7 →
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 →
      (∃ x : K, x ^ 2 = -(d : K)) →
      ∀ σ : K →+* ℂ,
        (classNumber K : ℝ)⁻¹ * ∑ A : ClassGroup (𝓞 K), classLogPeriod σ A =
          logPeriodConstant d

end Statement

section Ties

instance fact_sevenQ : Fact (∀ r : ℚ, r ^ 2 ≠ -7 + 0 * r) :=
  ⟨fun r h => by nlinarith [sq_nonneg r]⟩

abbrev QuadraticFieldSqrtNegSeven : Type := QuadraticAlgebra ℚ (-7) 0

instance : Algebra.IsQuadraticExtension ℚ QuadraticFieldSqrtNegSeven :=
  ⟨QuadraticAlgebra.finrank_eq_two _ _⟩

instance : NumberField QuadraticFieldSqrtNegSeven where





end Ties

end GroundTheory.Heights₂.Theta
