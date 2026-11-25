module

public import Formalism.UnipotentAdelicQuotients.EllRegCut
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Lemma
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ :=
  VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem sobolevOfCompactSupport : BaseLevel := by
  intro d g _ _
  let B := ∫ x, ‖g x‖
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) <|
    ((integrable_rpow_neg_one_add_norm_sq (E := E d) (r := 2 * ((d : ℝ) + 1))
      (by simp; linarith)).const_mul (B ^ 2)).hasFiniteIntegral
  simp [om, ← ofReal_norm]
  rw [abs_of_nonneg (by positivity), ← ENNReal.ofReal_pow (by positivity),
    ← ENNReal.ofReal_pow (norm_nonneg _), ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [show -(2 * ((d : ℝ) + 1)) / 2 = ((-(d : ℝ) - 1) / 2) * 2 by ring,
    Real.rpow_mul (by positivity : 0 ≤ 1 + ‖ξ‖ ^ 2), Real.rpow_two, mul_comm (B ^ 2)]
  gcongr
  exact norm_fourier_le_integral_norm g ξ

end ZetaZeros.D.EllReg
