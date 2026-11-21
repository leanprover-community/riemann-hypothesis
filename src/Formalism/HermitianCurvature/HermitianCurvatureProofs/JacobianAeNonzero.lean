import Formalism.HermitianCurvature.HermitianCurvatureProofs.LinearChangeOfVariablesBis
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FourthWeightDensityOfParts

open Matrix Formalism.FourierDecayAlt MeasureTheory
open scoped ENNReal

namespace Formalism.FourierDecayAlt.P

namespace RootChangeOfVariables

lemma jac (c : ℂ) :
    ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det = Complex.normSq c := by
  have e : ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ : ℂ →L[ℝ] ℂ).toLinearMap =
      (LinearMap.mulLeft ℂ c).restrictScalars ℝ := by
    ext x; simp [mul_comm]
  rw [ContinuousLinearMap.det, e, LinearMap.det_restrictScalars, LinearMap.det_mulLeft,
    Algebra.norm_complex_apply]

lemma ae_ne_zero : ∀ᵐ D : ℂ, D ∈ {D : ℂ | D ≠ 0} := by
  rw [ae_iff]
  have : {a : ℂ | ¬ a ∈ {D : ℂ | D ≠ 0}} = {0} := by ext a; simp
  rw [this, measure_singleton]

end RootChangeOfVariables

open RootChangeOfVariables



end Formalism.FourierDecayAlt.P
