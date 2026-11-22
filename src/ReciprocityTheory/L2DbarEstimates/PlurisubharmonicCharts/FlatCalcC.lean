module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
public import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.MeasurableSetImageOfIsLocalHomeomorph

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal

noncomputable section

universe u

theorem fc_det_real (n : ℕ) (J : V n →L[ℂ] V n) :
    |(J.restrictScalars ℝ).det| = ‖J.det‖ ^ 2 := by
  have h : (J.restrictScalars ℝ).det = Complex.normSq J.det := by
    show LinearMap.det ((J : V n →ₗ[ℂ] V n).restrictScalars ℝ) = _
    rw [LinearMap.det_restrictScalars, Algebra.norm_complex_apply]
  rw [h, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq]

end

end ReciprocityTheory.L2DbarEstimates.Y
