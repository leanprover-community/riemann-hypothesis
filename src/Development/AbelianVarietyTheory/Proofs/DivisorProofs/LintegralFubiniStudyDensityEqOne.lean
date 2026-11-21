import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableOnSourceIffOfDensity

section
open Set Filter Topology MeasureTheory

namespace GlobalTheory.RadialIntegral

lemma hasDerivAt_prim (m : ℕ) (a : ℝ) (ha : 0 < a) (r : ℝ) :
    HasDerivAt (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1))))
      (r * ((a + r ^ 2) ^ (m + 2))⁻¹) r := by
  have hp : 0 < a + r ^ 2 := by positivity
  have h1 : HasDerivAt (fun r : ℝ => a + r ^ 2) (2 * r) r := by
    simpa using ((hasDerivAt_pow 2 r).const_add a)
  have h2 := ((((h1.pow (m + 1)).inv (pow_ne_zero _ hp.ne')).div_const (2 * ((m : ℝ) + 1))).neg)
  refine h2.congr_deriv ?_
  simp only [Pi.pow_apply, Nat.add_sub_cancel]
  have : (m : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma tendsto_prim (m : ℕ) (a : ℝ) :
    Tendsto (fun r : ℝ => -(((a + r ^ 2) ^ (m + 1))⁻¹ / (2 * (m + 1)))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun r : ℝ => a + r ^ 2) atTop atTop :=
    tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
  have h2 : Tendsto (fun r : ℝ => (a + r ^ 2) ^ (m + 1)) atTop atTop :=
    (tendsto_pow_atTop (Nat.succ_ne_zero m)).comp h1
  simpa using ((h2.inv_tendsto_atTop).div_const (2 * ((m : ℝ) + 1))).neg

lemma radial (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal ((a ^ (m + 1))⁻¹ / (2 * (m + 1))) := by
  have hpos : ∀ r ∈ Ioi (0 : ℝ), 0 ≤ r * ((a + r ^ 2) ^ (m + 2))⁻¹ := fun r hr => by
    have : (0 : ℝ) < r := hr
    positivity
  have hint := integrableOn_Ioi_deriv_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0)
    (fun r _ => hasDerivAt_prim m a ha r) hpos (tendsto_prim m a)
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

theorem lintegral_inv_pow_add_norm_sq (m : ℕ) (a : ℝ) (ha : 0 < a) :
    ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹)
      = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  rw [← Complex.lintegral_comp_polarCoord_symm]
  have h : ∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 •
        ENNReal.ofReal (((a + ‖Complex.polarCoord.symm p‖ ^ 2) ^ (m + 2))⁻¹)
      = ∫⁻ p in polarCoord.target,
        ENNReal.ofReal (p.1 * ((a + p.1 ^ 2) ^ (m + 2))⁻¹) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
    refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun p hp => ?_)
    have h0 : 0 < p.1 := hp.1
    simp only [Complex.norm_polarCoord_symm, sq_abs, smul_eq_mul, mul_one]
    rw [ENNReal.ofReal_mul h0.le]
  rw [h, polarCoord_target, Measure.volume_eq_prod, ← Measure.prod_restrict,
    lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal (r * ((a + r ^ 2) ^ (m + 2))⁻¹))
      (g := fun _ : ℝ => (1 : ENNReal)) (by fun_prop) (by fun_prop), radial m a ha]
  simp only [lintegral_const, one_mul, MeasurableSet.univ, Measure.restrict_apply, univ_inter,
    Real.volume_Ioo]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp
  ring

end GlobalTheory.RadialIntegral
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq : ∀ (m : ℕ) (a : ℝ), 0 < a → ∫⁻ z : ℂ, ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) = ENNReal.ofReal (Real.pi / ((m + 1) * a ^ (m + 1))) := by
  atlas_forward_decl GlobalTheory.RadialIntegral.lintegral_inv_pow_add_norm_sq
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
namespace GlobalTheory.ComplexSpaceIntegral

theorem lintegral_inv_pow_add_sum_norm_sq :
    ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹)
      = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  intro n
  induction n with
  | zero =>
    intro m a ha
    rw [lintegral_unique]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add, pow_zero, one_mul]
    have : (volume : Measure (Fin 0 → ℂ)) univ = 1 := by
      rw [MeasureTheory.volume_pi, Measure.pi_univ]; simp
    rw [this, mul_one]
    congr 1
    have hf : (m.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  | succ n ih =>
    intro m a ha
    have e := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0
    rw [← (e.symm).lintegral_comp_emb (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurableEmbedding]
    rw [MeasureTheory.Measure.volume_eq_prod]
    rw [lintegral_prod]
    swap
    · apply Measurable.aemeasurable
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      apply Measurable.add measurable_const
      apply Finset.measurable_sum
      intro i _
      apply Measurable.pow_const
      apply Measurable.norm
      exact (measurable_pi_apply i).comp (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm.measurable
    have inner : ∀ z : ℂ, ∫⁻ w : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2) ^ (n + 1 + m + 1))⁻¹)
        = ENNReal.ofReal (Real.pi ^ n * (m+1).factorial / (n + (m+1)).factorial) * ENNReal.ofReal (((a + ‖z‖ ^ 2) ^ (m + 2))⁻¹) := by
      intro z
      have hz : 0 < a + ‖z‖ ^ 2 := by positivity
      have key := ih (m+1) (a + ‖z‖ ^ 2) hz
      have hsum : ∀ w : Fin n → ℂ, a + ∑ i, ‖(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℂ) 0).symm (z, w) i‖ ^ 2
          = a + ‖z‖ ^ 2 + ∑ i, ‖w i‖ ^ 2 := by
        intro w
        rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.sum_univ_succ]
        simp [Fin.insertNthEquiv, add_assoc]
      simp_rw [hsum]
      have hexp : n + 1 + m + 1 = n + (m + 1) + 1 := by ring
      rw [hexp, key, ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      rw [show m + 1 + 1 = m + 2 by ring]
      have hf : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
      have hp : (a + ‖z‖ ^ 2) ^ (m + 2) ≠ 0 := by positivity
      field_simp
    simp_rw [inner]
    rw [lintegral_const_mul _ (by
      apply ENNReal.measurable_ofReal.comp
      apply Measurable.inv
      apply Measurable.pow_const
      exact measurable_const.add (measurable_norm.pow_const 2))]
    rw [GlobalTheory.T.lintegral_complex_inv_pow_add_norm_sq m a ha, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    have h1 : ((n + (m+1)).factorial : ℝ) ≠ 0 := by positivity
    have h2 : ((n + 1 + m).factorial : ℝ) ≠ 0 := by positivity
    have h3 : (n + (m+1)) = n + 1 + m := by ring
    rw [h3, Nat.factorial_succ m]
    push_cast
    have ha' : a ^ (m+1) ≠ 0 := by positivity
    field_simp
    ring

end GlobalTheory.ComplexSpaceIntegral
end

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace : ∀ (n m : ℕ) (a : ℝ), 0 < a → ∫⁻ v : Fin n → ℂ, ENNReal.ofReal (((a + ∑ i, ‖v i‖ ^ 2) ^ (n + m + 1))⁻¹) = ENNReal.ofReal (Real.pi ^ n * m.factorial / ((n + m).factorial * a ^ (m + 1))) := by
  atlas_forward_decl GlobalTheory.ComplexSpaceIntegral.lintegral_inv_pow_add_sum_norm_sq
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

namespace GlobalTheory

theorem lintegral_fubiniStudy_density_eq_one : ∀ n : ℕ, ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n,
    ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) = 1 := by
  intro n
  have hc : (0 : ℝ) ≤ n.factorial / Real.pi ^ n := by positivity
  have hmeas : Measurable fun v : ReciprocityTheory.L2DbarEstimates.V n =>
      ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := by fun_prop
  have hsplit : ∀ v : ReciprocityTheory.L2DbarEstimates.V n,
      ENNReal.ofReal (n.factorial / Real.pi ^ n * ((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
        ENNReal.ofReal (n.factorial / Real.pi ^ n) *
          ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) := fun v => ENNReal.ofReal_mul hc
  simp_rw [hsplit]
  rw [lintegral_const_mul _ hmeas]
  have hV : ∫⁻ v : ReciprocityTheory.L2DbarEstimates.V n, ENNReal.ofReal (((1 + ‖v‖ ^ 2) ^ (n + 1))⁻¹) =
      ∫⁻ z : Fin n → ℂ, ENNReal.ofReal (((1 + ∑ i, ‖z i‖ ^ 2) ^ (n + 0 + 1))⁻¹) := by
    rw [← (FinChart.measurePreserving_toV (D := n)).lintegral_comp hmeas]
    congr 1
    funext z
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  rw [hV, GlobalTheory.T.lintegral_inv_pow_add_normSq_complexSpace n 0 1 one_pos, ← ENNReal.ofReal_mul hc]
  have hpi : Real.pi ^ n ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos n).ne'
  rw [show (n.factorial : ℝ) / Real.pi ^ n * (Real.pi ^ n * (Nat.factorial 0 : ℝ) /
      (((n + 0).factorial : ℝ) * 1 ^ (0 + 1))) = 1 by
    simp only [Nat.factorial_zero, Nat.cast_one, add_zero, one_pow, mul_one]
    field_simp]
  exact ENNReal.ofReal_one

end GlobalTheory
end
