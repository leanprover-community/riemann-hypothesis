import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralCongrOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTopFormChartIntegralZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFiniteSumTopForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousMulTopChernFormIsTopDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodPatchOfComplexPointOpenPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPoincareGoodPatchOutsideOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothPartitionOfUnityComplexPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionTopChernFormGoodPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumTransgressionDensitiesPartitionUnityEqZero

section
open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart E O H hH y hy
    · exact GlobalTheory.T.exists_poincareGoodPatch_outside_open E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => GlobalTheory.T.transgression_topChernForm_goodPatch E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm ⊤) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ hy => GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (GlobalTheory.T.hasTopFormChartIntegral_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodMetric_topChernForm_integral_eq_smooth : GlobalTheory.Published.GoodTopChernForm := by
  atlas_forward_decl GlobalTheory.GoodTop.goodTopChernForm
