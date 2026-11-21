import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SectionsCoordsAndNonvanishingAtFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvatureLowerBoundOnCoverBalls
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyAtlasBallPartitionCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2ExtensionEtaleCoordinatesFiniteZeros

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.JacSec

noncomputable section

def jacM {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n) : V n →L[ℂ] V n :=
  ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n).comp
    (ContinuousLinearMap.pi fun k => f0 v • fderiv ℂ (f k) v - f k v • fderiv ℂ f0 v)

theorem jacM_apply {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v ξ : V n) (k : Fin n) :
    (jacM f0 f v ξ).ofLp k = f0 v * fderiv ℂ (f k) v ξ - f k v * fderiv ℂ f0 v ξ := by
  simp [jacM]

theorem jacM_congr {n : ℕ} {f0 g0 : V n → ℂ} {f g : Fin n → V n → ℂ} {v : V n}
    (h0 : f0 =ᶠ[𝓝 v] g0) (h : ∀ k, f k =ᶠ[𝓝 v] g k) : jacM f0 f v = jacM g0 g v := by
  ext ξ k
  rw [jacM_apply, jacM_apply, h0.fderiv_eq, (h k).fderiv_eq, h0.eq_of_nhds, (h k).eq_of_nhds]

theorem jacM_trans {n : ℕ} (G : V n → ℂ) (Φ : V n → V n) (h0 : V n → ℂ) (h : Fin n → V n → ℂ)
    (v : V n) (hG : DifferentiableAt ℂ G v) (hΦ : DifferentiableAt ℂ Φ v)
    (hh0 : DifferentiableAt ℂ h0 (Φ v)) (hh : ∀ k, DifferentiableAt ℂ (h k) (Φ v)) :
    jacM (fun w => G w * h0 (Φ w)) (fun k w => G w * h k (Φ w)) v =
      (G v ^ 2) • (jacM h0 h (Φ v)).comp (fderiv ℂ Φ v) := by
  have d0 : fderiv ℂ (fun w => G w * h0 (Φ w)) v =
      G v • ((fderiv ℂ h0 (Φ v)).comp (fderiv ℂ Φ v)) + h0 (Φ v) • fderiv ℂ G v :=
    (hG.hasFDerivAt.mul (hh0.hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  have dk : ∀ k, fderiv ℂ (fun w => G w * h k (Φ w)) v =
      G v • ((fderiv ℂ (h k) (Φ v)).comp (fderiv ℂ Φ v)) + h k (Φ v) • fderiv ℂ G v := fun k =>
    (hG.hasFDerivAt.mul ((hh k).hasFDerivAt.comp v hΦ.hasFDerivAt)).fderiv
  ext ξ k
  rw [jacM_apply, d0, dk]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, jacM_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul, PiLp.smul_apply]
  ring

theorem det_smul_V {n : ℕ} (c : ℂ) (M : V n →L[ℂ] V n) : (c • M).det = c ^ n * M.det := by
  rw [ContinuousLinearMap.det, ContinuousLinearMap.coe_smul, LinearMap.det_smul,
    finrank_euclideanSpace_fin]

theorem jacM_det_diffAt {n : ℕ} {f0 : V n → ℂ} {f : Fin n → V n → ℂ} {U : Set (V n)}
    (hU : IsOpen U) (h0 : DifferentiableOn ℂ f0 U) (h : ∀ k, DifferentiableOn ℂ (f k) U)
    {v : V n} (hv : v ∈ U) : DifferentiableAt ℂ (fun w => (jacM f0 f w).det) v := by
  have c0 : ContDiffOn ℂ ∞ f0 U := ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU h0
  have ck : ∀ k, ContDiffOn ℂ ∞ (f k) U := fun k =>
    ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hU (h k)
  have d0 : ContDiffOn ℂ ∞ (fderiv ℂ f0) U := c0.fderiv_of_isOpen hU (by simp)
  have dk : ∀ k, ContDiffOn ℂ ∞ (fderiv ℂ (f k)) U := fun k =>
    (ck k).fderiv_of_isOpen hU (by simp)
  have hn := hU.mem_nhds hv
  have hc : ContDiffAt ℂ ∞ (fun w => (jacM f0 f w).det) v := by
    simp_rw [flL_det_eq, jacM_apply]
    refine ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun c _ => ?_)
    exact ((c0.contDiffAt hn).mul (((dk _).contDiffAt hn).clm_apply contDiffAt_const)).sub
      (((ck _).contDiffAt hn).mul ((d0.contDiffAt hn).clm_apply contDiffAt_const))
  exact hc.differentiableAt (by simp)

theorem zLoc_fderiv {n : ℕ} (f0 : V n → ℂ) (f : Fin n → V n → ℂ) (v : V n)
    (h0 : DifferentiableAt ℂ f0 v) (h : ∀ k, DifferentiableAt ℂ (f k) v) (hne : f0 v ≠ 0) :
    fderiv ℂ (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) v =
      ((f0 v ^ 2)⁻¹) • jacM f0 f v := by
  have hinv : HasFDerivAt (fun w => (f0 w)⁻¹) (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) v :=
    (hasDerivAt_inv hne).comp_hasFDerivAt v h0.hasFDerivAt
  have hk : ∀ k, HasFDerivAt (fun w => f k w / f0 w)
      (f k v • (-((f0 v) ^ 2)⁻¹ • fderiv ℂ f0 v) + (f0 v)⁻¹ • fderiv ℂ (f k) v) v := by
    intro k
    exact ((h k).hasFDerivAt.mul hinv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun w => by simp [div_eq_mul_inv])
  have hpi := hasFDerivAt_pi.2 hk
  have hE := ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm :
    (Fin n → ℂ) →L[ℂ] V n).hasFDerivAt.comp v hpi
  rw [show (fun w => (WithLp.toLp 2 (fun k => f k w / f0 w) : V n)) =
    (((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm : (Fin n → ℂ) →L[ℂ] V n) ∘
      fun w k => f k w / f0 w) from rfl, hE.fderiv]
  ext ξ k
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, PiLp.smul_apply,
    jacM_apply, smul_eq_mul]
  simp
  field_simp
  ring

theorem jac_section : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → ∃ J : ι → Y → ℂ, A.IsSec (A.kap + (2 * n) • B) J ∧ ∀ i y, y ∈ (A.chart i).source → t0 i y ≠ 0 → J i y = t0 i y ^ (2 * n) * (fderiv ℂ (A.zLoc t0 t i) (A.chart i y)).det := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t h0 ht
  have hd0 : ∀ i, DifferentiableOn ℂ (t0 i ∘ (A.chart i).symm) (A.chart i).target := fun i => by
    simpa using h0.1 i
  have hdk : ∀ i k, DifferentiableOn ℂ (t k i ∘ (A.chart i).symm) (A.chart i).target :=
    fun i k => by simpa using (ht k).1 i
  refine ⟨fun i y => (jacM (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
    (A.chart i y)).det, ⟨fun i => ?_, ?_⟩, ?_⟩
  · intro v hv
    have hvt : v ∈ (A.chart i).target := hv.1
    exact (jacM_det_diffAt (A.chart i).open_target (hd0 i) (hdk i) hvt).differentiableWithinAt.congr
      (fun w hw => by simp [(A.chart i).right_inv hw.1]) (by simp [(A.chart i).right_inv hvt])
  · intro i j y _ hi hj
    have hov : IsOpen (ovl A.chart i j) :=
      (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
    have hmov : A.chart i y ∈ ovl A.chart i j :=
      ⟨(A.chart i).map_source hi, by simp [(A.chart i).left_inv hi, hj]⟩
    have hΦv : (A.chart j ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp [(A.chart i).left_inv hi]
    have hEv : ∀ s : ι → Y → ℂ, A.IsSec B s → s i ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        fun w => (A.g B i j ∘ (A.chart i).symm) w *
          (s j ∘ (A.chart j).symm) ((A.chart j ∘ (A.chart i).symm) w) := by
      intro s hs
      filter_upwards [hov.mem_nhds hmov] with w hw
      have hsi : (A.chart i).symm w ∈ (A.chart i).source := (A.chart i).map_target hw.1
      simp only [Function.comp_apply]
      rw [(A.chart j).left_inv hw.2]
      exact hs.2 i j _ trivial hsi hw.2
    have hG : DifferentiableAt ℂ (A.g B i j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_g B i j).differentiableAt (hov.mem_nhds hmov)
    have hΦ : DifferentiableAt ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) :=
      (A.holo_trans i j).differentiableAt (hov.mem_nhds hmov)
    have hjt : (A.chart j).target ∈ 𝓝 ((A.chart j ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hΦv]; exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
    have key := jacM_trans (A.g B i j ∘ (A.chart i).symm) (A.chart j ∘ (A.chart i).symm)
      (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart i y) hG hΦ
      ((hd0 j).differentiableAt hjt) (fun k => (hdk j k).differentiableAt hjt)
    rw [hΦv] at key
    have hcong := jacM_congr (hEv t0 h0) (fun k => hEv (t k) (ht k))
    have hdc : ((jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm)
        (A.chart j y)).comp (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y))).det =
        (jacM (t0 j ∘ (A.chart j).symm) (fun k => t k j ∘ (A.chart j).symm) (A.chart j y)).det *
        (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y)).det := LinearMap.det_comp _ _
    simp only
    rw [hcong, key, det_smul_V, hdc, A.g_add _ _ i j y hi hj, bsA_g_nsmul A B _ hi hj,
      A.g_kap i j y hi hj]
    simp only [Function.comp_apply, (A.chart i).left_inv hi]
    rw [← pow_mul]
    ring
  · intro i y hi hne
    have hyt : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
    have hn := (A.chart i).open_target.mem_nhds hyt
    have hne' : (t0 i ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
      simpa [(A.chart i).left_inv hi] using hne
    have hz := zLoc_fderiv (t0 i ∘ (A.chart i).symm) (fun k => t k i ∘ (A.chart i).symm)
      (A.chart i y) ((hd0 i).differentiableAt hn) (fun k => (hdk i k).differentiableAt hn) hne'
    have hzl : A.zLoc t0 t i = fun w => (WithLp.toLp 2 (fun k =>
        (t k i ∘ (A.chart i).symm) w / (t0 i ∘ (A.chart i).symm) w) : V n) := rfl
    simp only
    rw [hzl, hz, det_smul_V]
    simp only [Function.comp_apply, (A.chart i).left_inv hi] at hne' ⊢
    rw [← mul_assoc, ← inv_pow, pow_mul, ← mul_pow]
    rw [show t0 i y ^ 2 * (t0 i y)⁻¹ ^ 2 = 1 by field_simp, one_pow, one_mul]

end

end GlobalTheory.JacSec
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_jacobian_section_canonical_weight : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → ∃ J : ι → Y → ℂ, A.IsSec (A.kap + (2 * n) • B) J ∧ ∀ i y, y ∈ (A.chart i).source → t0 i y ≠ 0 → J i y = t0 i y ^ (2 * n) * (fderiv ℂ (A.zLoc t0 t i) (A.chart i y)).det := by
  atlas_forward_decl GlobalTheory.JacSec.jac_section
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

section QuotEtale

variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La) {B : La} {t0 : ι → Y → ℂ} {t : Fin n → ι → Y → ℂ}

end QuotEtale

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
variable {n : ℕ} {Y : Type} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι La : Type} [AddCommGroup La] in
private lemma sec_eq_transition_mul {A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La} {B : La} {s : ι → Y → ℂ}
    (hs : A.IsSec B s) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : s i y = A.g B i j y * s j y := by
  have h := hs
  unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at h
  exact h.2 i j y (Set.mem_univ y) hi hj

open MeasureTheory Filter Topology Metric in
open scoped ENNReal ContDiff in
theorem _root_.GlobalTheory.OTY.etale_zmap_main : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y),
    A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U →
    (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → _root_.GlobalTheory.OTY.Etale A U (A.zmap t0 t) := by
  intro n Y _ _ _ _ _ ι La _ A B t0 t U h0 ht hU hcoord
  have hne : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source → t0 i y ≠ 0 := by
    intro i y hy hi
    rw [sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact mul_ne_zero (A.g_ne B i _ y hi (A.mem_pick y)) (hcoord y hy).1
  have hz : ∀ i, ∀ y ∈ U, y ∈ (A.chart i).source →
      A.zmap t0 t y = A.zLoc t0 t i (A.chart i y) := by
    intro i y hy hi
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zmap _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    rw [(A.chart i).left_inv hi]
    congr 1
    funext k
    rw [sec_eq_transition_mul (ht k) hi (A.mem_pick y),
      sec_eq_transition_mul h0 hi (A.mem_pick y)]
    exact (mul_div_mul_left _ _ (A.g_ne B i _ y hi (A.mem_pick y))).symm
  have hloc : ∀ i, DifferentiableOn ℂ (A.zLoc t0 t i)
      ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
    intro i
    apply (differentiableOn_piLp (𝕜 := ℂ) 2).2
    intro k
    have hk := ht k
    have h0' := h0
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSec _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsSecOn at hk h0'
    have hsub : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
        (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, Set.mem_univ _⟩
    have hnum : DifferentiableOn ℂ (fun v => t k i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hk.1 i).mono hsub
    have hden : DifferentiableOn ℂ (fun v => t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (h0'.1 i).mono hsub
    have hdiv : DifferentiableOn ℂ
        (fun v => t k i ((A.chart i).symm v) / t0 i ((A.chart i).symm v))
        ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := by
      simp only [div_eq_mul_inv]
      exact hnum.mul (hden.inv fun v hv => hne i _ hv.2 ((A.chart i).map_target hv.1))
    unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.zLoc
    exact hdiv
  refine ⟨hU, ?_, ?_⟩
  · intro i
    refine (hloc i).congr ?_
    intro v hv
    simp only [Function.comp_apply]
    rw [hz i _ hv.2 ((A.chart i).map_target hv.1), (A.chart i).right_inv hv.1]
  · intro i y hy hi
    unfold _root_.GlobalTheory.OTY.jdet _root_.GlobalTheory.OTY.jz
    set j := A.pick y with hj_def
    have hj : y ∈ (A.chart j).source := A.mem_pick y
    have hV : (A.chart i).target ∩ (A.chart i).symm ⁻¹' (U ∩ (A.chart j).source) ∈
        𝓝 (A.chart i y) := by
      refine ((A.chart i).isOpen_inter_preimage_symm (hU.inter (A.chart j).open_source)).mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact ⟨hy, hj⟩
    have heq : A.zmap t0 t ∘ (A.chart i).symm =ᶠ[𝓝 (A.chart i y)]
        A.zLoc t0 t j ∘ ((A.chart j) ∘ (A.chart i).symm) := by
      filter_upwards [hV] with v hv
      simp only [Function.comp_apply]
      exact hz j _ hv.2.1 hv.2.2
    rw [heq.fderiv_eq]
    have hT : DifferentiableAt ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) := by
      refine (A.holo_trans i j).differentiableAt ?_
      have ho : IsOpen ((A.chart i).target ∩ (A.chart i).symm ⁻¹' (A.chart j).source) :=
        (A.chart i).isOpen_inter_preimage_symm (A.chart j).open_source
      refine ho.mem_nhds ?_
      refine ⟨(A.chart i).map_source hi, ?_⟩
      simp only [Set.mem_preimage, (A.chart i).left_inv hi]
      exact hj
    have hTy : ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) = A.chart j y := by
      simp only [Function.comp_apply, (A.chart i).left_inv hi]
    have hL : DifferentiableAt ℂ (A.zLoc t0 t j) (((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) := by
      rw [hTy]
      refine (hloc j).differentiableAt ?_
      refine ((A.chart j).isOpen_inter_preimage_symm hU).mem_nhds ?_
      refine ⟨(A.chart j).map_source hj, ?_⟩
      simp only [Set.mem_preimage, (A.chart j).left_inv hj]
      exact hy
    rw [fderiv_comp _ hL hT, hTy]
    have hdet : LinearMap.det (((fderiv ℂ (A.zLoc t0 t j) (A.chart j y)).comp
        (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y)) : _root_.ReciprocityTheory.L2DbarEstimates.V n →L[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :
          _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) =
        LinearMap.det (fderiv ℂ (A.zLoc t0 t j) (A.chart j y) : _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) *
          LinearMap.det (fderiv ℂ ((A.chart j) ∘ (A.chart i).symm) (A.chart i y) :
            _root_.ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] _root_.ReciprocityTheory.L2DbarEstimates.V n) :=
      LinearMap.det_comp _ _
    rw [ContinuousLinearMap.det, hdet]
    refine mul_ne_zero ?_ ?_
    · have hc := (hcoord y hy).2
      unfold _root_.ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.IsCoordAt at hc
      exact hc
    · have hk := A.g_kap i j y hi hj
      have hg := A.g_ne A.kap i j y hi hj
      rw [hk] at hg
      exact hg

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCoordinates_section_quotients : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (B : La) (t0 : ι → Y → ℂ) (t : Fin n → ι → Y → ℂ) (U : Set Y), A.IsSec B t0 → (∀ j, A.IsSec B (t j)) → IsOpen U → (∀ y ∈ U, t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y) → Etale A U (A.zmap t0 t) := by
  atlas_forward_decl GlobalTheory.OTY.etale_zmap_main
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY.LinComb

open Polynomial in

theorem exists_pow_ne_zero {Y : Type} (N : ℕ) (T : Finset Y) (v : Y → Fin N → ℂ)
    (hv : ∀ P ∈ T, v P ≠ 0) : ∃ x : ℂ, ∀ P ∈ T, ∑ k : Fin N, x ^ (k : ℕ) * v P k ≠ 0 := by
  classical
  let q : Y → ℂ[X] := fun P => ∑ k : Fin N, C (v P k) * X ^ (k : ℕ)
  have hcoeff : ∀ P (k : Fin N), (q P).coeff k = v P k := by
    intro P k
    simp only [q, finset_sum_coeff, coeff_C_mul_X_pow, Fin.val_inj]
    simp
  have hq : ∀ P ∈ T, q P ≠ 0 := by
    intro P hP h0
    apply hv P hP
    funext k
    have := hcoeff P k
    rw [h0, coeff_zero] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset (T.biUnion fun P => (q P).roots.toFinset)
  refine ⟨x, fun P hP h => hx ?_⟩
  rw [Finset.mem_biUnion]
  refine ⟨P, hP, ?_⟩
  rw [Multiset.mem_toFinset, mem_roots (hq P hP), IsRoot.def]
  simp only [q, eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]
  rw [← h]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

end GlobalTheory.OTY.LinComb

theorem GlobalTheory.OTY.exists_linComb_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ ι La _ A L N s T hs hT
  classical
  obtain ⟨x, hx⟩ := GlobalTheory.OTY.LinComb.exists_pow_ne_zero N T (fun P k => s k (A.pick P) P) (by
    intro P hP h0
    apply hT P hP
    intro k
    exact congrFun h0 k)
  refine ⟨fun i y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y, ⟨?_, ?_⟩, fun P hP => hx P hP, ?_⟩
  · intro i
    have : ((fun y => ∑ k : Fin N, x ^ (k : ℕ) * s k i y) ∘ (A.chart i).symm)
        = ∑ k : Fin N, (fun v => x ^ (k : ℕ) * (s k i ∘ (A.chart i).symm) v) := by
      funext v; simp [Finset.sum_apply]
    rw [this]
    exact DifferentiableOn.sum fun k _ => ((hs k).1 i).const_mul _
  · intro i j y hy hi hj
    simp only
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hs k).2 i j y hy hi hj]
    ring
  · refine ⟨1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2, by positivity, fun y => ?_⟩
    simp only [WeightedAtlas.nsq, WeightedAtlas.sqn]
    rw [← Finset.sum_mul, ← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    have h1 : ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ≤ ∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact Finset.sum_congr rfl fun k _ => norm_mul _ _
    have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k : Fin N => ‖x ^ (k : ℕ)‖)
      (fun k => ‖s k (A.pick y) y‖)
    have h3 : 0 ≤ ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by positivity
    calc ‖∑ k : Fin N, x ^ (k : ℕ) * s k (A.pick y) y‖ ^ 2
        ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ * ‖s k (A.pick y) y‖) ^ 2 := by gcongr
      _ ≤ (∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := h2
      _ ≤ (1 + ∑ k : Fin N, ‖x ^ (k : ℕ)‖ ^ 2) * ∑ k : Fin N, ‖s k (A.pick y) y‖ ^ 2 := by
        gcongr; linarith
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linComb_sections_ne_zero_on_finset : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (N : ℕ) (s : Fin N → ι → Y → ℂ) (T : Finset Y), (∀ k, A.IsSec L (s k)) → (∀ P ∈ T, P ∉ A.zeroSet s) → ∃ s' : ι → Y → ℂ, A.IsSec L s' ∧ (∀ P ∈ T, s' (A.pick P) P ≠ 0) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq L s' y ≤ C * A.sqn L s y := by
  atlas_forward_decl GlobalTheory.OTY.exists_linComb_ne_zero_on_finset
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem sections_prod_quot_open : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  intro n Y _ _ _ _ _ ι La _ A
  refine ⟨?_, ?_, ?_⟩
  · intro la mu a b ha hb
    refine ⟨⟨fun i => ?_, fun i j y _ hi hj => ?_⟩, fun y => ?_⟩
    · exact (ha.1 i).mul (hb.1 i)
    · beta_reduce
      rw [A.g_add la mu i j y hi hj, ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj]
      ring
    · simp only [WeightedAtlas.nsq]
      rw [A.ph_add la mu _ y (A.mem_pick y), norm_mul, mul_pow, neg_add, Real.exp_add]
      ring
  · intro la a ha
    have hc : Continuous (A.nsq la a) := bsA_nsq_cont A ha
    have : nz A a = A.nsq la a ⁻¹' {0}ᶜ := by
      ext y
      simp only [nz, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, WeightedAtlas.nsq]
      constructor
      · intro h
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr h)) (Real.exp_pos _).ne'
      · intro h h0
        apply h
        simp [h0]
    rw [this]
    exact isOpen_compl_singleton.preimage hc
  · intro B la a b U ha hb hU
    have hbne : ∀ i y, y ∈ U → y ∈ (A.chart i).source → b i y ≠ 0 := by
      intro i y hy hi
      rw [hb.2 i (A.pick y) y trivial hi (A.mem_pick y)]
      exact mul_ne_zero (A.g_ne B i (A.pick y) y hi (A.mem_pick y)) (hU y hy).2
    refine ⟨⟨fun i => ?_, fun i j y hy hi hj => ?_⟩, fun y hy => div_ne_zero (hU y hy).1 (hU y hy).2⟩
    · have hS : (A.chart i).target ∩ (A.chart i).symm ⁻¹' U ⊆
          (A.chart i).target ∩ (A.chart i).symm ⁻¹' Set.univ := fun v hv => ⟨hv.1, trivial⟩
      have h1 : DifferentiableOn ℂ (a i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (ha.1 i).mono hS
      have h2 : DifferentiableOn ℂ (b i ∘ (A.chart i).symm)
          ((A.chart i).target ∩ (A.chart i).symm ⁻¹' U) := (hb.1 i).mono hS
      have h3 := h1.mul (h2.inv (fun v (hv : v ∈ (A.chart i).target ∩ (A.chart i).symm ⁻¹' U) =>
        hbne i _ hv.2 ((A.chart i).map_target hv.1)))
      refine h3.congr (fun v _ => ?_)
      simp [div_eq_mul_inv]
    · have hgB := A.g_ne B i j y hi hj
      have hbj := hbne j y hy hj
      beta_reduce
      rw [ha.2 i j y trivial hi hj, hb.2 i j y trivial hi hj, A.g_add B la i j y hi hj]
      field_simp

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), (∀ (la mu : La) (a b : ι → Y → ℂ), A.IsSec la a → A.IsSec mu b → A.IsSec (la + mu) (fun i y => a i y * b i y) ∧ ∀ y, A.nsq (la + mu) (fun i y => a i y * b i y) y = A.nsq la a y * A.nsq mu b y) ∧ (∀ (la : La) (a : ι → Y → ℂ), A.IsSec la a → IsOpen (nz A a)) ∧ (∀ (B la : La) (a b : ι → Y → ℂ) (U : Set Y), A.IsSec (B + la) a → A.IsSec B b → (∀ y ∈ U, a (A.pick y) y ≠ 0 ∧ b (A.pick y) y ≠ 0) → A.IsFrameOn la U (fun i y => a i y / b i y)) := by
  atlas_forward_decl GlobalTheory.OTY.sections_prod_quot_open
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.SemiPosLarge

theorem semipos_add_smul : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  intro n Y _ _ _ _ _ _ ι La _ A H G hH
  obtain ⟨C⟩ := GlobalTheory.T.nonempty_atlasBallPartitionCover n Y ι La A
  obtain ⟨k0, hk0⟩ := GlobalTheory.T.curvature_lower_bound_on_cover_balls n Y ι La A C H G hH 0
  refine ⟨k0, fun k hk i y hy ξ => ?_⟩
  have hcurv := hk0 k hk

  have hex : ∃ a, C.chi a y ≠ 0 := by
    by_contra hno
    push_neg at hno
    have := C.sum_one y
    simp [hno] at this
  obtain ⟨a, ha⟩ := hex
  have hts : y ∈ tsupport (C.chi a) := subset_tsupport _ (Function.mem_support.2 ha)
  obtain ⟨hsrc, hball⟩ := C.supp a hts
  have hsm : A.SmoothFn (fun _ : Y => (0 : ℝ)) := fun _ => contDiffOn_const
  have ht := A.levi_transfer (G + k • H) (fun _ => (0 : ℝ)) hsm i (C.idx a) hy hsrc ξ
  simp only [add_zero] at ht ⊢
  rw [ht]
  have h1 := hcurv a (A.chart (C.idx a) y) hball
    (fderiv ℂ ((A.chart (C.idx a)) ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp
  rw [(A.chart (C.idx a)).left_inv hsrc, zero_mul] at h1
  exact h1

end GlobalTheory.SemiPosLarge
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ H G : La, (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∃ k0 : ℕ, ∀ k ≥ k0, A.Pos (G + k • H) (fun _ => 0) := by
  atlas_forward_decl GlobalTheory.SemiPosLarge.semipos_add_smul
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem nz_dense_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ →
    (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) →
    Dense (nz A τ) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ T hs hT hP
  set Zs : Set Y := {y | τ (A.pick y) y = 0} with hZs
  have hc : (nz A τ)ᶜ = Zs := by
    ext y; simp [nz, Zs]

  have toI : ∀ i x, x ∈ (A.chart i).source → τ (A.pick x) x = 0 → τ i x = 0 := by
    intro i x hx h0
    rw [hs.2 i (A.pick x) x (Set.mem_univ _) hx (A.mem_pick x), h0, mul_zero]
  have toP : ∀ i x, x ∈ (A.chart i).source → τ i x = 0 → τ (A.pick x) x = 0 := by
    intro i x hx h0
    rw [hs.2 (A.pick x) i x (Set.mem_univ _) (A.mem_pick x) hx, h0, mul_zero]
  set Z := interior Zs with hZ
  have hZo : IsOpen Z := isOpen_interior
  have hZc : IsClosed Z := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set i := A.pick y
    set e := A.chart i
    have hyv : e y ∈ e.target := e.map_source (A.mem_pick y)
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp e.open_target (e y) hyv
    set W : Set Y := e.source ∩ e ⁻¹' ball (e y) r
    have hWo : IsOpen W := e.isOpen_inter_preimage isOpen_ball
    have hyW : y ∈ W := ⟨A.mem_pick y, mem_ball_self hr⟩
    obtain ⟨x, hxW, hxZ⟩ := (mem_closure_iff.mp hy) W hWo hyW
    set F : V n → ℂ := τ i ∘ e.symm
    have hF : DifferentiableOn ℂ F (ball (e y) r) := by
      have := hs.1 i
      refine this.mono ?_
      intro w hw; exact ⟨hball hw, Set.mem_univ _⟩
    have hxs : e x ∈ ball (e y) r := hxW.2
    have hev : F =ᶠ[𝓝 (e x)] 0 := by
      have hxt : e x ∈ e.target := e.map_source hxW.1
      have h1 : ∀ᶠ w in 𝓝 (e x), e.symm w ∈ Z := by
        have hca : ContinuousAt e.symm (e x) := e.continuousAt_symm hxt
        have : e.symm (e x) = x := e.left_inv hxW.1
        refine hca.preimage_mem_nhds ?_
        rw [this]; exact hZo.mem_nhds hxZ
      have h2 : ∀ᶠ w in 𝓝 (e x), w ∈ e.target := e.open_target.mem_nhds hxt
      filter_upwards [h1, h2] with w hw1 hw2
      have hsrc : e.symm w ∈ e.source := e.map_target hw2
      exact toI i _ hsrc (interior_subset (s := Zs) hw1)
    have hEq := ReciprocityTheory.L2DbarEstimates.C.ident n (ball (e y) r) F (e x) isOpen_ball (convex_ball _ _) hF hxs hev
    have hWZs : W ⊆ Zs := by
      intro z hz
      have h0 : F (e z) = 0 := hEq hz.2
      have : τ i z = 0 := by
        simpa [F, e.left_inv hz.1] using h0
      exact toP i z hz.1 this
    exact interior_maximal hWZs hWo hyW
  have hempty : Z = ∅ := by
    by_contra hne
    obtain ⟨y, hy⟩ := Set.nonempty_iff_ne_empty.mpr hne
    obtain ⟨P, hPT, hPc⟩ := hT y
    have hsub := (IsClopen.connectedComponent_subset ⟨hZc, hZo⟩ hy)
    exact hP P hPT (interior_subset (s := Zs) (hsub hPc))
  have hd := interior_eq_empty_iff_dense_compl.mp hempty
  rw [← hc, compl_compl] at hd
  exact hd

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ) (T : Set Y), A.IsSec Λ τ → (∀ y, ∃ P ∈ T, P ∈ connectedComponent y) → (∀ P ∈ T, τ (A.pick P) P ≠ 0) → Dense (nz A τ) := by
  atlas_forward_decl GlobalTheory.nz_dense_of_ne_zero_on_components
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem exists_preconnected_infinite_nhds {n : ℕ} {Y : Type} [TopologicalSpace Y]
    (hn : 1 ≤ n) (e : OpenPartialHomeomorph Y (V n)) (x : Y) (hx : x ∈ e.source) :
    ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ B.Infinite := by
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.1 e.open_target (e x) (e.map_source hx)
  refine ⟨e.symm '' ball (e x) r, ?_, ?_, ?_⟩
  · have h := e.symm.image_mem_nhds (x := e x) (e.map_source hx) (ball_mem_nhds (e x) hr)
    rwa [e.left_inv hx] at h
  · exact (convex_ball (e x) r).isPreconnected.image _ (e.continuousOn_symm.mono hsub)
  · refine Set.Infinite.image (e.symm.injOn.mono hsub) ?_
    haveI : NeBot (𝓝[≠] (e x)) := Module.punctured_nhds_neBot ℂ (V n) (e x)
    exact infinite_of_mem_nhds (e x) (ball_mem_nhds (e x) hr)

theorem exists_finite_disjoint_meets_components :
    ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn S hS
  have h1 : ∀ x : Y, ∃ B : Set Y, B ∈ 𝓝 x ∧ IsPreconnected B ∧ ∃ P ∈ B, P ∉ S := by
    intro x
    obtain ⟨B, hB, hc, hi⟩ :=
      exists_preconnected_infinite_nhds hn (A.chart (A.pick x)) x (A.mem_pick x)
    obtain ⟨P, hP, hPS⟩ := (hi.diff hS).nonempty
    exact ⟨B, hB, hc, P, hP, hPS⟩
  choose B hB hc P hP hPS using h1
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover B (fun x _ => hB x)
  refine ⟨P '' (t : Set Y), t.finite_toSet.image P, ?_, ?_⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨x, -, rfl⟩
    exact hPS x
  · intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨P x, ⟨x, hx, rfl⟩, (hc x).subset_connectedComponent hy (hP x)⟩

end GlobalTheory.OTY
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_disjoint_meeting_every_component : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → ∀ S : Set Y, S.Finite → ∃ T : Set Y, T.Finite ∧ Disjoint T S ∧ ∀ y, ∃ P ∈ T, P ∈ connectedComponent y := by
  atlas_forward_decl GlobalTheory.OTY.exists_finite_disjoint_meets_components
end

section
section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_etale_frame_of_finite_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (A.zeroSet s).Finite → ∃ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y := by
  intro n Y _ _ _ _ _ _ ι La _ A hn hH E L s hs hS
  obtain ⟨H, hH⟩ := hH
  obtain ⟨T, hTf, hTd, hTm⟩ := GlobalTheory.T.exists_finite_disjoint_meeting_every_component n Y ι La A hn _ hS
  obtain ⟨k1, hk1⟩ := GlobalTheory.T.exists_sections_coords_nonvanishing_at_finset n Y ι La A H hH hTf.toFinset (A.kap + E)
  obtain ⟨k2, hk2⟩ := GlobalTheory.T.exists_pos_add_nsmul_of_levi_pos n Y ι La A H ((2 * n + 4) • A.kap + E + L) hH
  obtain ⟨t0, t, a, ht0, ht, ha, hT⟩ := hk1 (max k1 k2) (le_max_left _ _)
  obtain ⟨J, hJ, hJeq⟩ := GlobalTheory.T.exists_jacobian_section_canonical_weight n Y ι La A (A.kap + (max k1 k2) • H) t0 t ht0 ht
  obtain ⟨s', hs', hs'T, C, hC, hs'C⟩ := GlobalTheory.T.exists_linComb_sections_ne_zero_on_finset n Y ι La A L n s hTf.toFinset hs (by
    intro P hP hPS
    exact Set.disjoint_left.mp hTd (hTf.mem_toFinset.mp hP) hPS)
  obtain ⟨hmul, hopen, hfrac⟩ := GlobalTheory.T.atlasSections_mul_div_nonvanishing_isOpen n Y ι La A
  have ha' : A.IsSec ((A.kap + (max k1 k2) • H) + (A.kap + E)) a := by
    have e : (A.kap + (max k1 k2) • H) + (A.kap + E) = A.kap + ((A.kap + E) + (max k1 k2) • H) := by
      abel
    rw [e]; exact ha
  obtain ⟨h1, h1n⟩ := hmul _ _ _ _ ht0 hJ
  obtain ⟨h2, h2n⟩ := hmul _ _ _ _ h1 ha'
  obtain ⟨h3, h3n⟩ := hmul _ _ _ _ h2 hs'
  have hdec : ∀ y, t0 (A.pick y) y * J (A.pick y) y * a (A.pick y) y * s' (A.pick y) y ≠ 0 →
      t0 (A.pick y) y ≠ 0 ∧ A.IsCoordAt t0 t y ∧ a (A.pick y) y ≠ 0 := by
    intro y hy
    have hJ0 : J (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ht00 : t0 (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    have ha0 : a (A.pick y) y ≠ 0 := fun h => hy (by rw [h]; ring)
    refine ⟨ht00, ?_, ha0⟩
    rw [hJeq (A.pick y) y (A.mem_pick y) ht00] at hJ0
    exact right_ne_zero_of_mul hJ0
  have hopen' := hopen _ _ h3
  obtain ⟨M, hM⟩ := (isCompact_range (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuous_nsq A h2)).bddAbove
  refine ⟨_, fun i y => t0 i y * J i y * a i y * s' i y, A.zmap t0 t, fun i y => a i y / t0 i y,
    h3, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (A.kap + (max k1 k2) • H) + (A.kap + (2 * n) • (A.kap + (max k1 k2) • H)) +
        ((A.kap + (max k1 k2) • H) + (A.kap + E)) + L
        = ((2 * n + 4) • A.kap + E + L) + ((2 * n + 2) * max k1 k2) • H := by
      module
    rw [e]
    apply hk2
    calc k2 ≤ max k1 k2 := le_max_right _ _
      _ ≤ (2 * n + 2) * max k1 k2 := Nat.le_mul_of_pos_left _ (by omega)
  · exact GlobalTheory.T.isEtaleCoordinates_section_quotients n Y ι La A _ t0 t _ ht0 ht hopen' (fun y hy => ⟨(hdec y hy).1, (hdec y hy).2.1⟩)
  · exact hfrac _ _ a t0 _ ha' ht0 (fun y hy => ⟨(hdec y hy).2.2, (hdec y hy).1⟩)
  · refine GlobalTheory.T.dense_nonvanishingSet_of_ne_zero_on_components n Y ι La A _ _ T h3 hTm ?_
    intro P hP
    obtain ⟨ht0P, hcP, haP⟩ := hT P (hTf.mem_toFinset.mpr hP)
    have hsP := hs'T P (hTf.mem_toFinset.mpr hP)
    have hJP : J (A.pick P) P ≠ 0 := by
      rw [hJeq (A.pick P) P (A.mem_pick P) ht0P]
      exact mul_ne_zero (pow_ne_zero _ ht0P) hcP
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero ht0P hJP) haP) hsP
  · refine ⟨max M 1 * C, by positivity, fun y => ?_⟩
    rw [h3n y, mul_assoc]
    exact mul_le_mul ((hM ⟨y, rfl⟩).trans (le_max_left _ _)) (hs'C y)
      (ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.nsq_nonneg A _ _ _) (by positivity)

end GlobalTheory
end

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etale_frame_off_finite_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] [CompactSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), 1 ≤ n → (∃ H : La, ∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < A.leviAt i (A.ph H i) y ξ) → ∀ (E L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → (A.zeroSet s).Finite → ∃ (Λ : La) (τ : ι → Y → ℂ) (z : Y → V n) (β : ι → Y → ℂ), A.IsSec Λ τ ∧ A.Pos Λ (fun _ => 0) ∧ Etale A (nz A τ) z ∧ A.IsFrameOn (A.kap + E) (nz A τ) β ∧ Dense (nz A τ) ∧ ∃ C : ℝ, 0 < C ∧ ∀ y, A.nsq Λ τ y ≤ C * A.sqn L s y := by
  atlas_forward_decl GlobalTheory.exists_etale_frame_of_finite_zeroSet
end

section
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem l2ExtensionLogCanonical' : GlobalTheory.Published.L2ExtensionLogCanonical := by
  intro n hn Y _ _ _ _ _ _ ι La _ A hH E L s hs hS hjac hle δ hδ hcurv f
  obtain ⟨Λ, τ, z, β, hdata⟩ := GlobalTheory.T.exists_etale_frame_off_finite_zeroSet n Y ι La A hn hH E L s hs hS
  exact GlobalTheory.T.l2_extension_etale_coordinates_finite_zeros n Y ι La A hn E L s hs hS hjac hle δ hδ hcurv Λ τ z β hdata f

end GlobalTheory
end
