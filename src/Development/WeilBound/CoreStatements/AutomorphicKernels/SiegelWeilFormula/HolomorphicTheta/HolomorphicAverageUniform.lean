import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.HolomorphicTranslationLevi
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ContinuousQuad
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.ZOfSurjBdd
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionUnipotentInvariant

section
noncomputable section

open MeasureTheory Filter Topology Metric Set

namespace PositivityTheory.SiegelWeilFormula.Holtb

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]

theorem aesm_fderiv (f : X → E → ℂ) (W₀ : E) (r : ℝ) (hr : 0 < r)
    (hd : ∀ x, DifferentiableAt ℂ (f x) W₀)
    (hm : ∀ W ∈ ball W₀ r, AEStronglyMeasurable (f · W) ν) :
    AEStronglyMeasurable (fun x => fderiv ℂ (f x) W₀) ν := by
  classical
  let b := Module.finBasis ℂ E
  let L : Fin (Module.finrank ℂ E) → E →L[ℂ] ℂ := fun i => LinearMap.toContinuousLinearMap (b.coord i)
  have hrep : ∀ x, fderiv ℂ (f x) W₀ = ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := by
    intro x
    ext v
    simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul, Pi.smul_apply,
      smul_eq_mul, L, LinearMap.coe_toContinuousLinearMap', Module.Basis.coord_apply]
    conv_lhs => rw [← b.sum_repr v]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, smul_eq_mul, mul_comm]
  have hfun : (fun x => fderiv ℂ (f x) W₀) = fun x => ∑ i, fderiv ℂ (f x) W₀ (b i) • L i := funext hrep
  rw [hfun]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ (L i)
  set v := b i
  set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def
  have hε : 0 < ε := by positivity
  set t : ℕ → ℂ := fun k => ((ε * (1 / ((k : ℝ) + 1)) : ℝ) : ℂ) with ht_def
  have ht0 : Tendsto t atTop (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun k => ?_⟩
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul ε)
      rw [mul_zero] at h
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h
      simpa [ht_def, Function.comp_def] using h2
    · simp only [ht_def, Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
      positivity
  have htn : ∀ k, ‖t k‖ ≤ ε := by
    intro k
    simp only [ht_def, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
    have : 1 / ((k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    nlinarith
  have htmem : ∀ k, W₀ + t k • v ∈ ball W₀ r := by
    intro k
    rw [mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul]
    have h1 : ε * (‖v‖ + 1) = r / 2 := by rw [hε_def]; field_simp
    have h2 : ‖t k‖ * ‖v‖ ≤ ε * (‖v‖ + 1) := by
      calc ‖t k‖ * ‖v‖ ≤ ε * ‖v‖ := by gcongr; exact htn k
        _ ≤ ε * (‖v‖ + 1) := by nlinarith
    linarith
  refine aestronglyMeasurable_of_tendsto_ae (u := atTop)
    (f := fun k x => (t k)⁻¹ • (f x (W₀ + t k • v) - f x W₀)) (fun k => ?_) (ae_of_all _ fun x => ?_)
  · exact (((hm _ (htmem k)).sub (hm _ (mem_ball_self hr))).const_smul ((t k)⁻¹)).congr (ae_of_all _ fun x => rfl)
  · have hl : HasDerivAt (fun s : ℂ => W₀ + s • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add W₀
    have h1 : HasDerivAt (fun s : ℂ => f x (W₀ + s • v)) (fderiv ℂ (f x) W₀ v) 0 :=
      (hd x).hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hl (by simp)
    have h2 := h1.tendsto_slope_zero.comp ht0
    simpa [Function.comp_def] using h2

theorem differentiableOn_integral_of_bdd [IsFiniteMeasure ν] {U : Set E} (hU : IsOpen U) (f : X → E → ℂ)
    (hd : ∀ x, DifferentiableOn ℂ (f x) U) (hm : ∀ W ∈ U, AEStronglyMeasurable (f · W) ν)
    (hb : ∀ W₀ ∈ U, ∃ r > 0, ∃ M, ball W₀ r ⊆ U ∧ ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M) :
    DifferentiableOn ℂ (fun W => ∫ x, f x W ∂ν) U := by
  intro W₀ hW₀
  obtain ⟨r, hr, M, hsub, hM⟩ := hb W₀ hW₀
  set M' := max M 0
  have hM' : ∀ x, ∀ W ∈ ball W₀ r, ‖f x W‖ ≤ M' := fun x W hW => (hM x W hW).trans (le_max_left _ _)
  have hdiffAt : ∀ x, ∀ W ∈ ball W₀ r, DifferentiableAt ℂ (f x) W := fun x W hW =>
    (hd x).differentiableAt (hU.mem_nhds (hsub hW))
  have hball : ∀ W ∈ ball W₀ (r / 2), ball W (r / 2) ⊆ ball W₀ r := by
    intro W hW
    apply ball_subset_ball'
    rw [mem_ball] at hW
    linarith
  have hbnd : ∀ x, ∀ W ∈ ball W₀ (r / 2), ‖fderiv ℂ (f x) W‖ ≤ (2 * M') / (r / 2) := by
    intro x W hW
    apply Complex.norm_fderiv_le_div_of_mapsTo_ball
    · exact (hd x).mono ((hball W hW).trans hsub)
    · intro Z hZ
      rw [mem_closedBall, dist_eq_norm]
      have hZ' : Z ∈ ball W₀ r := hball W hW hZ
      have hW' : W ∈ ball W₀ r := ball_subset_ball (by linarith) hW
      calc ‖f x Z - f x W‖ ≤ ‖f x Z‖ + ‖f x W‖ := norm_sub_le _ _
        _ ≤ M' + M' := add_le_add (hM' x Z hZ') (hM' x W hW')
        _ = 2 * M' := by ring
    · positivity
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := ν) (F := fun W x => f x W)
    (F' := fun W x => fderiv ℂ (f x) W) (bound := fun _ => (2 * M') / (r / 2)) (s := ball W₀ (r / 2)) (x₀ := W₀)
    (ball_mem_nhds W₀ (by positivity))
    (eventually_of_mem (hU.mem_nhds hW₀) fun W hW => hm W hW)
    ((integrable_const M').mono' (hm W₀ hW₀) (ae_of_all _ fun x => hM' x W₀ (mem_ball_self hr)))
    (aesm_fderiv f W₀ r hr (fun x => hdiffAt x W₀ (mem_ball_self hr)) (fun W hW => hm W (hsub hW)))
    (ae_of_all _ fun x W hW => hbnd x W hW)
    (integrable_const _)
    (ae_of_all _ fun x W hW => (hdiffAt x W (ball_subset_ball (by linarith) hW)).hasFDerivAt)
  exact key.differentiableAt.differentiableWithinAt

end PositivityTheory.SiegelWeilFormula.Holtb
end
end

section
noncomputable section

open Matrix Metric Set Filter Topology
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

variable {n : ℕ}

def bmap (q : ℕ) (y : GR n) : Matrix (Fin n) (Fin n) ℂ := if q = 0 then zOf y else -(zOf y)ᴴ

def negConj (W : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ := fun i j => -star (W j i)

theorem negConj_eq (W : Fin n → Fin n → ℂ) : negConj W = (-(Matrix.of W)ᴴ : Matrix (Fin n) (Fin n) ℂ) := by
  ext i j; simp [negConj]

theorem negConj_negConj (W : Fin n → Fin n → ℂ) : negConj (negConj W) = W := by
  ext i j; simp [negConj]

theorem negConj_mem {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : negConj W ∈ Dom n := by
  rw [negConj_eq]; exact neg_conj_mem' hW

theorem norm_negConj_sub (W W' : Fin n → Fin n → ℂ) : ‖negConj W - negConj W'‖ ≤ ‖W - W'‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j => ?_
  have h : (negConj W - negConj W') i j = -star ((W - W') j i) := by
    show -star (W j i) - -star (W' j i) = -star (W j i - W' j i)
    rw [star_sub]; ring
  rw [h, norm_neg, norm_star]
  exact (norm_le_pi_norm ((W - W') j) i).trans (norm_le_pi_norm (W - W') j)

theorem bmap_local (q : ℕ) (W₀ : Fin n → Fin n → ℂ) (hW₀ : W₀ ∈ Dom n) : ∃ r > 0, closedBall W₀ r ⊆ Dom n ∧
    ∃ S : Set (GR n), IsCompact S ∧ ∀ W ∈ closedBall W₀ r, ∃ y ∈ S, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' W₀ hW₀
    refine ⟨r, hr, hsub, S, hS, fun W hW => ?_⟩
    obtain ⟨y, hy, hyW⟩ := hcov W hW
    refine ⟨y, hy, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hyW
  · obtain ⟨r, hr, hsub, S, hS, hcov⟩ := zOf_surj_bdd' (negConj W₀) (negConj_mem hW₀)
    have key : ∀ W ∈ closedBall W₀ r, negConj W ∈ closedBall (negConj W₀) r := by
      intro W hW
      rw [mem_closedBall, dist_eq_norm] at hW ⊢
      exact (norm_negConj_sub W W₀).trans hW
    refine ⟨r, hr, fun W hW => ?_, S, hS, fun W hW => ?_⟩
    · have h := negConj_mem (hsub (key W hW))
      rwa [negConj_negConj] at h
    · obtain ⟨y, hy, hyW⟩ := hcov (negConj W) (key W hW)
      refine ⟨y, hy, ?_⟩
      unfold bmap
      rw [if_neg hq, hyW]
      funext i j
      show -star (negConj W j i) = W i j
      simp [negConj]

theorem bmap_surj (q : ℕ) {W : Fin n → Fin n → ℂ} (hW : W ∈ Dom n) : ∃ y : GR n, (bmap q y : Fin n → Fin n → ℂ) = W := by
  by_cases hq : q = 0
  · obtain ⟨y, hy⟩ := zOf_surj' hW
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_pos hq]
    exact hy
  · obtain ⟨y, hy⟩ := zOf_surj' (negConj_mem hW)
    refine ⟨y, ?_⟩
    unfold bmap
    rw [if_neg hq, hy]
    funext i j
    show -star (negConj W j i) = W i j
    simp [negConj]

theorem continuous_mR : Continuous (mR : GR n → M2 n) :=
  Units.continuous_val.comp continuous_subtype_val

theorem continuous_toBlocks₂₁ : Continuous fun M : M2 n => M.toBlocks₂₁ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inl j)).comp (continuous_apply (Sum.inr i))

theorem continuous_toBlocks₂₂ : Continuous fun M : M2 n => M.toBlocks₂₂ :=
  continuous_pi fun i => continuous_pi fun j => (continuous_apply (Sum.inr j)).comp (continuous_apply (Sum.inr i))

theorem zpow_cond {a : ℂ} {k : ℤ} (h : a ^ k ≠ 0) : a ≠ 0 ∨ 0 ≤ k := by
  by_contra hc
  push_neg at hc
  obtain ⟨rfl, hk⟩ := hc
  exact h (zero_zpow k (ne_of_lt hk))

theorem continuous_weight_factor (p q : ℕ) (e : ℤ) : Continuous (F0 p q e : GR n → ℂ) := by
  have hd : Continuous fun y : GR n => (mR y).det := continuous_mR.matrix_det
  have hb1 : Continuous fun y : GR n => toBlocks₂₁ (mR y) := continuous_toBlocks₂₁.comp continuous_mR
  have hb2 : Continuous fun y : GR n => toBlocks₂₂ (mR y) := continuous_toBlocks₂₂.comp continuous_mR
  have h1 : Continuous fun y : GR n => (u1 (mR y)).det := by
    unfold u1
    exact (((continuous_const (y := Complex.I)).smul hb1).add hb2).matrix_det
  have h2 : Continuous fun y : GR n => (u2 (mR y)).det := by
    unfold u2
    exact ((((continuous_const (y := Complex.I)).smul hb1).neg).add hb2).matrix_det
  have hne := spherical_section_ne_zero_group (n := n) p q e
  simp only [F0, f0] at hne ⊢
  exact (hd.zpow₀ e fun y => zpow_cond (left_ne_zero_of_mul (hne y))).mul
    ((h1.zpow₀ _ fun y => zpow_cond (left_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))).mul
      (h2.zpow₀ _ fun y => zpow_cond (right_ne_zero_of_mul (right_ne_zero_of_mul (hne y)))))

end PositivityTheory.SiegelWeilFormula.Holtb
end
end

section
noncomputable section

open Matrix Metric Set Filter Topology MeasureTheory
open scoped ComplexOrder

namespace PositivityTheory.SiegelWeilFormula.Holtb

open PositivityTheory.Rg.Sw PositivityTheory.SiegelWeilFormula PositivityTheory.Rg.Sw.HSt.HolTPf

theorem holomorphic_average_uniform : ∀ (n p q : ℕ) (e : ℤ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (ι : GR n →* G),
    Continuous ι →
    ∀ A : G → ℂ, Continuous A → (∀ g, IsHolW p q e fun y => A (g * ι y)) →
    ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [IsFiniteMeasure ν] (c : X → G) (u : X → ℂ) (C : Set G), IsCompact C →
      (∀ x, c x ∈ C) → (∀ x, ‖u x‖ ≤ 1) → (∀ y, AEStronglyMeasurable (fun x => A (c x * ι y) * u x) ν) →
      IsHolW p q e fun y => ∫ x, A (c x * ι y) * u x ∂ν := by
  intro n p q e G _ _ _ ι hι A hA hhol X _ ν _ c u C hC hcC hu hmeas
  choose H hHd hHe using hhol
  have hHe' : ∀ g y, A (g * ι y) = F0 p q e y * H g (bmap q y) := hHe
  have hval : ∀ g y, H g (bmap q y) = A (g * ι y) / F0 p q e y := by
    intro g y
    rw [hHe' g y]
    exact (mul_div_cancel_left₀ _ (spherical_section_ne_zero_group p q e y)).symm
  set f : X → (Fin n → Fin n → ℂ) → ℂ := fun x W => H (c x) W * u x with hf
  refine ⟨fun W => ∫ x, f x W ∂ν, ?_, ?_⟩
  · refine differentiableOn_integral_of_bdd (U := Dom n) isOpen_dom' f (fun x => (hHd (c x)).mul_const _) ?_ ?_
    · intro W hW
      obtain ⟨y, hy⟩ := bmap_surj q hW
      have h : (fun x => f x W) = fun x => (A (c x * ι y) * u x) * (F0 p q e y)⁻¹ := by
        funext x
        simp only [hf]
        rw [← hy, hval, div_eq_mul_inv]
        ring
      rw [h]
      exact (hmeas y).mul_const _
    · intro W₀ hW₀
      obtain ⟨r, hr, hsub, S, hS, hSW⟩ := bmap_local q W₀ hW₀
      obtain ⟨K, hK⟩ := (hC.prod hS).exists_bound_of_continuousOn
        ((hA.comp (continuous_fst.mul (hι.comp continuous_snd))).continuousOn)
      obtain ⟨y₀, hy₀S, -⟩ := hSW W₀ (mem_closedBall_self hr.le)
      obtain ⟨ym, hymS, hymin⟩ := hS.exists_isMinOn ⟨y₀, hy₀S⟩ (continuous_weight_factor p q e).norm.continuousOn
      have hm : 0 < ‖F0 p q e ym‖ := norm_pos_iff.2 (spherical_section_ne_zero_group p q e ym)
      refine ⟨r, hr, K / ‖F0 p q e ym‖, ball_subset_closedBall.trans hsub, fun x W hW => ?_⟩
      obtain ⟨y, hyS, hy⟩ := hSW W (ball_subset_closedBall hW)
      have hAy : ‖A (c x * ι y)‖ ≤ K := hK (c x, y) ⟨hcC x, hyS⟩
      have hmy : ‖F0 p q e ym‖ ≤ ‖F0 p q e y‖ := hymin hyS
      have hK0 : 0 ≤ K := (norm_nonneg _).trans hAy
      have hfx : ‖f x W‖ = ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ := by
        simp only [hf]
        rw [← hy, hval, norm_mul, norm_div]
      rw [hfx]
      calc ‖A (c x * ι y)‖ / ‖F0 p q e y‖ * ‖u x‖ ≤ K / ‖F0 p q e ym‖ * 1 := by
            apply mul_le_mul _ (hu x) (norm_nonneg _) (by positivity)
            exact div_le_div₀ hK0 hAy hm hmy
        _ = K / ‖F0 p q e ym‖ := mul_one _
  · intro y
    show _ = F0 p q e y * ∫ x, f x (bmap q y) ∂ν
    rw [← integral_const_mul]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [hf]
    rw [hHe' (c x) y]
    ring

theorem holT : HolT := ⟨holomorphic_translation_levi, holomorphic_average_uniform⟩

end PositivityTheory.SiegelWeilFormula.Holtb
end
end
