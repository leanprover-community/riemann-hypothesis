import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFsPotLaplacian
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsInvDerivDecay
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsLaplacianDecayZero

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real

theorem LaplacianLogGrowth.proof (hA : FsPotLaplacian.Statement) (hD : InvDerivDecay.Statement)
    (hZ : LaplacianDecayZero.Statement) : LaplacianLogGrowth.Statement := by
  intro u F a r hu hr hF heq
  obtain ⟨-, hAi, hA0⟩ := hA
  obtain ⟨v, hv_def⟩ : ∃ v : ℂ → ℝ, v = u - a • fsPotPlane := ⟨_, rfl⟩
  have hφ : ContDiff ℝ 2 (a • fsPotPlane) := contDiff_fsPotPlane.const_smul a
  have hv : ContDiff ℝ 2 v := hv_def ▸ hu.sub hφ
  have hρ : 0 < min r 1 := lt_min hr one_pos
  have hG : ContDiffOn ℝ 2 (F - a • fsPotPlane) (Metric.ball 0 (min r 1)) :=
    (hF.mono (Metric.ball_subset_ball (min_le_left _ _))).sub hφ.contDiffOn
  have hveq : ∀ y : ℂ, max r⁻¹ 1 < ‖y‖ → v y = (F - a • fsPotPlane) y⁻¹ := by
    intro y hy
    have h1 := heq y (lt_of_le_of_lt (le_max_left _ _) hy)
    have h2 := fsPotPlane_eq (y := y) (by rw [inv_one]; exact lt_of_le_of_lt (le_max_right _ _) hy)
    simp only [hv_def, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    ring
  obtain ⟨C, R₀, hC⟩ := hD v (F - a • fsPotPlane) (min r 1) (max r⁻¹ 1) hρ hG hveq
  obtain ⟨hvi, hv0⟩ := hZ v C R₀ hv hC
  have hu' : u = a • fsPotPlane + v := by rw [hv_def]; abel
  have hΔ : Δ u = fun y => a * Δ fsPotPlane y + Δ v y := by
    funext y
    rw [hu', ContDiffAt.laplacian_add hφ.contDiffAt hv.contDiffAt,
      laplacian_smul a contDiff_fsPotPlane.contDiffAt, smul_eq_mul]
  rw [hΔ]
  refine ⟨(hAi.const_mul a).add hvi, ?_⟩
  rw [MeasureTheory.integral_add (hAi.const_mul a) hvi, MeasureTheory.integral_const_mul, hA0, hv0]
  ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian Real MeasureTheory Filter Topology Set

theorem hasFDerivAt_fsPotPlane (z : ℂ) :
    HasFDerivAt fsPotPlane ((1 + ‖z‖ ^ 2)⁻¹ • innerSL ℝ z) z := by
  have hl : HasFDerivAt (fun y : ℂ => Real.log (1 + ‖y‖ ^ 2))
      ((1 + ‖z‖ ^ 2)⁻¹ • (2 • innerSL ℝ z)) z :=
    ((hasStrictFDerivAt_norm_sq z).hasFDerivAt.const_add 1).log (by positivity)
  have e : fsPotPlane = fun y : ℂ => Real.log (1 + ‖y‖ ^ 2) * (1 / 2) := by
    funext y; simp only [fsPotPlane]; ring
  rw [e]
  refine (hl.mul_const (1 / 2 : ℝ)).congr_fderiv ?_
  ext w
  simp
  ring

theorem fderiv_fsPotPlane_apply (z e : ℂ) :
    fderiv ℝ fsPotPlane z e = (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) := by
  rw [(hasFDerivAt_fsPotPlane z).fderiv]
  simp [Complex.inner] <;> ring_nf <;> simp

theorem fderiv_fderiv_fsPotPlane_apply (y e : ℂ) :
    fderiv ℝ (fderiv ℝ fsPotPlane) y e e =
      fderiv ℝ (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im)) y e := by
  have hd : DifferentiableAt ℝ (fderiv ℝ fsPotPlane) y :=
    ((contDiff_fsPotPlane.fderiv_right (m := 1) (by norm_num)).differentiable
      (by norm_num)) y
  have h := fderiv_clm_apply hd (differentiableAt_const e)
  have hfun : (fun z : ℂ => fderiv ℝ fsPotPlane z e) =
      fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im) :=
    funext fun z => fderiv_fsPotPlane_apply z e
  rw [hfun] at h
  rw [h]
  simp

theorem hasFDerivAt_partial (y e : ℂ) :
    HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹ * (z.re * e.re + z.im * e.im))
      ((1 + ‖y‖ ^ 2)⁻¹ • (e.re • Complex.reCLM + e.im • Complex.imCLM) +
        (y.re * e.re + y.im * e.im) •
          (-(((1 + ‖y‖ ^ 2) ^ 2)⁻¹) • (2 • innerSL ℝ y))) y := by
  have h1 : HasFDerivAt (fun z : ℂ => 1 + ‖z‖ ^ 2) (2 • innerSL ℝ y) y :=
    (hasStrictFDerivAt_norm_sq y).hasFDerivAt.const_add 1
  have h2 : HasFDerivAt (fun z : ℂ => (1 + ‖z‖ ^ 2)⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) (-((1 + ‖y‖ ^ 2) ^ 2)⁻¹)).comp
        (2 • innerSL ℝ y)) y :=
    (hasFDerivAt_inv (by positivity : (1 + ‖y‖ ^ 2) ≠ 0)).comp y h1
  have h3 : HasFDerivAt (fun z : ℂ => z.re * e.re + z.im * e.im)
      (e.re • Complex.reCLM + e.im • Complex.imCLM) y := by
    have hf : (fun z : ℂ => z.re * e.re + z.im * e.im) =
        fun z => (e.re • Complex.reCLM + e.im • Complex.imCLM) z := by
      funext z; simp; ring
    rw [hf]
    exact ContinuousLinearMap.hasFDerivAt _
  refine (h2.mul h3).congr_fderiv ?_
  ext w
  simp <;> ring_nf <;> simp

theorem laplacian_fsPotPlane (y : ℂ) : Δ fsPotPlane y = 2 / (1 + ‖y‖ ^ 2) ^ 2 := by
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_fsPotPlane_apply, fderiv_fderiv_fsPotPlane_apply,
    (hasFDerivAt_partial y 1).fderiv, (hasFDerivAt_partial y Complex.I).fderiv]
  have hn : ‖y‖ ^ 2 = y.re ^ 2 + y.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  have hp : (0 : ℝ) < 1 + ‖y‖ ^ 2 := by positivity
  simp [Complex.inner]
  rw [hn] at hp ⊢
  field_simp
  ring

theorem integrable_laplacian_fsPotPlane : Integrable (Δ fsPotPlane) := by
  have h : Δ fsPotPlane = fun y : ℂ => 2 * ((1 : ℝ) + ‖y‖ ^ 2) ^ (-(4 : ℝ) / 2) := by
    funext y
    rw [laplacian_fsPotPlane, show -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) by norm_num,
      rpow_neg (by positivity), rpow_natCast, div_eq_mul_inv]
  rw [h]
  exact (integrable_rpow_neg_one_add_norm_sq (by simp [Complex.finrank_real_complex]; norm_num)).const_mul 2

theorem integral_radial_fsPot :
    ∫ s in Ioi (0 : ℝ), s ^ (2 - 1) • (2 / (1 + s ^ 2) ^ 2) = 1 := by
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt (fun s : ℝ => -(1 + s ^ 2)⁻¹)
      (x ^ (2 - 1) • (2 / (1 + x ^ 2) ^ 2)) x := by
    intro x _
    have hx : (1 + x ^ 2) ≠ 0 := by positivity
    have h := (((hasDerivAt_pow 2 x).const_add 1).inv hx).neg
    refine h.congr_deriv ?_
    rw [smul_eq_mul, neg_div, neg_neg]
    push_cast
    ring
  have htend : Tendsto (fun s : ℝ => -(1 + s ^ 2)⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun s : ℝ => 1 + s ^ 2) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
    simpa using h.inv_tendsto_atTop.neg
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv (fun x hx => by
    have : (0 : ℝ) < x := hx
    positivity) htend
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv hint htend]
  norm_num

theorem integral_laplacian_fsPotPlane : ∫ y, Δ fsPotPlane y = 2 * π := by
  have h : (fun y : ℂ => Δ fsPotPlane y) = fun y : ℂ => (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2) ‖y‖ :=
    funext laplacian_fsPotPlane
  rw [h, integral_fun_norm_addHaar volume (fun s : ℝ => 2 / (1 + s ^ 2) ^ 2),
    Complex.finrank_real_complex, integral_radial_fsPot]
  simp [Measure.real, Complex.volume_ball]

theorem FsPotLaplacian.proof : FsPotLaplacian.Statement :=
  ⟨laplacian_fsPotPlane, integrable_laplacian_fsPotPlane, integral_laplacian_fsPotPlane⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

open Nat Set Filter Topology

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem norm_iteratedFDeriv_real_inv (k : ℕ) {z : ℂ} (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ k (Inv.inv : ℂ → ℂ) z‖ = k ! * (‖z‖ ^ (k + 1))⁻¹ := by
  rw [← (contDiffAt_inv ℂ hz (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    Function.comp_apply, ContinuousMultilinearMap.norm_restrictScalars,
    norm_iteratedFDeriv_eq_norm_iteratedDeriv, iteratedDeriv_eq_iterate, iter_deriv_inv]
  rw [show (-1 - (k : ℤ)) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
  simp

theorem InvDerivDecay.proof : InvDerivDecay.Statement := by
  intro v G ρ R hρ hG hv
  set t : Set ℂ := Metric.ball 0 ρ with ht_def
  have ht : IsOpen t := Metric.isOpen_ball
  have hK : Metric.closedBall (0 : ℂ) (ρ / 2) ⊆ t :=
    Metric.closedBall_subset_ball (by linarith)
  have hbd : ∀ i : ℕ, i ≤ 2 → ∃ M : ℝ, ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi
    exact (isCompact_closedBall (0 : ℂ) (ρ / 2)).exists_bound_of_continuousOn
      ((hG.continuousOn_iteratedFDerivWithin (by exact_mod_cast hi) ht.uniqueDiffOn).mono hK)
  obtain ⟨M₀, hM₀⟩ := hbd 0 (by norm_num)
  obtain ⟨M₁, hM₁⟩ := hbd 1 (by norm_num)
  obtain ⟨M₂, hM₂⟩ := hbd 2 le_rfl
  set M : ℝ := max 0 (max M₀ (max M₁ M₂)) with hM_def
  have hM0 : 0 ≤ M := le_max_left _ _
  have hMi : ∀ i : ℕ, i ≤ 2 → ∀ z ∈ Metric.closedBall (0 : ℂ) (ρ / 2),
      ‖iteratedFDerivWithin ℝ i G t z‖ ≤ M := by
    intro i hi z hz
    interval_cases i
    · exact (hM₀ z hz).trans (by simp [hM_def])
    · exact (hM₁ z hz).trans (by simp [hM_def])
    · exact (hM₂ z hz).trans (by simp [hM_def])
  set R₀ : ℝ := max R (max 1 (2 / ρ)) with hR₀_def
  refine ⟨4 * M, R₀, fun y hy => ?_⟩
  have hRR₀ : R ≤ R₀ := le_max_left _ _
  have h1R₀ : 1 ≤ R₀ := (le_max_left _ _).trans (le_max_right _ _)
  have h2R₀ : 2 / ρ ≤ R₀ := (le_max_right _ _).trans (le_max_right _ _)
  set s : Set ℂ := {z | R₀ < ‖z‖} with hs_def
  have hs : IsOpen s := isOpen_lt continuous_const continuous_norm
  have hys : y ∈ s := hy
  have hy1 : 1 < ‖y‖ := lt_of_le_of_lt h1R₀ hy
  have hypos : 0 < ‖y‖ := by linarith
  have hy0 : y ≠ 0 := norm_pos_iff.mp hypos
  have hinvK : ∀ z ∈ s, z⁻¹ ∈ Metric.closedBall (0 : ℂ) (ρ / 2) := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    rw [mem_closedBall_zero_iff, norm_inv,
      inv_le_comm₀ hzpos (by positivity), inv_div]
    linarith
  have hmaps : MapsTo (Inv.inv : ℂ → ℂ) s t := fun z hz => hK (hinvK z hz)
  have hinvC : ContDiffOn ℝ 2 (Inv.inv : ℂ → ℂ) s := by
    intro z hz
    have hz' : R₀ < ‖z‖ := hz
    have hzpos : 0 < ‖z‖ := by linarith
    exact (contDiffAt_inv ℝ (norm_pos_iff.mp hzpos)).contDiffWithinAt
  have hev : v =ᶠ[𝓝 y] G ∘ Inv.inv := by
    filter_upwards [hs.mem_nhds hys] with z hz
    exact hv z (lt_of_le_of_lt hRR₀ hz)
  have hinvD : ∀ k : ℕ, ‖iteratedFDerivWithin ℝ k (Inv.inv : ℂ → ℂ) s y‖ =
      k ! * (‖y‖ ^ (k + 1))⁻¹ := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys, norm_iteratedFDeriv_real_inv k hy0]
  have hcomp : ∀ k : ℕ, iteratedFDeriv ℝ k v y = iteratedFDerivWithin ℝ k (G ∘ Inv.inv) s y := by
    intro k
    rw [iteratedFDerivWithin_of_isOpen k hs hys]
    exact (hev.iteratedFDeriv ℝ k).eq_of_nhds
  have hC : ∀ i, i ≤ 2 → ‖iteratedFDerivWithin ℝ i G t (y⁻¹)‖ ≤ M :=
    fun i hi => hMi i hi _ (hinvK y hys)
  constructor
  · have hD1 : ∀ i, 1 ≤ i → i ≤ 1 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ ((‖y‖ ^ 2)⁻¹) ^ i := by
      intro i h1 h2
      obtain rfl : i = 1 := le_antisymm h2 h1
      rw [hinvD]
      simp
    have key := norm_iteratedFDerivWithin_comp_le (n := 1) hG hinvC (by norm_num)
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys (fun i hi => hC i (by omega)) hD1
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ), hcomp 1]
    refine key.trans ?_
    have hp : 0 < (‖y‖ ^ 2)⁻¹ := by positivity
    rw [div_eq_mul_inv]
    simp only [factorial_one, cast_one, one_mul, pow_one]
    exact mul_le_mul_of_nonneg_right (by linarith) hp.le
  · set D : ℝ := Real.sqrt (2 / ‖y‖ ^ 3) with hD_def
    have hDsq : D ^ 2 = 2 / ‖y‖ ^ 3 := Real.sq_sqrt (by positivity)
    have hD2 : ∀ i, 1 ≤ i → i ≤ 2 →
        ‖iteratedFDerivWithin ℝ i (Inv.inv : ℂ → ℂ) s y‖ ≤ D ^ i := by
      intro i h1 h2
      rw [hinvD]
      interval_cases i
      · rw [pow_one, hD_def, Real.le_sqrt (by positivity) (by positivity)]
        simp only [factorial_one, cast_one, one_mul]
        rw [inv_pow, ← pow_mul, inv_le_iff_one_le_mul₀ (by positivity)]
        rw [show (1 + 1) * 2 = 4 by norm_num, show ‖y‖ ^ 4 = ‖y‖ * ‖y‖ ^ 3 by ring,
          div_mul_eq_mul_div, ← mul_assoc, mul_div_assoc, div_self (by positivity)]
        nlinarith
      · rw [hDsq]
        simp [div_eq_mul_inv]
    have key := norm_iteratedFDerivWithin_comp_le (n := 2) hG hinvC le_rfl
      ht.uniqueDiffOn hs.uniqueDiffOn hmaps hys hC hD2
    rw [hcomp 2]
    refine key.trans (le_of_eq ?_)
    rw [hDsq]
    simp only [factorial_two, cast_ofNat]
    ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open InnerProductSpace Laplacian MeasureTheory Filter Topology

theorem LaplacianDecayZero.integral_line_eq_zero (v : ℂ → ℝ)
    (hdiff : Differentiable ℝ (fderiv ℝ v))
    (hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0)) (w e : ℂ) (he : ‖e‖ = 1) :
    ∫ t : ℝ, fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e = 0 := by
  have hγd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => w + (s : ℂ) * e) e t := by
    intro t
    have := (((hasDerivAt_id t).ofReal_comp).mul_const e).const_add w
    simpa using this
  have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e)
      (fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e) t := by
    intro t
    have h1 := ((hdiff (w + (t : ℂ) * e)).hasFDerivAt).comp_hasDerivAt t (hγd t)
    have h2 := (ContinuousLinearMap.apply ℝ ℝ e).hasFDerivAt.comp_hasDerivAt t h1
    exact h2
  have hiso : Isometry (fun s : ℝ => w + (s : ℂ) * e) := by
    refine Isometry.of_dist_eq fun s t => ?_
    rw [dist_eq_norm, dist_eq_norm,
      show w + (s : ℂ) * e - (w + (t : ℂ) * e) = ((s - t : ℝ) : ℂ) * e by push_cast; ring,
      norm_mul, he, mul_one, Complex.norm_real]
  have hcoc : Tendsto (fun s : ℝ => w + (s : ℂ) * e) (cocompact ℝ) (cocompact ℂ) :=
    hiso.isClosedEmbedding.tendsto_cocompact
  have hlim' : Tendsto (fun s : ℝ => fderiv ℝ v (w + (s : ℂ) * e) e) (cocompact ℝ) (𝓝 0) := by
    have := ((ContinuousLinearMap.apply ℝ ℝ e).continuous.tendsto 0).comp (hlim.comp hcoc)
    exact this
  by_cases hint : Integrable (fun t : ℝ => fderiv ℝ (fderiv ℝ v) (w + (t : ℂ) * e) e e)
  · have := integral_of_hasDerivAt_of_tendsto hF hint (hlim'.mono_left atBot_le_cocompact)
      (hlim'.mono_left atTop_le_cocompact)
    simpa using this
  · exact integral_undef hint

theorem LaplacianDecayZero.proof : LaplacianDecayZero.Statement := by
  intro v C R₀ hv hdec
  have hD2c : Continuous (iteratedFDeriv ℝ 2 v) := hv.continuous_iteratedFDeriv le_rfl
  have hdiff : Differentiable ℝ (fderiv ℝ v) :=
    (hv.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hlim : Tendsto (fderiv ℝ v) (cocompact ℂ) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hn : Tendsto (fun y : ℂ => ‖y‖) (cocompact ℂ) atTop := tendsto_norm_cocompact_atTop
    have hc : Tendsto (fun y : ℂ => C / ‖y‖ ^ 2) (cocompact ℂ) (𝓝 0) :=
      tendsto_const_nhds.div_atTop ((tendsto_pow_atTop two_ne_zero).comp hn)
    refine squeeze_zero' (Eventually.of_forall fun y => norm_nonneg _) ?_ hc
    filter_upwards [hn.eventually_gt_atTop R₀] with y hy
    exact (hdec y hy).1

  obtain ⟨M, hM⟩ : ∃ M, ∀ y ∈ Metric.closedBall (0 : ℂ) (max R₀ 1),
      ‖iteratedFDeriv ℝ 2 v y‖ ≤ M :=
    (isCompact_closedBall 0 (max R₀ 1)).exists_bound_of_continuousOn hD2c.continuousOn
  have hR1 : (1 : ℝ) ≤ max R₀ 1 := le_max_right _ _
  have hMR : 0 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
    mul_nonneg (abs_nonneg _) (pow_nonneg (by linarith) _)
  have hbound : ∀ y : ℂ, ‖iteratedFDeriv ℝ 2 v y‖ ≤
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ)) := by
    intro y
    have hpos : 0 < 1 + ‖y‖ := by positivity
    rw [Real.rpow_neg hpos.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
    by_cases hy : ‖y‖ ≤ max R₀ 1
    · have h1 := hM y (by simpa using hy)
      have h2 : (1 + ‖y‖) ^ 3 ≤ (1 + max R₀ 1) ^ 3 := by gcongr
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3 ≤ |M| * (1 + max R₀ 1) ^ 3 :=
            mul_le_mul (h1.trans (le_abs_self M)) h2 (by positivity) (abs_nonneg M)
        _ ≤ _ := by linarith [abs_nonneg C]
    · push Not at hy
      have hR0 : R₀ < ‖y‖ := lt_of_le_of_lt (le_max_left _ _) hy
      have hy1 : 1 < ‖y‖ := lt_of_le_of_lt hR1 hy
      have h1 := (hdec y hR0).2
      have h3 : ‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3 ≤ |C| := by
        rw [le_div_iff₀ (by positivity)] at h1
        exact h1.trans (le_abs_self C)
      have h4 : (1 + ‖y‖) ^ 3 ≤ 8 * ‖y‖ ^ 3 := by
        calc (1 + ‖y‖) ^ 3 ≤ (2 * ‖y‖) ^ 3 := pow_le_pow_left₀ (by positivity) (by linarith) 3
          _ = 8 * ‖y‖ ^ 3 := by ring
      calc ‖iteratedFDeriv ℝ 2 v y‖ * (1 + ‖y‖) ^ 3
          ≤ ‖iteratedFDeriv ℝ 2 v y‖ * (8 * ‖y‖ ^ 3) := by gcongr
        _ = 8 * (‖iteratedFDeriv ℝ 2 v y‖ * ‖y‖ ^ 3) := by ring
        _ ≤ 8 * |C| := by gcongr
        _ ≤ _ := by linarith
  have hK : Integrable (fun y : ℂ =>
      (|M| * (1 + max R₀ 1) ^ 3 + 8 * |C|) * (1 + ‖y‖) ^ (-(3 : ℝ))) :=
    (integrable_one_add_norm (by rw [Complex.finrank_real_complex]; norm_num)).const_mul _

  have hpart : ∀ e : ℂ, ‖e‖ = 1 → Integrable (fun y => iteratedFDeriv ℝ 2 v y ![e, e]) := by
    intro e he
    refine hK.mono' ((continuous_eval_const (![e, e] : Fin 2 → ℂ)).comp hD2c).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    calc ‖iteratedFDeriv ℝ 2 v y ![e, e]‖
        ≤ ‖iteratedFDeriv ℝ 2 v y‖ * ∏ i, ‖(![e, e] : Fin 2 → ℂ) i‖ :=
          (iteratedFDeriv ℝ 2 v y).le_opNorm _
      _ = ‖iteratedFDeriv ℝ 2 v y‖ := by simp [Fin.prod_univ_two, he]
      _ ≤ _ := hbound y
  have hform : ∀ y e : ℂ, iteratedFDeriv ℝ 2 v y ![e, e] = fderiv ℝ (fderiv ℝ v) y e e := by
    intro y e
    rw [iteratedFDeriv_two_apply]
    rfl
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  have hemb := Complex.measurableEquivRealProd.symm.measurableEmbedding

  have htr : ∀ e : ℂ, ‖e‖ = 1 →
      (∫ y, iteratedFDeriv ℝ 2 v y ![e, e]) =
        ∫ p : ℝ × ℝ, iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e] ∧
      Integrable (fun p : ℝ × ℝ =>
        iteratedFDeriv ℝ 2 v (Complex.measurableEquivRealProd.symm p) ![e, e])
        (volume.prod volume) := by
    intro e he
    exact ⟨(hmp.integral_comp hemb _).symm, (hmp.integrable_comp_emb hemb).mpr (hpart e he)⟩
  have hz1 : ∫ y, iteratedFDeriv ℝ 2 v y ![1, 1] = 0 := by
    obtain ⟨h1, h2⟩ := htr 1 (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod_symm _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun b => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim ((b : ℂ) * Complex.I) 1 (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext x
    rw [hform, show Complex.measurableEquivRealProd.symm (x, b) = (b : ℂ) * Complex.I + (x : ℂ) * 1 from
      Complex.ext (by simp) (by simp)]
  have hzI : ∫ y, iteratedFDeriv ℝ 2 v y ![Complex.I, Complex.I] = 0 := by
    obtain ⟨h1, h2⟩ := htr Complex.I (by simp)
    rw [h1, Measure.volume_eq_prod, integral_prod _ h2]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun a => ?_)
    have := LaplacianDecayZero.integral_line_eq_zero v hdiff hlim (a : ℂ) Complex.I (by simp)
    simp only [Pi.zero_apply]
    rw [← this]
    congr 1
    ext t
    rw [hform, show Complex.measurableEquivRealProd.symm (a, t) = (a : ℂ) + (t : ℂ) * Complex.I from
      Complex.ext (by simp) (by simp)]
  have hΔ := laplacian_eq_iteratedFDeriv_complexPlane v
  have h1 := hpart 1 (by simp)
  have hI := hpart Complex.I (by simp)
  refine ⟨?_, ?_⟩
  · rw [hΔ]
    exact h1.add hI
  · rw [hΔ, integral_add h1 hI, hz1, hzI, add_zero]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

theorem LaplacianLogGrowth.full : LaplacianLogGrowth.Statement :=
  LaplacianLogGrowth.proof FsPotLaplacian.proof InvDerivDecay.proof LaplacianDecayZero.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
