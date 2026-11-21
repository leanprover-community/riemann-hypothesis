import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionNearS
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.DivisionSkodaStep
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtNonIntChart
import GroundTheory.HeightsAndTheta.Heights.EffectiveHilbertSamuel.PExtension

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology
open scoped ENNReal

noncomputable section

namespace DivisionNearS

theorem exists_bound_of_iteratedFDeriv_eq_zero {D : ℕ} {f : (Fin D → ℂ) → ℂ}
    {w₀ : Fin D → ℂ} (hf : AnalyticAt ℂ f w₀) (m : ℕ)
    (h0 : ∀ k < m, iteratedFDeriv ℂ k f w₀ = 0) :
    ∃ C : ℝ, ∀ᶠ w in 𝓝 w₀, ‖f w‖ ≤ C * ‖w - w₀‖ ^ m := by
  obtain ⟨p, r, hp⟩ := hf
  have hps : ∀ y, p.partialSum m y = 0 := by
    intro y
    refine Finset.sum_eq_zero fun k hk => ?_
    have h1 := hp.factorial_smul y k
    rw [h0 k (Finset.mem_range.mp hk)] at h1
    have h2 : (k.factorial : ℂ) • p k (fun _ => y) = 0 := by
      rw [Nat.cast_smul_eq_nsmul]; simpa using h1
    exact (smul_eq_zero.mp h2).resolve_left (by exact_mod_cast k.factorial_ne_zero)
  obtain ⟨C, hC⟩ := (hp.hasFPowerSeriesAt.isBigO_sub_partialSum_pow m).bound
  refine ⟨C, ?_⟩
  have ht : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 0) := by
    simpa using (tendsto_id.sub_const w₀ : Tendsto (fun w => w - w₀) (𝓝 w₀) (𝓝 (w₀ - w₀)))
  filter_upwards [ht.eventually hC] with w hw
  simpa [hps, norm_pow, norm_norm] using hw

theorem exists_lowerBound_of_det_ne_zero {D : ℕ} {σ : (Fin D → ℂ) → (Fin D → ℂ)}
    {L : (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)} {w₀ : Fin D → ℂ} (hσ : HasFDerivAt σ L w₀)
    (hL : LinearMap.det (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0) (h0 : σ w₀ = 0) :
    ∃ κ > (0 : ℝ), ∀ᶠ w in 𝓝 w₀, κ * ‖w - w₀‖ ≤ ‖σ w‖ := by
  have hu : IsUnit (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :=
    (LinearMap.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hL)
  have hinj : Function.Injective (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) :=
    ((Module.End.isUnit_iff _).mp hu).injective
  obtain ⟨K, hK0, hK⟩ :=
    (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)).exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hinj)
  have hb : ∀ v, ‖v‖ ≤ K * ‖L v‖ := fun v =>
    ZeroHomClass.bound_of_antilipschitz (L : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) hK v
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK0
  have hε := hσ.isLittleO.bound (c := 1 / (2 * K)) (by positivity)
  refine ⟨1 / (2 * K), by positivity, ?_⟩
  filter_upwards [hε] with w hw
  rw [h0, sub_zero] at hw
  have h2 : ‖L (w - w₀)‖ ≤ ‖σ w‖ + 1 / (2 * K) * ‖w - w₀‖ := by
    calc ‖L (w - w₀)‖ = ‖σ w - (σ w - L (w - w₀))‖ := by congr 1; abel
      _ ≤ ‖σ w‖ + ‖σ w - L (w - w₀)‖ := norm_sub_le _ _
      _ ≤ _ := by gcongr
  have h3 : ‖w - w₀‖ ≤ K * ‖σ w‖ + ‖w - w₀‖ / 2 := by
    calc ‖w - w₀‖ ≤ K * ‖L (w - w₀)‖ := hb _
      _ ≤ K * (‖σ w‖ + 1 / (2 * K) * ‖w - w₀‖) := by gcongr
      _ = K * ‖σ w‖ + ‖w - w₀‖ / 2 := by field_simp
  have h4 : ‖w - w₀‖ ≤ 2 * K * ‖σ w‖ := by linarith
  calc 1 / (2 * K) * ‖w - w₀‖ ≤ 1 / (2 * K) * (2 * K * ‖σ w‖) := by gcongr
    _ = ‖σ w‖ := by field_simp

theorem finrank_real_fin_complex (D : ℕ) : Module.finrank ℝ (Fin D → ℂ) = 2 * D := by
  rw [Module.finrank_pi_fintype]
  simp [Complex.finrank_real_complex, mul_comm]

theorem lintegral_ball_rpow_lt_top {D : ℕ} (hD : 1 ≤ D) (w₀ : Fin D → ℂ) (ε a : ℝ)
    (ha : -(2 * D : ℝ) < a) :
    ∫⁻ w in Metric.ball w₀ ε, ENNReal.ofReal (‖w - w₀‖ ^ a) < ⊤ := by
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hint : IntegrableOn (fun x : Fin D → ℂ => ‖x‖ ^ a) (Metric.ball 0 ε) volume := by
    rw [integrableOn_fun_norm_addHaar volume (f := fun y : ℝ => y ^ a), finrank_real_fin_complex]
    have hr : -1 < ((2 * D - 1 : ℕ) : ℝ) + a := by
      have : ((2 * D - 1 : ℕ) : ℝ) = 2 * D - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [this]; linarith
    have hII := intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := ε) hr
    rcases le_or_gt ε 0 with hε | hε
    · simp [Ioo_eq_empty (not_lt.mpr hε)]
    · have hon : IntegrableOn (fun y : ℝ => y ^ (((2 * D - 1 : ℕ) : ℝ) + a)) (Ioo 0 ε) :=
        ((intervalIntegrable_iff_integrableOn_Ioc_of_le hε.le).mp hII).mono_set Ioo_subset_Ioc_self
      refine (integrableOn_congr_fun (fun y hy => ?_) measurableSet_Ioo).mp hon
      simp only [smul_eq_mul]
      rw [Real.rpow_add hy.1, Real.rpow_natCast]
  have h1 := hint.lintegral_lt_top
  have h2 : ∫⁻ w in Metric.ball w₀ ε, ENNReal.ofReal (‖w - w₀‖ ^ a) =
      ∫⁻ y in Metric.ball (0 : Fin D → ℂ) ε, ENNReal.ofReal (‖y‖ ^ a) := by
    rw [← lintegral_indicator measurableSet_ball, ← lintegral_indicator measurableSet_ball]
    rw [← lintegral_sub_right_eq_self (fun y => (Metric.ball (0 : Fin D → ℂ) ε).indicator
      (fun y => ENNReal.ofReal (‖y‖ ^ a)) y) w₀]
    congr 1
    funext w
    simp only [indicator, Metric.mem_ball, dist_eq_norm, sub_zero]
  rw [h2]; exact h1

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

theorem mem_source_chartIdx {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U) (x : U) :
    x ∈ (A.chart (chartIdx A x)).source :=
  Classical.choose_spec (A.cover x)

theorem setLIntegral_piece_le_chart {U : Type} [TopologicalSpace U] (A : FinHolAtlas D U)
    (f : Fin A.n → U → ℝ≥0∞) (c : Fin A.n) (W : Set U) (hW : IsOpen W)
    (hWc : W ⊆ (A.chart c).source)
    (hf : ∀ j, ∀ p ∈ (A.chart j).source ∩ W,
      f j p = ENNReal.ofReal (‖jac A j c p‖ ^ 2) * f c p) (j : Fin A.n) :
    ∫⁻ y in piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W), f j ((A.chart j).symm y) ≤
      ∫⁻ z in A.chart c '' W, f c ((A.chart c).symm z) := by
  set G : (Fin D → ℂ) → ℝ≥0∞ := fun z => f c ((A.chart c).symm z)
  set B := piece A j ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' W) with hBdef
  let φ : (Fin D → ℂ) → (Fin D → ℂ) := A.chart c ∘ (A.chart j).symm
  have hBmeas : MeasurableSet B := (ExtensionProof.measurableSet_piece A j).inter
    ((A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target hW).measurableSet
  have hBmem : ∀ y ∈ B, y ∈ (A.chart j).target ∧ (A.chart j).symm y ∈ W := fun y hy =>
    ⟨hy.2.1, hy.2.2⟩
  have hderiv : ∀ y ∈ B, HasFDerivWithinAt φ ((fderiv ℂ φ y).restrictScalars ℝ) B y := by
    intro y hy
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have han : AnalyticAt ℂ φ y := A.holo j c y ⟨hyt, hWc hyW⟩
    exact (han.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have hinj : InjOn φ B := by
    intro y₁ h₁ y₂ h₂ h
    obtain ⟨h₁t, h₁W⟩ := hBmem y₁ h₁
    obtain ⟨h₂t, h₂W⟩ := hBmem y₂ h₂
    have := (A.chart c).injOn (hWc h₁W) (hWc h₂W) h
    rw [← (A.chart j).right_inv h₁t, ← (A.chart j).right_inv h₂t, this]
  have hcv := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hBmeas hderiv hinj G
  have heq : ∫⁻ y in B, ENNReal.ofReal |((fderiv ℂ φ y).restrictScalars ℝ).det| * G (φ y)
      = ∫⁻ y in B, f j ((A.chart j).symm y) := by
    refine setLIntegral_congr_fun hBmeas fun y hy => ?_
    obtain ⟨hyt, hyW⟩ := hBmem y hy
    have hys : (A.chart j).symm y ∈ (A.chart j).source := (A.chart j).map_target hyt
    rw [hf j _ ⟨hys, hyW⟩, ExtNonInt.det_restrictScalars_complex, abs_of_nonneg (by positivity)]
    simp only [G, φ, Function.comp_apply, (A.chart c).left_inv (hWc hyW), jac,
      (A.chart j).right_inv hyt]
  have hsub : φ '' B ⊆ A.chart c '' W := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨(A.chart j).symm y, (hBmem y hy).2, rfl⟩
  calc ∫⁻ y in B, f j ((A.chart j).symm y) = ∫⁻ z in φ '' B, G z := by rw [hcv, heq]
    _ ≤ ∫⁻ z in A.chart c '' W, G z := lintegral_mono_set hsub

variable (X : EmbDatum D)

theorem e_transform (k : Fin X.N) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    X.e k j x = X.L.g j c x * X.e k c x := by
  have := (X.e_mem k).2.1 j c x hx
  simpa using this

theorem lin_apply (a : Fin X.N → ℂ) (j : Fin X.A.n) (x : X.U) :
    lin X.e a j x = ∑ k, a k * X.e k j x := by
  simp [lin, Finset.sum_apply]

theorem s_transform (Z : ZeroDatum X) (i : Fin D) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    Z.s i j x = X.L.g j c x * Z.s i c x := by
  simp only [ZeroDatum.s, lin_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx]; ring

theorem s_mem (Z : ZeroDatum X) (i : Fin D) : Z.s i ∈ X.L.sections 1 := by
  show lin X.e (Z.c i) ∈ X.L.sections 1
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (X.e_mem k)

theorem esum_pos (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) :
    0 < ∑ k, ‖X.e k j x‖ ^ 2 := by
  obtain ⟨k, hk⟩ := X.gen x
  have hc := mem_source_chartIdx X.A x
  have hg := X.L.ne_zero j (chartIdx X.A x) x ⟨hx, hc⟩
  have hne : X.e k j x ≠ 0 := by
    rw [e_transform X k j (chartIdx X.A x) x ⟨hx, hc⟩]; exact mul_ne_zero hg hk
  exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum (f := fun k => ‖X.e k j x‖ ^ 2)
    (fun _ _ => by positivity) (Finset.mem_univ k))

theorem esum_transform (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ k, ‖X.e k j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ k, ‖X.e k c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [e_transform X k j c x hx, norm_mul, mul_pow]

theorem ssum_transform (Z : ZeroDatum X) (j c : Fin X.A.n) (x : X.U)
    (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    ∑ i, ‖Z.s i j x‖ ^ 2 = ‖X.L.g j c x‖ ^ 2 * ∑ i, ‖Z.s i c x‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [s_transform X Z i j c x hx, norm_mul, mul_pow]

theorem ssum_le (Z : ZeroDatum X) (j : Fin X.A.n) (x : X.U) :
    ∑ i, ‖Z.s i j x‖ ^ 2 ≤ rSq Z.c * ∑ k, ‖X.e k j x‖ ^ 2 := by
  unfold rSq
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖Z.s i j x‖ ≤ ∑ k, ‖Z.c i k‖ * ‖X.e k j x‖ := by
    simp only [ZeroDatum.s, lin_apply]
    exact (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => norm_mul _ _))
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => ‖Z.c i k‖)
    (fun k => ‖X.e k j x‖)
  calc ‖Z.s i j x‖ ^ 2 ≤ (∑ k, ‖Z.c i k‖ * ‖X.e k j x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := h2

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

namespace DivisionNearS

variable {D : ℕ}

theorem exp_identity (T : ℕ) (t G g₂ E φc : ℝ) (hG : 0 < G) (hg₂ : 0 < g₂) :
    g₂ * G ^ (D + T) * G ^ (-(t + 1)) *
        Real.exp (-(φc + Real.log g₂ + (D : ℝ) * Real.log G +
          ((T : ℝ) - 1 - t) * (Real.log G + Real.log E))) =
      Real.exp (-(φc + ((T : ℝ) - 1 - t) * Real.log E)) := by
  obtain ⟨a, rfl⟩ : ∃ a, g₂ = Real.exp a := ⟨_, (Real.exp_log hg₂).symm⟩
  obtain ⟨b, rfl⟩ : ∃ b, G = Real.exp b := ⟨_, (Real.exp_log hG).symm⟩
  rw [Real.log_exp, Real.log_exp, ← Real.rpow_natCast, ← Real.exp_mul, ← Real.exp_mul,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem dens_transform (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (t : ℝ) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (j c : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source ∩ (X.A.chart c).source) :
    2 ^ D * ‖F j x‖ ^ 2 * (∑ i, ‖Z.s i j x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      ‖jac X.A j c x‖ ^ 2 * (2 ^ D * ‖F c x‖ ^ 2 * (∑ i, ‖Z.s i c x‖ ^ 2) ^ (-(t + 1)) *
        Real.exp (-(φA.φ c x + ((T : ℝ) - 1 - t) * fsWeight X.e c x))) := by
  have hG : 0 < ‖X.L.g j c x‖ ^ 2 := by
    have := X.L.ne_zero j c x hx; positivity
  have hg₂ : 0 < ‖X.L₂.g j c x‖ ^ 2 := by
    have := X.L₂.ne_zero j c x hx; positivity
  have hE := esum_pos X c x hx.2
  have hS : 0 ≤ ∑ i, ‖Z.s i c x‖ ^ 2 := by positivity
  have hFj : ‖F j x‖ ^ 2 = ‖jac X.A j c x‖ ^ 2 * ‖X.L₂.g j c x‖ ^ 2 *
      (‖X.L.g j c x‖ ^ 2) ^ (D + T) * ‖F c x‖ ^ 2 := by
    rw [hF.2.1 j c x hx, norm_mul, norm_mul, norm_mul, norm_pow]; ring
  have key := exp_identity (D := D) T t _ _ (∑ k, ‖X.e k c x‖ ^ 2) (φA.φ c x) hG hg₂
  rw [hFj, ssum_transform X Z j c x hx, Real.mul_rpow hG.le hS, φA.compat j c x hx]
  unfold fsWeight
  rw [esum_transform X j c x hx, Real.log_mul hG.ne' hE.ne', ← key]
  ring

theorem dens_eq (X : EmbDatum D) (φA : TwistWeight X.A X.L₂ X.L D) (T : ℕ) (t : ℝ)
    (j : Fin X.A.n) (x : X.U) (hx : x ∈ (X.A.chart j).source) (a S : ℝ) :
    a * S ^ (-(t + 1)) * Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * fsWeight X.e j x)) =
      a * Real.exp (-(φA.φ j x + (T : ℝ) * fsWeight X.e j x)) *
        (S ^ (-(t + 1)) * (∑ k, ‖X.e k j x‖ ^ 2) ^ (t + 1)) := by
  have hE := esum_pos X j x hx
  rw [Real.rpow_def_of_pos hE (t + 1)]
  unfold fsWeight
  have : Real.exp (-(φA.φ j x + ((T : ℝ) - 1 - t) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) =
      Real.exp (-(φA.φ j x + (T : ℝ) * Real.log (∑ k, ‖X.e k j x‖ ^ 2))) *
        Real.exp (Real.log (∑ k, ‖X.e k j x‖ ^ 2) * (t + 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [this]; ring

theorem ratio_le_of_nonpos (t S E r : ℝ) (ht : t + 1 ≤ 0) (hE : 0 < E) (hS : 0 ≤ S)
    (hr : 0 ≤ r) (hSE : S ≤ r * E) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) := by
  have h1 : S ^ (-(t + 1)) ≤ (r * E) ^ (-(t + 1)) := Real.rpow_le_rpow hS hSE (by linarith)
  rw [Real.mul_rpow hr hE.le] at h1
  have hEp : 0 < E ^ (t + 1) := Real.rpow_pos_of_pos hE _
  calc S ^ (-(t + 1)) * E ^ (t + 1) ≤ r ^ (-(t + 1)) * E ^ (-(t + 1)) * E ^ (t + 1) := by gcongr
    _ = r ^ (-(t + 1)) := by
      rw [Real.rpow_neg hE.le, mul_assoc, inv_mul_cancel₀ hEp.ne', mul_one]

theorem ratio_le_of_nonneg (t S E C : ℝ) (ht : 0 ≤ t + 1) (hE : 0 < E) (hS : 0 < S)
    (hSE : E ≤ C * S) :
    S ^ (-(t + 1)) * E ^ (t + 1) ≤ C ^ (t + 1) := by
  have h1 : E / S ≤ C := (div_le_iff₀ hS).mpr hSE
  have h2 : (E / S) ^ (t + 1) ≤ C ^ (t + 1) := Real.rpow_le_rpow (by positivity) h1 ht
  rw [Real.div_rpow hE.le hS.le, div_eq_mul_inv, ← Real.rpow_neg hS.le, mul_comm] at h2
  exact h2

theorem local_bound (X : EmbDatum D) (Z : ZeroDatum X) (φA : TwistWeight X.A X.L₂ X.L D)
    (T : ℕ) (hDT : D ≤ T) (F : Fin X.A.n → X.U → ℂ) (hF : F ∈ topSections X.A X.L₂ X.L (D + T))
    (hfil : IsFil X.A Z.s F (T - D)) (t : ℝ) (ht : 0 < t + 1) (x₀ : X.U)
    (hx₀ : x₀ ∈ zeroSet X.A Z.s) (c : Fin X.A.n) (hc : c = chartIdx X.A x₀) :
    ∃ ε > (0 : ℝ), ∃ K : ℝ, Metric.ball (X.A.chart c x₀) ε ⊆ (X.A.chart c).target ∧
      ∀ w ∈ Metric.ball (X.A.chart c x₀) ε,
        ENNReal.ofReal (2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 *
            (∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2) ^ (-(t + 1)) *
            Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
              ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))) ≤
          ENNReal.ofReal (K * ‖w - X.A.chart c x₀‖ ^ (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
  subst hc
  set c := chartIdx X.A x₀
  set w₀ := X.A.chart c x₀
  have hx₀s : x₀ ∈ (X.A.chart c).source := mem_source_chartIdx X.A x₀
  have hw₀t : w₀ ∈ (X.A.chart c).target := (X.A.chart c).map_source hx₀s
  have hsymm : (X.A.chart c).symm w₀ = x₀ := (X.A.chart c).left_inv hx₀s
  have hmem : w₀ ∈ (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source :=
    ⟨hw₀t, by simpa [hsymm] using hx₀s⟩
  have hnhd : (X.A.chart c).target ∩ (X.A.chart c).symm ⁻¹' (X.A.chart c).source ∈ 𝓝 w₀ :=
    ((X.A.chart c).continuousOn_symm.isOpen_inter_preimage (X.A.chart c).open_target
      (X.A.chart c).open_source).mem_nhds hmem

  have hfan : AnalyticAt ℂ (F c ∘ (X.A.chart c).symm) w₀ := hF.1 c c w₀ hmem
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_iteratedFDeriv_eq_zero hfan (T - D)
    (fun k hk => hfil x₀ hx₀ k hk)

  set σ : (Fin D → ℂ) → (Fin D → ℂ) := fun z i => Z.s i c ((X.A.chart c).symm z)
  have hσd : DifferentiableAt ℂ σ w₀ :=
    differentiableAt_pi.mpr fun i => ((s_mem X Z i).1 c c w₀ hmem).differentiableAt
  have hdet : LinearMap.det (fderiv ℂ σ w₀ : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ)) ≠ 0 :=
    Z.nondeg x₀ hx₀
  have hσ0 : σ w₀ = 0 := funext fun i => by simp only [σ, hsymm]; exact hx₀ i
  obtain ⟨κ, hκ, hκb⟩ := exists_lowerBound_of_det_ne_zero hσd.hasFDerivAt hdet hσ0

  set h : (Fin D → ℂ) → ℝ := fun w => Real.exp (-(φA.φ c ((X.A.chart c).symm w) +
    ((T : ℝ) - 1 - t) * fsWeight X.e c ((X.A.chart c).symm w)))
  have hφc : ContinuousAt (fun w => φA.φ c ((X.A.chart c).symm w)) w₀ :=
    ((φA.smooth c c).continuousOn).continuousAt hnhd
  have hEc : ContinuousAt (fun w => ∑ k, ‖X.e k c ((X.A.chart c).symm w)‖ ^ 2) w₀ := by
    have hk : ∀ k, ContinuousAt (fun w => X.e k c ((X.A.chart c).symm w)) w₀ := fun k =>
      ((X.e_mem k).1 c c w₀ hmem).continuousAt
    exact tendsto_finsetSum Finset.univ fun k _ => (hk k).norm.pow 2
  have hE0 : (∑ k, ‖X.e k c ((X.A.chart c).symm w₀)‖ ^ 2) ≠ 0 := by
    rw [hsymm]; exact (esum_pos X c x₀ hx₀s).ne'
  have hcont : ContinuousAt h w₀ :=
    (hφc.add (continuousAt_const.mul (hEc.log hE0))).neg.rexp
  have hev : ∀ᶠ w in 𝓝 w₀, h w < h w₀ + 1 := hcont.eventually (gt_mem_nhds (lt_add_one _))
  have hall := (show ∀ᶠ w in 𝓝 w₀, w ∈ (X.A.chart c).target from
    (X.A.chart c).open_target.mem_nhds hw₀t).and (hC₁.and (hκb.and hev))
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp hall
  have hh0 : 0 < h w₀ := Real.exp_pos _
  refine ⟨ε, hε, 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1), fun w hw => (hball w hw).1,
    fun w hw => ?_⟩
  obtain ⟨-, h1, h2, h3⟩ := hball w hw
  apply ENNReal.ofReal_le_ofReal
  have hK : 0 ≤ 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by positivity
  by_cases hw0 : w = w₀
  · have hS0 : ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2 = 0 := by
      rw [hw0, hsymm]; simp [show ∀ i, Z.s i c x₀ = 0 from hx₀]
    rw [hS0, Real.zero_rpow (by linarith)]
    simp only [mul_zero, zero_mul]
    exact mul_nonneg hK (Real.rpow_nonneg (norm_nonneg _) _)
  · set r := ‖w - w₀‖ with hr
    have hr0 : 0 < r := norm_pos_iff.mpr (sub_ne_zero.mpr hw0)
    set S := ∑ i, ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2
    have hσS : ‖σ w‖ ≤ Real.sqrt S := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      refine Real.le_sqrt_of_sq_le ?_
      exact Finset.single_le_sum (f := fun i => ‖Z.s i c ((X.A.chart c).symm w)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    have hS : κ ^ 2 * r ^ 2 ≤ S := by
      have : (κ * r) ^ 2 ≤ (Real.sqrt S) ^ 2 :=
        pow_le_pow_left₀ (by positivity) (h2.trans hσS) 2
      rwa [Real.sq_sqrt (by positivity), mul_pow] at this
    have hSr : S ^ (-(t + 1)) ≤ (κ ^ 2 * r ^ 2) ^ (-(t + 1)) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hS (by linarith)
    have hF2 : ‖F c ((X.A.chart c).symm w)‖ ^ 2 ≤ (C₁ * r ^ (T - D)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have hra : r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) =
        (r ^ (T - D)) ^ 2 * (r ^ 2) ^ (-(t + 1)) := by
      rw [← pow_mul, ← Real.rpow_natCast r ((T - D) * 2), ← Real.rpow_two r,
        ← Real.rpow_mul hr0.le, ← Real.rpow_add hr0]
      congr 1
      push_cast [Nat.cast_sub hDT]
      ring
    calc 2 ^ D * ‖F c ((X.A.chart c).symm w)‖ ^ 2 * S ^ (-(t + 1)) * h w
        ≤ 2 ^ D * (C₁ * r ^ (T - D)) ^ 2 * (κ ^ 2 * r ^ 2) ^ (-(t + 1)) * (h w₀ + 1) := by
          gcongr
      _ = 2 ^ D * C₁ ^ 2 * (κ ^ 2) ^ (-(t + 1)) * (h w₀ + 1) *
            r ^ (2 * ((T : ℝ) - D) - 2 * (t + 1)) := by
          rw [hra, Real.mul_rpow (by positivity) (by positivity)]; ring

end DivisionNearS

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.EffectiveHS

open MeasureTheory Set Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
  GroundTheory.Heights₂.Heights.HilbertSamuel
open scoped ENNReal

noncomputable section

open DivisionNearS in

theorem DivisionNearS.proof : DivisionNearS.Statement := by
  intro D T X Z φA hD hDT F hFv hfil t ht
  obtain ⟨hF, hFn⟩ := hFv
  set d : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) *
      Real.exp (-(φA.φ a x + ((T : ℝ) - 1 - t) * fsWeight X.e a x))) with hd
  set n : Fin X.A.n → X.U → ℝ≥0∞ := fun a x => ENNReal.ofReal (2 ^ D * ‖F a x‖ ^ 2 *
    Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x))) with hn
  have hnT : chartIntegral X.A n < ⊤ := hFn
  show chartIntegral X.A d < ⊤

  have hcmp : ∀ a x (M : ℝ), 0 ≤ M → (x ∈ (X.A.chart a).source →
      (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤ M) →
      d a x ≤ ENNReal.ofReal M * n a x := by
    intro a x M hM hR
    by_cases hx : x ∈ (X.A.chart a).source
    · simp only [hd, hn]
      rw [← ENNReal.ofReal_mul hM]
      apply ENNReal.ofReal_le_ofReal
      rw [dens_eq X φA T t a x hx]
      calc 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) *
            ((∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1))
          ≤ 2 ^ D * ‖F a x‖ ^ 2 * Real.exp (-(φA.φ a x + (T : ℝ) * fsWeight X.e a x)) * M :=
            mul_le_mul_of_nonneg_left (hR hx) (by positivity)
        _ = _ := by ring
    · have h0 : F a x = 0 := hF.2.2 a x hx
      simp [hd, h0]
  rcases le_or_gt (t + 1) 0 with ht1 | ht1
  ·
    have hr : 0 ≤ rSq Z.c := by unfold rSq; positivity
    have hM : 0 ≤ rSq Z.c ^ (-(t + 1)) := Real.rpow_nonneg hr _
    calc chartIntegral X.A d
        ≤ chartIntegral X.A (fun a x => ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * n a x) :=
          ExtensionProof.chartIntegral_mono _ fun a x => hcmp a x _ hM fun hx =>
            ratio_le_of_nonpos t _ _ _ ht1 (esum_pos X a x hx) (by positivity) hr
              (ssum_le X Z a x)
      _ = ENNReal.ofReal (rSq Z.c ^ (-(t + 1))) * chartIntegral X.A n :=
          ExtensionProof.chartIntegral_const_mul _ _ ENNReal.ofReal_ne_top _
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hnT
  ·
    have hSfin : (zeroSet X.A Z.s).Finite := Z.finite
    choose ε hε K hsub hbd using fun x₀ : zeroSet X.A Z.s =>
      local_bound X Z φA T hDT F hF hfil t ht1 x₀ x₀.2 (chartIdx X.A x₀) rfl
    set W : zeroSet X.A Z.s → Set X.U := fun x₀ => (X.A.chart (chartIdx X.A x₀)).source ∩
      X.A.chart (chartIdx X.A x₀) ⁻¹' Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) with hW
    have hWo : ∀ x₀, IsOpen (W x₀) := fun x₀ =>
      (X.A.chart _).continuousOn.isOpen_inter_preimage (X.A.chart _).open_source Metric.isOpen_ball
    have hWc : ∀ x₀ : zeroSet X.A Z.s, W x₀ ⊆ (X.A.chart (chartIdx X.A x₀)).source := fun _ _ h => h.1
    have hWimg : ∀ x₀ : zeroSet X.A Z.s, X.A.chart (chartIdx X.A x₀) '' W x₀ ⊆
        Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀) := by
      rintro x₀ _ ⟨y, hy, rfl⟩; exact hy.2
    set V : Set X.U := ⋃ x₀, W x₀ with hV
    have hVo : IsOpen V := isOpen_iUnion hWo
    have hSV : zeroSet X.A Z.s ⊆ V := fun x hx =>
      mem_iUnion.mpr ⟨⟨x, hx⟩, mem_source_chartIdx X.A x, by
        simpa [Metric.mem_ball] using hε ⟨x, hx⟩⟩
    obtain ⟨C, hC⟩ := Z.fl V hVo hSV

    have hoff : ∀ a x, x ∈ (X.A.chart a).source → x ∉ V →
        (∑ i, ‖Z.s i a x‖ ^ 2) ^ (-(t + 1)) * (∑ k, ‖X.e k a x‖ ^ 2) ^ (t + 1) ≤
          |C| ^ (t + 1) := by
      intro a x hx hxV
      have hc' := mem_source_chartIdx X.A x
      have h1 : ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2 ≤
          C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 := hC x hxV
      have hnz : x ∉ zeroSet X.A Z.s := fun h => hxV (hSV h)
      have hG : 0 < ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 := by
        have := X.L.ne_zero a (chartIdx X.A x) x ⟨hx, hc'⟩; positivity
      have hSpos : 0 < ∑ i, ‖Z.s i a x‖ ^ 2 := by
        simp only [zeroSet, mem_ofPred_eq, not_forall] at hnz
        obtain ⟨i, hi⟩ := hnz
        have hne : Z.s i a x ≠ 0 := by
          rw [s_transform X Z i a (chartIdx X.A x) x ⟨hx, hc'⟩]
          exact mul_ne_zero (X.L.ne_zero a _ x ⟨hx, hc'⟩) hi
        exact lt_of_lt_of_le (by positivity) (Finset.single_le_sum
          (f := fun i => ‖Z.s i a x‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ i))
      have hSE : ∑ k, ‖X.e k a x‖ ^ 2 ≤ |C| * ∑ i, ‖Z.s i a x‖ ^ 2 := by
        rw [esum_transform X a (chartIdx X.A x) x ⟨hx, hc'⟩,
          ssum_transform X Z a (chartIdx X.A x) x ⟨hx, hc'⟩]
        have h2 : C * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 ≤
            |C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2 :=
          mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
        calc ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * ∑ k, ‖X.e k (chartIdx X.A x) x‖ ^ 2
            ≤ ‖X.L.g a (chartIdx X.A x) x‖ ^ 2 * (|C| * ∑ i, ‖Z.s i (chartIdx X.A x) x‖ ^ 2) :=
              mul_le_mul_of_nonneg_left (h1.trans h2) hG.le
          _ = _ := by ring
      exact ratio_le_of_nonneg t _ _ _ ht1.le (esum_pos X a x hx) hSpos hSE

    have htr : ∀ x₀ : zeroSet X.A Z.s, ∀ a, ∀ p ∈ (X.A.chart a).source ∩ W x₀,
        d a p = ENNReal.ofReal (‖jac X.A a (chartIdx X.A x₀) p‖ ^ 2) * d (chartIdx X.A x₀) p := by
      intro x₀ a p hp
      simp only [hd]
      rw [← ENNReal.ofReal_mul (by positivity)]
      congr 1
      exact dens_transform X Z φA T t F hF a (chartIdx X.A x₀) p ⟨hp.1, hp.2.1⟩
    have hexp : ∀ x₀ : zeroSet X.A Z.s, ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
        ENNReal.ofReal (K x₀ * ‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
          (2 * ((T : ℝ) - D) - 2 * (t + 1))) < ⊤ := by
      intro x₀
      have ha : -(2 * D : ℝ) < 2 * ((T : ℝ) - D) - 2 * (t + 1) := by linarith
      calc _ ≤ ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal |K x₀| * ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := by
            refine lintegral_mono fun w => ?_
            rw [← ENNReal.ofReal_mul (abs_nonneg _)]
            exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self _)
              (Real.rpow_nonneg (norm_nonneg _) _))
        _ = ENNReal.ofReal |K x₀| * ∫⁻ w in Metric.ball (X.A.chart (chartIdx X.A x₀) x₀) (ε x₀),
            ENNReal.ofReal (‖w - X.A.chart (chartIdx X.A x₀) x₀‖ ^
              (2 * ((T : ℝ) - D) - 2 * (t + 1))) := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (lintegral_ball_rpow_lt_top hD _ _ _ ha)
    have : Finite (zeroSet X.A Z.s) := hSfin.to_subtype
    have : Fintype (zeroSet X.A Z.s) := Fintype.ofFinite _
    unfold chartIntegral
    refine ENNReal.sum_lt_top.mpr fun j _ => ?_
    set O := (X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' V with hOdef
    have hO : IsOpen O :=
      (X.A.chart j).continuousOn_symm.isOpen_inter_preimage (X.A.chart j).open_target hVo
    rw [← inter_union_sdiff (piece X.A j) O]
    refine (lintegral_union_le _ _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨?_, ?_⟩)
    ·
      have hcov : piece X.A j ∩ O ⊆
          ⋃ x₀, piece X.A j ∩ ((X.A.chart j).target ∩ (X.A.chart j).symm ⁻¹' W x₀) := by
        rintro y ⟨hp, hyt, hyV⟩
        obtain ⟨x₀, hx₀⟩ := mem_iUnion.mp hyV
        exact mem_iUnion.mpr ⟨x₀, hp, hyt, hx₀⟩
      refine (lintegral_mono_set hcov).trans_lt ((lintegral_iUnion_le _ _).trans_lt ?_)
      rw [tsum_fintype]
      refine ENNReal.sum_lt_top.mpr fun x₀ _ => ?_
      refine (setLIntegral_piece_le_chart X.A d (chartIdx X.A x₀) (W x₀) (hWo x₀) (hWc x₀)
        (htr x₀) j).trans_lt ?_
      refine (lintegral_mono_set (hWimg x₀)).trans_lt ?_
      exact (setLIntegral_mono' measurableSet_ball fun w hw => hbd x₀ w hw).trans_lt (hexp x₀)
    ·
      have hmeas : MeasurableSet (piece X.A j \ O) :=
        (ExtensionProof.measurableSet_piece X.A j).diff hO.measurableSet
      have hM : (0 : ℝ) ≤ |C| ^ (t + 1) := Real.rpow_nonneg (abs_nonneg _) _
      refine (setLIntegral_mono' hmeas (g := fun y => ENNReal.ofReal (|C| ^ (t + 1)) *
        n j ((X.A.chart j).symm y)) fun y hy => ?_).trans_lt ?_
      · have hyt : y ∈ (X.A.chart j).target := hy.1.1
        have hyV : (X.A.chart j).symm y ∉ V := fun h => hy.2 ⟨hyt, h⟩
        exact hcmp j _ _ hM fun hx => hoff j _ hx hyV
      · refine (lintegral_mono_set sdiff_subset).trans_lt ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_of_le_of_lt ?_ hnT)
        exact Finset.single_le_sum (f := fun k => ∫⁻ y in piece X.A k, n k ((X.A.chart k).symm y))
          (fun _ _ => by simp) (Finset.mem_univ j)

end

end GroundTheory.Heights₂.Heights.EffectiveHS
end
