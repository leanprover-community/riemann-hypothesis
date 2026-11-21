import Mathlib
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsNormEmbId

section
open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.Godement

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B]

theorem inner_map {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (g : Γ) (x y : B) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := by
  obtain ⟨-, -, hnorm, -⟩ := hU
  exact (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y

theorem inner_orbit {ρ : Γ → (B →L[ℂ] B)} (hU : IsU ρ) (v : B) (g h : Γ) :
    ⟪ρ g v, ρ h v⟫_ℂ = ⟪v, ρ (g⁻¹ * h) v⟫_ℂ := by
  rw [← GlobalTheory.CompanionTheory.Godement.inner_map hU g v (ρ (g⁻¹ * h) v)]
  obtain ⟨-, hmul, -, -⟩ := hU
  congr 1
  calc ρ h v = ρ (g * (g⁻¹ * h)) v := by rw [mul_inv_cancel_left]
    _ = ρ g (ρ (g⁻¹ * h) v) := by rw [hmul g (g⁻¹ * h), ContinuousLinearMap.mul_apply]

end Unitary

theorem mul_le_half_add (a b : ℝ≥0∞) : a * b ≤ 2⁻¹ * (a ^ 2 + b ^ 2) := by
  have h := ENNReal.young_inequality a b Real.HolderConjugate.two_two
  rw [ENNReal.rpow_two, ENNReal.rpow_two, ENNReal.ofReal_ofNat] at h
  calc a * b ≤ a ^ 2 / 2 + b ^ 2 / 2 := h
    _ = 2⁻¹ * (a ^ 2 + b ^ 2) := by
      rw [div_eq_mul_inv, div_eq_mul_inv, mul_comm (a ^ 2), mul_comm (b ^ 2), mul_add]

theorem norm_sq_integral_smul_le : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ f : Γ → ℂ, Measurable f → Integrable f ν →
    Integrable (fun g => ‖f g‖ ^ 2) ν →
    ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 ≤ (∫ g, ‖f g‖ ^ 2 ∂ν) * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := by
  intro Γ _ _ _ _ _ _ _ ν _ _ B _ _ _ ρ hU v hφ f hf hfi hf2
  obtain ⟨-, -, -, hcont⟩ := id hU
  have hA : 0 ≤ ∫ g, ‖f g‖ ^ 2 ∂ν := integral_nonneg fun g => sq_nonneg _
  have hB : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun g => norm_nonneg _
  by_cases hF : Integrable (fun g => f g • ρ g v) ν
  swap
  · rw [integral_undef hF, norm_zero, zero_pow two_ne_zero]
    exact mul_nonneg hA hB
  have hψc : Continuous fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := (continuous_const.inner (hcont v)).enorm
  have hψ : Measurable fun x : Γ => ‖⟪v, ρ x v⟫_ℂ‖ₑ := hψc.measurable
  have hfe : Measurable fun g : Γ => ‖f g‖ₑ ^ 2 := hf.enorm.pow_const 2
  have hswap : ∀ g h : Γ, ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ = ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ := by
    intro g h
    rw [← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v h g, ← GlobalTheory.CompanionTheory.Godement.inner_orbit hU v g h,
      ← inner_conj_symm (ρ h v) (ρ g v), RCLike.enorm_conj]
  have hswapm : AEMeasurable (Function.uncurry fun h g : Γ =>
      2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) (ν.prod ν) := by
    apply Measurable.aemeasurable
    exact measurable_const.mul ((hfe.comp measurable_snd).mul
      (hψ.comp (measurable_fst.inv.mul measurable_snd)))
  have hm3 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν :=
    (measurable_const.mul hfe).mul_const _
  have hm4 : Measurable fun h => 2⁻¹ * ‖f h‖ₑ ^ 2 := measurable_const.mul hfe
  have hII : ⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ =
      ∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν := by
    rw [← integral_inner hF]
    refine integral_congr_ae ?_
    filter_upwards with h
    rw [inner_smul_right, ← inner_conj_symm, ← integral_inner hF]
    simp only [inner_smul_right]
  have key : ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ₑ ≤
      (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [hII]
    calc ‖∫ h, f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν) ∂ν‖ₑ
        ≤ ∫⁻ h, ‖f h * starRingEnd ℂ (∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν)‖ₑ ∂ν :=
          enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν ∂ν := by
          refine lintegral_mono fun h => ?_
          beta_reduce
          rw [enorm_mul, RCLike.enorm_conj]
          calc ‖f h‖ₑ * ‖∫ g, f g * ⟪ρ h v, ρ g v⟫_ℂ ∂ν‖ₑ
              ≤ ‖f h‖ₑ * ∫⁻ g, ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := by
                gcongr
                exact enorm_integral_le_lintegral_enorm _
            _ ≤ ∫⁻ g, ‖f h‖ₑ * ‖f g * ⟪ρ h v, ρ g v⟫_ℂ‖ₑ ∂ν := lintegral_const_mul_le _ _
            _ ≤ _ := by
                refine lintegral_mono fun g => ?_
                beta_reduce
                rw [enorm_mul, GlobalTheory.CompanionTheory.Godement.inner_orbit hU, ← mul_assoc]
                gcongr ?_ * _
                exact GlobalTheory.CompanionTheory.Godement.mul_le_half_add _ _
      _ = ∫⁻ h, (2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν +
            ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν) ∂ν := by
          refine lintegral_congr fun h => ?_
          have hm : Measurable fun g => ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ := hψ.comp (measurable_const_mul h⁻¹)
          have hm2 : Measurable fun g => 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ :=
            measurable_const.mul hm
          calc ∫⁻ g, 2⁻¹ * (‖f h‖ₑ ^ 2 + ‖f g‖ₑ ^ 2) * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν
              = ∫⁻ g, (2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ +
                  2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ)) ∂ν :=
                lintegral_congr fun g => by ring
            _ = ∫⁻ g, 2⁻¹ * ‖f h‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ ∂ν +
                  ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν :=
                lintegral_add_left hm2 _
            _ = _ := by
                rw [lintegral_const_mul _ hm,
                  lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) h⁻¹]
      _ = (∫⁻ h, 2⁻¹ * ‖f h‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν) +
            ∫⁻ h, ∫⁻ g, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν :=
          lintegral_add_left hm3 _
      _ = 2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) +
            2⁻¹ * (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * (∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν) := by
          congr 1
          · rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
          · rw [lintegral_lintegral_swap hswapm]
            calc ∫⁻ g, ∫⁻ h, 2⁻¹ * (‖f g‖ₑ ^ 2 * ‖⟪v, ρ (h⁻¹ * g) v⟫_ℂ‖ₑ) ∂ν ∂ν
                = ∫⁻ g, 2⁻¹ * ‖f g‖ₑ ^ 2 * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν ∂ν := by
                  refine lintegral_congr fun g => ?_
                  have hm : Measurable fun h => ‖⟪v, ρ (g⁻¹ * h) v⟫_ℂ‖ₑ :=
                    hψ.comp (measurable_const_mul g⁻¹)
                  simp_rw [hswap g]
                  rw [← lintegral_mul_left_eq_self (fun x => ‖⟪v, ρ x v⟫_ℂ‖ₑ) g⁻¹,
                    ← lintegral_const_mul _ hm]
                  exact lintegral_congr fun h => by ring
              _ = _ := by
                  rw [lintegral_mul_const _ hm4, lintegral_const_mul _ hfe]
      _ = (∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν) * ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
          rw [← two_mul, ← mul_assoc, ← mul_assoc,
            ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hX : ENNReal.ofReal (∫ g, ‖f g‖ ^ 2 ∂ν) = ∫⁻ g, ‖f g‖ₑ ^ 2 ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hf2 (Filter.Eventually.of_forall fun g => sq_nonneg _)]
    refine lintegral_congr fun g => ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hY : ENNReal.ofReal (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) = ∫⁻ x, ‖⟪v, ρ x v⟫_ℂ‖ₑ ∂ν := by
    rw [ofReal_integral_eq_lintegral_ofReal hφ.norm (Filter.Eventually.of_forall fun g => norm_nonneg _)]
    exact lintegral_congr fun g => ofReal_norm_eq_enorm _
  have hL : ‖∫ g, f g • ρ g v ∂ν‖ ^ 2 = ‖⟪∫ g, f g • ρ g v ∂ν, ∫ g, f g • ρ g v ∂ν⟫_ℂ‖ := by
    rw [inner_self_eq_norm_sq_to_K]
    simp
  rw [hL, ← ENNReal.ofReal_le_ofReal_iff (mul_nonneg hA hB), ENNReal.ofReal_mul hA, hX, hY,
    ofReal_norm_eq_enorm]
  exact key

end GlobalTheory.CompanionTheory.Godement
end

section
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods Filter Topology
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.GodementCoeff

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure]
  [ν.IsMulRightInvariant] {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B]

private theorem integrableOn_and_setIntegral_sq_le_of_isU (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) {s : Set Γ} (hs : MeasurableSet s)
    (hs' : ν s ≠ ⊤) :
    IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν ∧
      ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hcont : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hbd : ∀ g, ‖⟪b, ρ g v⟫_ℂ‖ ≤ ‖b‖ * ‖v‖ := fun g =>
    (norm_inner_le_norm _ _).trans (by rw [hρ.norm])
  have hc2 : IntegrableOn (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) s ν := by
    refine Measure.integrableOn_of_bounded (M := (‖b‖ * ‖v‖) ^ 2) hs'
      (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun g => ?_)
    rw [norm_pow, norm_norm]
    exact pow_le_pow_left₀ (norm_nonneg _) (hbd g) 2
  set f : Γ → ℂ := s.indicator (fun g => starRingEnd ℂ ⟪b, ρ g v⟫_ℂ) with hfdef
  have hfm : Measurable f := ((Complex.continuous_conj.comp hcont).measurable).indicator hs
  have hfi : Integrable f ν := by
    refine (integrable_indicator_iff hs).mpr (Measure.integrableOn_of_bounded (M := ‖b‖ * ‖v‖) hs'
      (Complex.continuous_conj.comp hcont).aestronglyMeasurable (ae_of_all _ fun g => ?_))
    rw [Complex.norm_conj]
    exact hbd g
  have hfeq : (fun g => ‖f g‖ ^ 2) = s.indicator (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) := by
    funext g
    by_cases hg : g ∈ s <;> simp [hfdef, hg, norm_inner_symm]
  have hf2 : Integrable (fun g => ‖f g‖ ^ 2) ν := by
    rw [hfeq]
    exact (integrable_indicator_iff hs).mpr hc2
  have hG := GlobalTheory.CompanionTheory.Godement.norm_sq_integral_smul_le ν ρ hρ v hm f hfm hfi hf2
  rw [hfeq, integral_indicator hs] at hG
  have hint : Integrable (fun g => f g • ρ g v) ν :=
    hfi.smul_of_top_left (memLp_top_of_bound (hρ.cont v).aestronglyMeasurable ‖v‖
      (ae_of_all _ fun g => (hρ.norm g v).le))
  set I := ∫ g in s, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν with hIdef
  set w := ∫ g, f g • ρ g v ∂ν with hwdef
  have hinner : ⟪b, w⟫_ℂ = (I : ℂ) := by
    have h := (innerSL ℂ b).integral_comp_comm hint
    simp only [innerSL_apply_apply] at h
    rw [hwdef, ← h, hIdef, ← integral_indicator hs, ← integral_complex_ofReal]
    congr 1
    funext g
    by_cases hg : g ∈ s
    · rw [hfdef, Set.indicator_of_mem hg, Set.indicator_of_mem hg, inner_smul_right,
        Complex.conj_mul']
      push_cast
      rfl
    · simp [hfdef, hg]
  have hI0 : 0 ≤ I := setIntegral_nonneg hs fun _ _ => by positivity
  have hM0 : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  have h1 : I ≤ ‖b‖ * ‖w‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) b w
    rwa [hinner, Complex.norm_real, Real.norm_of_nonneg hI0] at h
  refine ⟨hc2, ?_⟩
  rcases hI0.eq_or_lt with h0 | hpos
  · rw [← h0]
    positivity
  · have h2 : I * I ≤ I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
      calc I * I ≤ (‖b‖ * ‖w‖) * (‖b‖ * ‖w‖) := mul_self_le_mul_self hI0 h1
        _ = ‖b‖ ^ 2 * ‖w‖ ^ 2 := by ring
        _ ≤ ‖b‖ ^ 2 * (I * ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) := by gcongr
        _ = I * ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by ring
    exact le_of_mul_le_mul_left h2 hpos

theorem sq_integrable_and_bound (ρ : Γ → (B →L[ℂ] B)) (hρ : IsU ρ) (v : B)
    (hm : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (b : B) :
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
      ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  have hK : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 :=
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) (sq_nonneg _)
  have hcont : Continuous fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 :=
    (continuous_const.inner (hρ.cont v)).norm.pow 2
  have key : ∀ s, MeasurableSet s → ν s ≠ ⊤ → ∫⁻ g in s, ‖‖⟪b, ρ g v⟫_ℂ‖ ^ 2‖ₑ ∂ν ≤
      ENNReal.ofReal ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) := by
    intro s hs hs'
    obtain ⟨hi, hle⟩ := integrableOn_and_setIntegral_sq_le_of_isU ν ρ hρ v hm b hs hs'
    rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
    apply ENNReal.ofReal_le_ofReal
    simpa only [norm_pow, norm_norm] using hle
  have hInt : Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν :=
    integrable_of_forall_fin_meas_le _ ENNReal.ofReal_lt_top hcont.aestronglyMeasurable key
  refine ⟨hInt, ?_⟩
  have hle := lintegral_le_of_forall_fin_meas_le _ key
  rw [← ofReal_integral_norm_eq_lintegral_enorm hInt, ENNReal.ofReal_le_ofReal_iff hK] at hle
  simpa only [norm_pow, norm_norm] using hle

end GlobalTheory.CompanionTheory.GodementCoeff

end
end

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matrix_coefficient_integrable_square : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
    [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
    {B : Type} [NormedAddCommGroup B] [InnerProductSpace ℂ B] [CompleteSpace B] (ρ : Γ → (B →L[ℂ] B)), IsU ρ → ∀ v : B, Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν → ∀ b : B,
    Integrable (fun g => ‖⟪b, ρ g v⟫_ℂ‖ ^ 2) ν ∧
    ∫ g, ‖⟪b, ρ g v⟫_ℂ‖ ^ 2 ∂ν ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2 := by
  atlas_forward_decl GlobalTheory.CompanionTheory.GodementCoeff.sq_integrable_and_bound
end

section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}

omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in

theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
end
end
