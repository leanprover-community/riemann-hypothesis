import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.JQExpansion

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries ArithmeticFunction
open scoped MatrixGroups ArithmeticFunction.sigma

noncomputable section

def DeltaQExpansionIntegral.Statement : Prop :=
  ∃ D : PowerSeries ℤ, constantCoeff D = 1 ∧
    qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) (X * D)

namespace DeltaQExpansionIntegral

def sigmaSeries (k : ℕ) : PowerSeries ℤ := mk fun n ↦ (σ k n : ℤ)

theorem qExpansion_E₄ :
    qExpansion 1 E₄ = map (Int.castRingHom ℂ) (1 + (240 : ℤ) • sigmaSeries 3) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨2, rfl⟩, coeff_map]
  have hb : bernoulli 4 = -1 / 30 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_add, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem qExpansion_E₆ :
    qExpansion 1 E₆ = map (Int.castRingHom ℂ) (1 - (504 : ℤ) • sigmaSeries 5) := by
  ext m
  rw [E_qExpansion_coeff _ ⟨3, rfl⟩, coeff_map]
  have hb : bernoulli 6 = 1 / 42 := by decide +kernel
  rcases eq_or_ne m 0 with rfl | hm
  · simp [sigmaSeries]
  · rw [map_sub, map_zsmul]
    simp [hm, sigmaSeries, hb, coeff_one]
    norm_num

theorem twelve_dvd (n : ℕ) : 12 ∣ 5 * σ 3 n + 7 * σ 5 n := by
  rw [sigma_apply, sigma_apply, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  rw [← ZMod.natCast_eq_zero_iff]
  push_cast
  generalize (d : ZMod 12) = x
  revert x
  decide

def cSeries : PowerSeries ℤ := mk fun n ↦ (((5 * σ 3 n + 7 * σ 5 n) / 12 : ℕ) : ℤ)

theorem twelve_smul_cSeries :
    (12 : ℤ) • cSeries = (5 : ℤ) • sigmaSeries 3 + (7 : ℤ) • sigmaSeries 5 := by
  ext n
  have h := Nat.mul_div_cancel' (twelve_dvd n)
  rw [map_add, map_zsmul, map_zsmul, map_zsmul]
  simp only [cSeries, sigmaSeries, coeff_mk, smul_eq_mul]
  exact_mod_cast h

theorem qExpansion_discriminant_smul :
    (1728 : ℂ) • qExpansion 1 ModularForm.discriminant =
      qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
  have e : (1728 : ℂ) • (⇑CuspForm.discriminant) = ⇑(E₄.pow 3) - ⇑(E₆.pow 2) := by
    funext τ
    simp only [Pi.smul_apply, Pi.sub_apply, ModularForm.coe_pow, Pi.pow_apply, smul_eq_mul,
      CuspForm.coe_discriminant, discriminant_eq_E₄_cube_sub_E₆_sq]
    ring
  rw [← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₄ 3,
    ← ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL E₆ 2,
    ← ModularForm.qExpansion_sub one_pos one_mem_strictPeriods_SL (E₄.pow 3) (E₆.pow 2), ← e,
    ModularForm.qExpansion_smul one_pos one_mem_strictPeriods_SL (1728 : ℂ) CuspForm.discriminant]
  rfl

theorem proof : Statement := by
  set A := sigmaSeries 3
  set B := sigmaSeries 5
  set Ez : PowerSeries ℤ := 100 * A ^ 2 + 8000 * A ^ 3 - 147 * B ^ 2 + cSeries with hEz
  have hC := twelve_smul_cSeries
  simp only [zsmul_eq_mul, Int.cast_ofNat] at hC
  have hring : (1 + (240 : ℤ) • A) ^ 3 - (1 - (504 : ℤ) • B) ^ 2 = 1728 * Ez := by
    simp only [zsmul_eq_mul, Int.cast_ofNat, hEz]
    linear_combination (-144 : PowerSeries ℤ) * hC
  have key : qExpansion 1 ModularForm.discriminant = map (Int.castRingHom ℂ) Ez := by
    have h2 : (1728 : ℂ) • map (Int.castRingHom ℂ) Ez = qExpansion 1 E₄ ^ 3 - qExpansion 1 E₆ ^ 2 := by
      rw [qExpansion_E₄, qExpansion_E₆, ← map_pow, ← map_pow, ← map_sub, hring, map_mul,
        map_ofNat, Algebra.smul_def, map_ofNat]
    exact smul_right_injective _ (by norm_num : (1728 : ℂ) ≠ 0)
      (qExpansion_discriminant_smul.trans h2.symm)
  have h0 : constantCoeff Ez = 0 := by
    simp [hEz, A, B, sigmaSeries, cSeries]
  obtain ⟨D, hD⟩ := X_dvd_iff.mpr h0
  refine ⟨D, ?_, hD ▸ key⟩
  have h1 := discriminant_qExpansion_coeff_one
  rw [key, hD, coeff_map, coeff_succ_X_mul, eq_intCast] at h1
  rw [← coeff_zero_eq_constantCoeff_apply]
  exact_mod_cast h1

end DeltaQExpansionIntegral

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open UpperHalfPlane ModularForm EisensteinSeries PowerSeries GroundTheory.Global.Elliptic Function
open scoped MatrixGroups Manifold

noncomputable section

namespace JQExpansion

lemma periodic_comp_ofComplex_of {f : ℍ → ℂ}
    (hf : ∀ z : ℂ, 0 < z.im → f (ofComplex (z + 1)) = f (ofComplex z)) :
    Periodic (f ∘ ofComplex) ((1 : ℝ) : ℂ) := by
  intro w
  simp only [comp_apply, Complex.ofReal_one]
  by_cases hw : 0 < w.im
  · exact hf w hw
  · have hw' : (w + 1).im ≤ 0 := by simpa using hw
    rw [ofComplex_apply_eq_of_im_nonpos hw' (not_lt.mp hw)]

theorem proof : JQExpansion.Statement := by
  set Q : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ with hQdef
  set φ : ℍ → ℂ := fun τ ↦ Periodic.qParam 1 τ * modularJ τ with hφdef
  have hqper : ∀ z : ℂ, Periodic.qParam 1 (z + 1) = Periodic.qParam 1 z := fun z ↦ by
    simp only [Periodic.qParam, Complex.ofReal_one, div_one, mul_add, mul_one, Complex.exp_add,
      Complex.exp_two_pi_mul_I]
  have hQper : Periodic (Q ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [hQdef, ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1,
]
      exact hqper z
  have hφper : Periodic (φ ∘ ofComplex) ((1 : ℝ) : ℂ) :=
    periodic_comp_ofComplex_of fun z hz ↦ by
      have hE := SlashInvariantFormClass.periodic_comp_ofComplex E₄ one_mem_strictPeriods_SL z
      have hD := SlashInvariantFormClass.periodic_comp_ofComplex CuspForm.discriminant
        one_mem_strictPeriods_SL z
      have hz1 : 0 < (z + 1).im := by simpa using hz
      simp only [comp_apply, Complex.ofReal_one, CuspForm.coe_discriminant] at hE hD
      simp only [hφdef, modularJ, hE, hD]
      rw [ofComplex_apply_of_im_pos hz, ofComplex_apply_of_im_pos hz1]
      simp only [hqper]
  have hQhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) Q := UpperHalfPlane.mdifferentiable_iff.mpr
    ((Periodic.differentiable_qParam (h := 1)).differentiableOn.congr fun z hz ↦ by
      simp [hQdef, ofComplex_apply_of_im_pos (show 0 < z.im from hz)])
  have hφhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) φ := UpperHalfPlane.mdifferentiable_iff.mpr
    ((UpperHalfPlane.mdifferentiable_iff.mp hQhol).mul differentiableOn_modularJC)
  have hQb : IsBoundedAtImInfty Q :=
    isBoundedAtImInfty_iff.mpr ⟨1, 0, fun τ _ ↦ (Periodic.norm_qParam_lt_one one_pos τ.im_pos).le⟩
  have hφb : IsBoundedAtImInfty φ := by
    obtain ⟨M, A, hM⟩ := isBoundedAtImInfty_iff.mp (ModularFormClass.bdd_at_infty E₄)
    obtain ⟨C, hC⟩ := exp_isBigO_discriminant.bound
    obtain ⟨A', hA'⟩ := (atImInfty_mem _).mp hC
    refine isBoundedAtImInfty_iff.mpr ⟨C * M ^ 3, max A A', fun τ hτ ↦ ?_⟩
    have h1 := hM τ (le_of_max_le_left hτ)
    have hΔ : 0 < ‖ModularForm.discriminant τ‖ := norm_pos_iff.mpr (discriminant_ne_zero τ)
    have h2 : ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ ≤ C := by
      have h3 := hA' τ (le_of_max_le_right hτ)
      simp only [Set.mem_ofPred_eq, Real.norm_of_nonneg (Real.exp_pos _).le] at h3
      rw [div_le_iff₀ hΔ, Periodic.norm_qParam, div_one, UpperHalfPlane.coe_im]
      exact h3
    calc ‖φ τ‖ = ‖Periodic.qParam 1 (τ : ℂ)‖ / ‖ModularForm.discriminant τ‖ * ‖E₄ τ‖ ^ 3 := by
          simp only [hφdef, modularJ, norm_mul, norm_div, norm_pow]
          ring
      _ ≤ C * M ^ 3 := mul_le_mul h2 (pow_le_pow_left₀ (norm_nonneg _) h1 3) (by positivity)
          (le_trans (by positivity) h2)
  have hQa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hQper hQhol hQb
  have hφa := UpperHalfPlane.analyticAt_cuspFunction_zero one_pos hφper hφhol hφb
  have hΔa := ModularFormClass.analyticAt_cuspFunction_zero CuspForm.discriminant one_pos
    one_mem_strictPeriods_SL
  have hE3a := ModularFormClass.analyticAt_cuspFunction_zero (E₄.pow 3) one_pos
    one_mem_strictPeriods_SL

  have hQX : qExpansion 1 Q = X := by
    have hsum : ∀ τ : ℍ, HasSum
        (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) (Q τ) := by
      intro τ
      have e : (fun n : ℕ ↦ (if n = 1 then (1 : ℂ) else 0) • Periodic.qParam 1 (τ : ℂ) ^ n) =
          fun n ↦ if n = 1 then Periodic.qParam 1 (τ : ℂ) else 0 := by
        funext n
        split_ifs with h <;> simp [h]
      rw [e]
      exact hasSum_ite_eq 1 _
    ext m
    have h := UpperHalfPlane.qExpansion_coeff_unique (⟨Q, hQhol.continuous⟩ : C(ℍ, ℂ)) one_pos
      hQa hsum m
    rw [coeff_X]
    exact h.symm

  have hprod : φ * ⇑CuspForm.discriminant = Q * ⇑(E₄.pow 3) := by
    funext τ
    have := discriminant_ne_zero τ
    simp only [Pi.mul_apply, hφdef, hQdef, modularJ, ModularForm.coe_pow, Pi.pow_apply,
      CuspForm.coe_discriminant]
    field_simp
  have hq := congrArg (qExpansion 1) hprod
  obtain ⟨D, hD0, hΔ⟩ := DeltaQExpansionIntegral.proof
  rw [UpperHalfPlane.qExpansion_mul hφa hΔa, UpperHalfPlane.qExpansion_mul hQa hE3a, hQX,
    ModularForm.qExpansion_pow one_pos one_mem_strictPeriods_SL,
    DeltaQExpansionIntegral.qExpansion_E₄, CuspForm.coe_discriminant, hΔ, map_mul, map_X,
    ← mul_assoc, mul_comm (qExpansion 1 φ) X, mul_assoc] at hq
  have hq' := mul_left_cancel₀ X_ne_zero hq
  set E4Z : PowerSeries ℤ := 1 + (240 : ℤ) • DeltaQExpansionIntegral.sigmaSeries 3 with hE4Z
  set u := invOfUnit D 1 with hu
  have hDu : D * u = 1 := mul_invOfUnit D 1 (by simp [hD0])
  have ha : qExpansion 1 φ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
    calc qExpansion 1 φ = qExpansion 1 φ * map (Int.castRingHom ℂ) (D * u) := by
          rw [hDu, map_one, mul_one]
      _ = map (Int.castRingHom ℂ) (E4Z ^ 3 * u) := by
          rw [map_mul, ← mul_assoc, hq', map_mul, map_pow]
  refine ⟨fun n ↦ coeff n (E4Z ^ 3 * u), ?_, fun τ ↦ ?_⟩
  · simp [hu, hE4Z, constantCoeff_invOfUnit, DeltaQExpansionIntegral.sigmaSeries]
  · have h := UpperHalfPlane.hasSum_qExpansion one_pos hφper hφhol hφb τ
    have e : ∀ n, coeff n (map (Int.castRingHom ℂ) (E4Z ^ 3 * u)) = ((coeff n (E4Z ^ 3 * u) : ℤ) : ℂ) :=
      fun n ↦ by rw [coeff_map, eq_intCast]
    simp only [ha, e, smul_eq_mul] at h
    exact h

end JQExpansion

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end
