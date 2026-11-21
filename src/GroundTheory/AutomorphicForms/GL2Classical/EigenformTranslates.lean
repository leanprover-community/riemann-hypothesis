import Mathlib
import GroundTheory.AutomorphicForms.GL2Classical.TranslateSpanLeCuspForms
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsDecay

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

omit [NeZero N] in
theorem one_mem_strictPeriods_Gamma0 :
    (1 : ℝ) ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
  rw [Subgroup.mem_strictPeriods_iff]
  refine ⟨ModularGroup.T, ?_, ?_⟩
  · change ModularGroup.T ∈ Gamma0 N
    rw [Gamma0_mem]
    simp [ModularGroup.T]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      (change ((ModularGroup.T : Matrix (Fin 2) (Fin 2) ℤ) _ _ : ℝ) = _
       simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom])

variable (p : ℕ) [NeZero p]

theorem slash_classicalUpper_apply (f : ℍ → ℂ) (j : ℤ) (τ : ℍ) :
    (f ∣[k] toReal (classicalUpper p j)) τ =
      (p : ℂ)⁻¹ * f (toReal (classicalUpper p j) • τ) := by
  have hdet := det_toReal_classicalUpper p j
  have hpos : 0 < (toReal (classicalUpper p j)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [slash_apply, σ_of_det_pos hpos, hdet]
  have hden : denom (toReal (classicalUpper p j)) τ = p := by
    simp [denom, toReal_apply, coe_classicalUpper]
  rw [hden]
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  simp only [abs_of_pos (natCast_pos_real p)]
  push_cast
  rw [_root_.zpow_neg, zpow_sub_one₀ hp]
  field_simp

theorem coe_classicalUpper_smul (j : ℤ) (τ : ℍ) :
    ((toReal (classicalUpper p j) • τ : ℍ) : ℂ) = (τ + j) / p := by
  have hdet := det_toReal_classicalUpper p j
  have hpos : 0 < (toReal (classicalUpper p j)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
  simp [num, denom, toReal_apply, coe_classicalUpper]

theorem slash_heckeAlpha_apply (f : ℍ → ℂ) (τ : ℍ) :
    (f ∣[k] toReal (heckeAlpha p)) τ = (p : ℂ) ^ (k - 1) * f (toReal (heckeAlpha p) • τ) := by
  have hdet := det_toReal_heckeAlpha p
  have hpos : 0 < (toReal (heckeAlpha p)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [slash_apply, σ_of_det_pos hpos, hdet]
  have hden : denom (toReal (heckeAlpha p)) τ = 1 := by
    simp [denom, toReal_apply, heckeAlpha, coe_upperHecke]
  rw [hden, _root_.one_zpow, mul_one]
  simp only [abs_of_pos (natCast_pos_real p)]
  push_cast
  ring

theorem coe_heckeAlpha_smul (τ : ℍ) : ((toReal (heckeAlpha p) • τ : ℍ) : ℂ) = p * τ := by
  have hdet := det_toReal_heckeAlpha p
  have hpos : 0 < (toReal (heckeAlpha p)).det.val := by rw [hdet]; exact natCast_pos_real p
  rw [UpperHalfPlane.coe_smul_of_det_pos hpos]
  simp [num, denom, toReal_apply, heckeAlpha, coe_upperHecke]

theorem sum_exp_mul_div (m : ℕ) :
    ∑ j : Fin p, Complex.exp (2 * π * I * ((j : ℕ) * m : ℂ) / p) = if p ∣ m then (p : ℂ) else 0 := by
  have hp : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
  set ζ : ℂ := Complex.exp (2 * π * I / p)
  have hζ : IsPrimitiveRoot ζ p := Complex.isPrimitiveRoot_exp p (NeZero.ne p)
  have e : ∀ j : ℕ, Complex.exp (2 * π * I * ((j : ℂ) * m) / p) = (ζ ^ m) ^ j := by
    intro j
    rw [← pow_mul, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [e]
  rw [Fin.sum_univ_eq_sum_range (fun j => (ζ ^ m) ^ j) p]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd m).2 h]
    simp
  · have h1 : ζ ^ m ≠ 1 := fun h' => h ((hζ.pow_eq_one_iff_dvd m).1 h')
    rw [geom_sum_eq h1, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self, zero_div]

local notation "𝕢₁" => Function.Periodic.qParam 1

theorem qParam_one_pow_smul_classicalUpper (j : ℕ) (τ : ℍ) (m : ℕ) :
    𝕢₁ ((toReal (classicalUpper p (j : ℤ)) • τ : ℍ) : ℂ) ^ m =
      Complex.exp (2 * π * I * (τ : ℂ) * m / p) * Complex.exp (2 * π * I * ((j : ℂ) * m) / p) := by
  rw [coe_classicalUpper_smul, Function.Periodic.qParam, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem qParam_one_pow_smul_heckeAlpha (τ : ℍ) (m : ℕ) :
    𝕢₁ ((toReal (heckeAlpha p) • τ : ℍ) : ℂ) ^ m = 𝕢₁ (τ : ℂ) ^ (m * p) := by
  rw [coe_heckeAlpha_smul, Function.Periodic.qParam, Function.Periodic.qParam, ← Complex.exp_nat_mul,
    ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def heckeCoeff (N p : ℕ) (k : ℤ) (a : ℕ → ℂ) (n : ℕ) : ℂ :=
  a (n * p) + if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0

variable [Fact p.Prime]

theorem hasSum_heckeCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    HasSum (fun n => heckeCoeff N p k (fun m => (qExpansion 1 f).coeff m) n * 𝕢₁ (τ : ℂ) ^ n)
      (heckeCusp N p k f τ) := by
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m
  have hf : ∀ z : ℍ, HasSum (fun m => a m * 𝕢₁ (z : ℂ) ^ m) (f z) := fun z =>
    ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_Gamma0 z
  have hpinj : Function.Injective fun n : ℕ => n * p := fun x y h =>
    Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (NeZero.ne p)) h

  have hU : HasSum (fun n => a (n * p) * 𝕢₁ (τ : ℂ) ^ n)
      (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) := by
    have h1 : HasSum (fun m => ∑ j : Fin p, (p : ℂ)⁻¹ *
        (a m * 𝕢₁ ((toReal (classicalUpper p ((j : ℕ) : ℤ)) • τ : ℍ) : ℂ) ^ m))
        (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) := by
      refine hasSum_sum fun j _ => ?_
      rw [slash_classicalUpper_apply]
      exact (hf _).mul_left _
    have h2 : (fun m => ∑ j : Fin p, (p : ℂ)⁻¹ *
        (a m * 𝕢₁ ((toReal (classicalUpper p ((j : ℕ) : ℤ)) • τ : ℍ) : ℂ) ^ m)) =
        fun m => if p ∣ m then a m * Complex.exp (2 * π * I * (τ : ℂ) * m / p) else 0 := by
      funext m
      simp_rw [qParam_one_pow_smul_classicalUpper]
      have : ∀ j : Fin p, (p : ℂ)⁻¹ * (a m * (Complex.exp (2 * π * I * (τ : ℂ) * m / p) *
          Complex.exp (2 * π * I * (((j : ℕ) : ℂ) * m) / p))) =
          ((p : ℂ)⁻¹ * a m * Complex.exp (2 * π * I * (τ : ℂ) * m / p)) *
            Complex.exp (2 * π * I * (((j : ℕ) : ℂ) * m) / p) := fun j => by ring
      simp_rw [this]
      rw [← Finset.mul_sum, sum_exp_mul_div]
      have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
      split_ifs
      · field_simp
      · simp
    rw [h2] at h1
    rw [← hpinj.hasSum_iff (fun m hm => by
      rw [if_neg]
      rintro ⟨c, rfl⟩
      exact hm ⟨c, mul_comm c p⟩)] at h1
    convert h1 using 1
    funext n
    simp only [Function.comp_apply, dvd_mul_left, if_true]
    congr 1
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne p)
    push_cast
    field_simp

  have hL : HasSum (fun n => (if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) *
      𝕢₁ (τ : ℂ) ^ n) ((if p ∣ N then 0 else (f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
    split_ifs with hpN
    · simp
    · have h1 : HasSum (fun m => (p : ℂ) ^ (k - 1) * (a m * 𝕢₁ (τ : ℂ) ^ (m * p)))
          (((f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
        rw [slash_heckeAlpha_apply]
        have := (hf (toReal (heckeAlpha p) • τ)).mul_left ((p : ℂ) ^ (k - 1))
        simpa only [qParam_one_pow_smul_heckeAlpha] using this
      rw [← hpinj.hasSum_iff (f := fun n => (if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) *
          𝕢₁ (τ : ℂ) ^ n) (fun m hm => by
        rw [if_neg, zero_mul]
        rintro ⟨c, rfl⟩
        exact hm ⟨c, mul_comm c p⟩)]
      convert h1 using 1
      funext m
      simp only [Function.comp_apply, dvd_mul_left, if_true,
        Nat.mul_div_cancel _ (Nat.pos_of_ne_zero (NeZero.ne p))]
      ring
  have e1 : (fun n => heckeCoeff N p k a n * 𝕢₁ (τ : ℂ) ^ n) = fun n => a (n * p) * 𝕢₁ (τ : ℂ) ^ n +
      (if p ∣ N then 0 else if p ∣ n then (p : ℂ) ^ (k - 1) * a (n / p) else 0) * 𝕢₁ (τ : ℂ) ^ n := by
    funext n
    simp only [heckeCoeff]
    ring
  have e2 : heckeCusp N p k f τ = (∑ j : Fin p, ((f : ℍ → ℂ) ∣[k] toReal (classicalUpper p ((j : ℕ) : ℤ))) τ) +
      ((if p ∣ N then 0 else (f : ℍ → ℂ) ∣[k] toReal (heckeAlpha p)) τ) := by
    rw [coe_heckeCusp]
    unfold heckeOp
    rw [Pi.add_apply, Finset.sum_apply]
  rw [e1, e2]
  exact hU.add hL

theorem qExpansion_coeff_heckeCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (n : ℕ) :
    (qExpansion 1 (heckeCusp N p k f)).coeff n =
      heckeCoeff N p k (fun m => (qExpansion 1 f).coeff m) n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0
    (f := heckeCusp N p k f) (fun τ => by simpa only [smul_eq_mul] using hasSum_heckeCusp p f τ) n).symm

theorem qExpansion_coeff_eq_of_hasSum (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {b : ℕ → ℂ}
    (hb : ∀ τ : ℍ, HasSum (fun n => b n * 𝕢₁ (τ : ℂ) ^ n) (f τ)) (n : ℕ) :
    (qExpansion 1 f).coeff n = b n :=
  (ModularFormClass.qExpansion_coeff_unique one_pos one_mem_strictPeriods_Gamma0 (f := f)
    (fun τ => by simpa only [smul_eq_mul] using hb τ) n).symm

theorem hasSum_qExpansion_cusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (τ : ℍ) :
    HasSum (fun n => (qExpansion 1 f).coeff n * 𝕢₁ (τ : ℂ) ^ n) (f τ) :=
  ModularForm.hasSum_qExpansion f one_pos one_mem_strictPeriods_Gamma0 τ

theorem qExpansion_coeff_sub_smul (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (c : ℂ) (n : ℕ) :
    (qExpansion 1 (⇑(g - c • f) : ℍ → ℂ)).coeff n = (qExpansion 1 g).coeff n - c * (qExpansion 1 f).coeff n := by
  refine qExpansion_coeff_eq_of_hasSum (g - c • f)
    (b := fun m => (qExpansion 1 g).coeff m - c * (qExpansion 1 f).coeff m) (fun τ => ?_) n
  have := (hasSum_qExpansion_cusp g τ).sub ((hasSum_qExpansion_cusp f τ).mul_left c)
  have e1 : (fun m => ((qExpansion 1 g).coeff m - c * (qExpansion 1 f).coeff m) * 𝕢₁ (τ : ℂ) ^ m) =
      fun m => (qExpansion 1 g).coeff m * 𝕢₁ (τ : ℂ) ^ m - c * ((qExpansion 1 f).coeff m * 𝕢₁ (τ : ℂ) ^ m) := by
    funext m
    ring
  have e2 : (g - c • f) τ = g τ - c * f τ := rfl
  rw [e1, e2]
  exact this

theorem eq_zero_of_qExpansion_coeff (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (h : ∀ n, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  ext τ
  have := hasSum_qExpansion_cusp f τ
  simp only [h, zero_mul] at this
  rw [this.unique hasSum_zero]
  rfl

theorem eq_zero_of_eigen_of_coeff_one (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (ev : ℕ → ℂ)
    (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (h1 : (qExpansion 1 f).coeff 1 = 0) : f = 0 := by
  refine eq_zero_of_qExpansion_coeff f fun n => ?_
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · exact CuspFormClass.qExpansion_coeff_zero f one_pos one_mem_strictPeriods_Gamma0
      · exact h1
    · set p := n.minFac
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have : Fact p.Prime := ⟨hp⟩
      have : NeZero p := ⟨hp.ne_zero⟩
      set m := n / p
      have hnm : n = m * p := (Nat.div_mul_cancel (Nat.minFac_dvd n)).symm
      have hm : m < n := Nat.div_lt_self (by omega) hp.one_lt
      have hmp : m / p < n := lt_of_le_of_lt (Nat.div_le_self m p) hm
      have key := qExpansion_coeff_heckeCusp p f m
      rw [hf p] at key
      have hsm : (qExpansion 1 (⇑(ev p • f) : ℍ → ℂ)).coeff m = ev p * (qExpansion 1 f).coeff m := by
        refine qExpansion_coeff_eq_of_hasSum (ev p • f) (b := fun j => ev p * (qExpansion 1 f).coeff j)
          (fun τ => ?_) m
        have := (hasSum_qExpansion_cusp f τ).mul_left (ev p)
        have e1 : (fun j => ev p * (qExpansion 1 f).coeff j * 𝕢₁ (τ : ℂ) ^ j) =
            fun j => ev p * ((qExpansion 1 f).coeff j * 𝕢₁ (τ : ℂ) ^ j) := by
          funext j
          ring
        have e2 : (ev p • f) τ = ev p * f τ := rfl
        rw [e1, e2]
        exact this
      rw [hsm, ih m hm, mul_zero] at key
      unfold heckeCoeff at key
      simp only at key
      rw [ih (m / p) hmp] at key
      simp only [mul_zero, ite_self, add_zero] at key
      rw [hnm]
      exact key.symm

theorem eq_smul_of_eigen (f g : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (ev : ℕ → ℂ)
    (hf : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k f = ev p • f)
    (hg : ∀ (p : ℕ) [Fact p.Prime], heckeCusp N p k g = ev p • g)
    (hf1 : (qExpansion 1 f).coeff 1 = 1) : g = (qExpansion 1 g).coeff 1 • f := by
  set c := (qExpansion 1 g).coeff 1
  have h := eq_zero_of_eigen_of_coeff_one (g - c • f) ev (fun p _ => by
    rw [map_sub, map_smul, hf p, hg p, smul_sub, smul_comm])
    (by rw [qExpansion_coeff_sub_smul, hf1, mul_one, sub_self])
  exact sub_eq_zero.1 h

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

local notation "𝕢₁" => Function.Periodic.qParam 1

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem norm_qParam_one (τ : ℍ) : ‖𝕢₁ (τ : ℂ)‖ = Real.exp (-2 * π * τ.im) := by
  rw [Function.Periodic.norm_qParam]
  simp

theorem exists_norm_le_exp_of_coeff_eq_zero (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) (B : ℕ)
    (hB : ∀ n ≤ B, (qExpansion 1 f).coeff n = 0) :
    ∃ C, ∀ τ : ℍ, 1 ≤ τ.im → ‖f τ‖ ≤ C * Real.exp (-2 * π * (B + 1) * τ.im) := by
  set a : ℕ → ℂ := fun m => (qExpansion 1 f).coeff m
  set τ₀ : ℍ := ⟨I / 2, by simp⟩
  have h0 := hasSum_qExpansion_cusp f τ₀
  obtain ⟨M0, hM0⟩ := (h0.summable.tendsto_atTop_zero.norm).bddAbove_range
  have hq0 : ‖𝕢₁ (τ₀ : ℂ)‖ = Real.exp (-π) := by
    rw [norm_qParam_one]
    congr 1
    simp [τ₀, UpperHalfPlane.im]
    ring
  have ha : ∀ m : ℕ, ‖a m‖ ≤ M0 * Real.exp (π * m) := by
    intro m
    have hm := hM0 ⟨m, rfl⟩
    simp only at hm
    rw [norm_mul, norm_pow, hq0, ← Real.exp_nat_mul] at hm
    have e : ‖a m‖ = ‖a m‖ * Real.exp (m * -π) * Real.exp (π * m) := by
      rw [mul_assoc, ← Real.exp_add]
      ring_nf
      simp
    rw [e]
    exact mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
  refine ⟨M0 * Real.exp (π * (B + 1)) * (1 - Real.exp (-π))⁻¹, fun τ hτ => ?_⟩
  have hs := hasSum_qExpansion_cusp f τ
  rw [← hasSum_nat_add_iff' (B + 1)] at hs
  have hzero : ∑ i ∈ Finset.range (B + 1), a i * 𝕢₁ (τ : ℂ) ^ i = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [Finset.mem_range] at hi
      simp only [a]
      rw [hB i (by omega), zero_mul]
  rw [hzero, sub_zero] at hs
  set r := ‖𝕢₁ (τ : ℂ)‖ with hrdef
  have hr : r = Real.exp (-2 * π * τ.im) := norm_qParam_one τ
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r ≤ Real.exp (-2 * π) := by
    rw [hr]
    exact Real.exp_le_exp.2 (by nlinarith [Real.pi_pos])
  have hg : HasSum (fun m : ℕ => M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * Real.exp (-π) ^ m)
      (M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * (1 - Real.exp (-π))⁻¹) :=
    (hasSum_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.2 (by linarith [Real.pi_pos]))).mul_left _
  have hle := hs.norm_le_of_bounded hg (fun m => by
    rw [norm_mul, norm_pow, ← hrdef, pow_add]
    have h1 : r ^ m ≤ Real.exp (-2 * π) ^ m := pow_le_pow_left₀ hr0 hr1 m
    have h2 := ha (m + (B + 1))
    have e1 : Real.exp (-2 * π) ^ m * Real.exp (π * ((m + (B + 1) : ℕ) : ℝ)) =
        Real.exp (π * (B + 1)) * Real.exp (-π) ^ m := by
      rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      push_cast
      ring
    have hM0' : 0 ≤ M0 := le_trans (norm_nonneg _) (hM0 ⟨0, rfl⟩)
    calc ‖a (m + (B + 1))‖ * (r ^ m * r ^ (B + 1))
        ≤ (M0 * Real.exp (π * ((m + (B + 1) : ℕ) : ℝ))) * (Real.exp (-2 * π) ^ m * r ^ (B + 1)) := by
          gcongr
      _ = M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * Real.exp (-π) ^ m := by
          linear_combination (M0 * r ^ (B + 1)) * e1)
  calc ‖f τ‖ ≤ M0 * Real.exp (π * (B + 1)) * r ^ (B + 1) * (1 - Real.exp (-π))⁻¹ := hle
    _ = M0 * Real.exp (π * (B + 1)) * (1 - Real.exp (-π))⁻¹ * Real.exp (-2 * π * (B + 1) * τ.im) := by
      rw [hr, ← Real.exp_nat_mul]
      push_cast
      ring_nf

variable (N k) in

def sturmBoundGamma0 : ℕ :=
  (k * Nat.card (𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ)).toNat / 12

theorem isBoundedAtImInfty_quotientFunc (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (q : 𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ) :
    IsBoundedAtImInfty (SlashInvariantForm.quotientFunc f q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    obtain ⟨σ, hσ⟩ := h.2
    rw [SlashInvariantForm.quotientFunc_mk]
    have e : ((h : GL (Fin 2) ℝ))⁻¹ = toReal (Matrix.SpecialLinearGroup.mapGL ℚ σ⁻¹) := by
      rw [toReal_mapGL, map_inv, hσ]
    rw [e]
    exact isBoundedAtImInfty_slash_toReal (CuspForm.toModularFormₗ f) _

theorem eq_zero_of_coeff_le_sturmBound (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (hB : ∀ n ≤ sturmBoundGamma0 N k, (qExpansion 1 f).coeff n = 0) : f = 0 := by
  classical
  set B := sturmBoundGamma0 N k
  obtain ⟨C, hC⟩ := exists_norm_le_exp_of_coeff_eq_zero f B hB
  set Q := 𝒮ℒ ⧸ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)).subgroupOf 𝒮ℒ
  set F := ModularForm.norm 𝒮ℒ f
  let : Fintype Q := Fintype.ofFinite Q
  set q₀ : Q := ⟦1⟧

  have hR : IsBoundedAtImInfty (∏ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q) := by
    rw [IsBoundedAtImInfty, BoundedAtFilter,
      show (1 : ℍ → ℝ) = (fun _ => ∏ _q ∈ Finset.univ.erase q₀, (1 : ℝ)) by ext; simp, Finset.prod_fn]
    exact Asymptotics.IsBigO.finsetProd fun q _ => isBoundedAtImInfty_quotientFunc f q
  obtain ⟨M, A, hMA⟩ := isBoundedAtImInfty_iff.1 hR
  have hF : ∀ τ : ℍ, F τ = f τ * (∏ q ∈ Finset.univ.erase q₀, SlashInvariantForm.quotientFunc f q) τ := by
    intro τ
    rw [ModularForm.coe_norm, ← Finset.mul_prod_erase _ _ (Finset.mem_univ q₀), Pi.mul_apply,
      SlashInvariantForm.quotientFunc_mk, OneMemClass.coe_one, inv_one, SlashAction.slash_one]
  have hcoeff : ∀ n ≤ B, (qExpansion 1 F).coeff n = 0 := by
    intro n hn
    by_contra hne
    have hpos : 0 < ‖(qExpansion 1 F).coeff n‖ := norm_pos_iff.2 hne
    set K := |C| * |M| + 1

    have hbound : ∀ t : ℝ, max 1 A ≤ t → ‖(qExpansion 1 F).coeff n‖ ≤ K * Real.exp (-2 * π * t) := by
      intro t ht
      have ht1 : 1 ≤ t := le_trans (le_max_left _ _) ht
      have htA : A ≤ t := le_trans (le_max_right _ _) ht
      have ht0 : 0 < t := by linarith
      rw [ModularFormClass.qExpansion_coeff_eq_intervalIntegral (f := F) one_pos one_mem_strictPeriods_SL n ht0]
      simp only [Complex.ofReal_one, div_one, one_mul]
      refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := K * Real.exp (-2 * π * t))
        fun u _ => ?_).trans (by simp)
      set τ : ℍ := ⟨u + t * I, by simpa using ht0⟩
      have him : τ.im = t := by simp [τ, UpperHalfPlane.im]
      have h1 := hC τ (by rw [him]; exact ht1)
      have h2 := hMA τ (by rw [him]; exact htA)
      have hq : ‖1 / 𝕢₁ ((u : ℂ) + t * I) ^ n‖ = Real.exp (2 * π * n * t) := by
        rw [norm_div, norm_one, norm_pow, Function.Periodic.norm_qParam, ← Real.exp_nat_mul, one_div,
          ← Real.exp_neg]
        congr 1
        simp
        ring
      change ‖1 / 𝕢₁ ((u : ℂ) + t * I) ^ n * F τ‖ ≤ _
      rw [norm_mul, hq, hF τ, norm_mul, him] at *
      rw [him] at h1
      have hnB : (n : ℝ) ≤ B := by exact_mod_cast hn
      calc Real.exp (2 * π * n * t) * (‖f τ‖ * ‖(∏ q ∈ Finset.univ.erase q₀,
              SlashInvariantForm.quotientFunc f q) τ‖)
          ≤ Real.exp (2 * π * n * t) * ((|C| * Real.exp (-2 * π * (B + 1) * t)) * |M|) := by
            gcongr
            · exact h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (Real.exp_pos _).le)
            · exact h2.trans (le_abs_self M)
        _ = |C| * |M| * (Real.exp (2 * π * n * t) * Real.exp (-2 * π * (B + 1) * t)) := by ring
        _ ≤ |C| * |M| * Real.exp (-2 * π * t) := by
            gcongr
            rw [← Real.exp_add]
            refine Real.exp_le_exp.2 ?_
            have key : 2 * π * n * t + -2 * π * (B + 1) * t = -2 * π * t + 2 * π * t * (n - B) := by ring
            rw [key]
            have : 2 * π * t * ((n : ℝ) - B) ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
            linarith
        _ ≤ K * Real.exp (-2 * π * t) := by
            gcongr
            linarith

    have htend : Tendsto (fun t : ℝ => K * Real.exp (-2 * π * t)) atTop (nhds 0) := by
      have : Tendsto (fun t : ℝ => -2 * π * t) atTop atBot :=
        tendsto_id.const_mul_atTop_of_neg (by linarith [Real.pi_pos])
      simpa using (Real.tendsto_exp_atBot.comp this).const_mul K
    obtain ⟨t, ht⟩ := ((htend.eventually (gt_mem_nhds hpos)).and (eventually_ge_atTop (max 1 A))).exists
    exact absurd (hbound t ht.2) (not_le.2 ht.1)
  have hFo : ((B : ℕ) : ℕ∞) < (qExpansion 1 F).order := by
    refine lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self B) (PowerSeries.nat_le_order _ (B + 1) ?_)
    intro i hi
    exact hcoeff i (by omega)
  have hF0 : F = 0 := ModularForm.sturm_bound_levelOne hFo
  have := (ModularForm.norm_eq_zero_iff 𝒮ℒ f).1 hF0
  exact DFunLike.coe_injective (by rw [this]; rfl)

def firstCoeffs (B : ℕ) : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k →ₗ[ℂ] (Fin (B + 1) → ℂ) where
  toFun f i := (qExpansion 1 f).coeff i
  map_add' f g := by
    funext i
    refine qExpansion_coeff_eq_of_hasSum (f + g)
      (b := fun m => (qExpansion 1 f).coeff m + (qExpansion 1 g).coeff m) (fun τ => ?_) i
    have := (hasSum_qExpansion_cusp f τ).add (hasSum_qExpansion_cusp g τ)
    simp only [← add_mul] at this
    exact this
  map_smul' c f := by
    funext i
    refine qExpansion_coeff_eq_of_hasSum (c • f)
      (b := fun m => c * (qExpansion 1 f).coeff m) (fun τ => ?_) i
    have := (hasSum_qExpansion_cusp f τ).mul_left c
    simp only [← mul_assoc] at this
    exact this

instance finiteDimensional_cuspForm : FiniteDimensional ℂ (CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) := by
  refine Module.Finite.of_injective (firstCoeffs (N := N) (k := k) (sturmBoundGamma0 N k)) ?_
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro f hf
  refine eq_zero_of_coeff_le_sturmBound f fun n hn => ?_
  have := congrFun hf ⟨n, by omega⟩
  exact this

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open scoped InnerProductSpace

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module ℂ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

section

variable (ρ : Representation ℂ G E) (ι : E →ₗ[ℂ] H) (T : Submodule ℂ E)

def orbitSum (K : Subgroup G) (v : E) (hv : (Set.range fun k : K => ρ k v).Finite) : E :=
  ∑ w ∈ hv.toFinset, w

variable {ρ}

theorem orbitSum_mem {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    {Y : Submodule ℂ E} (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hvY : v ∈ Y) : orbitSum ρ K v hv ∈ Y := by
  refine Submodule.sum_mem _ fun w hw => ?_
  rw [Set.Finite.mem_toFinset] at hw
  obtain ⟨k, rfl⟩ := hw
  exact hY _ _ hvY

theorem orbitSum_fixed {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite)
    (k : K) : ρ k (orbitSum ρ K v hv) = orbitSum ρ K v hv := by
  unfold orbitSum
  rw [map_sum]
  refine Finset.sum_nbij' (fun w => ρ k w) (fun w => ρ (k⁻¹ : K) w) ?_ ?_ ?_ ?_ (fun _ _ => rfl)
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k * k', by show ρ ((k * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w hw
    simp only [Set.Finite.mem_toFinset] at hw ⊢
    obtain ⟨k', rfl⟩ := hw
    exact ⟨k⁻¹ * k', by show ρ ((k⁻¹ * k' : K) : G) v = _; rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]⟩
  · intro w _
    change ρ ((k⁻¹ : K) : G) (ρ k w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply]
  · intro w _
    change ρ (k : G) (ρ ((k⁻¹ : K) : G) w) = w
    rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one, Module.End.one_apply]

theorem card_orbit_pos {K : Subgroup G} {v : E} (hv : (Set.range fun k : K => ρ k v).Finite) :
    0 < hv.toFinset.card :=
  Finset.card_pos.2 ⟨v, by rw [Set.Finite.mem_toFinset]; exact ⟨1, by simp⟩⟩

end

variable {ρ : Representation ℂ G E} {ι : E →ₗ[ℂ] H} {T : Submodule ℂ E} {φ : E}

theorem mem_of_stable_of_eigen
    (hT : T = Submodule.span ℂ (Set.range fun g : G => ρ g φ))
    (hinj : ∀ v ∈ T, ι v = 0 → v = 0)
    (hunit : ∀ g : G, ∀ v ∈ T, ∀ w ∈ T, ⟪ι (ρ g v), ι (ρ g w)⟫_ℂ = ⟪ι v, ι w⟫_ℂ)
    (K : Subgroup G) (hφK : ∀ k : K, ρ k φ = φ)
    (horb : ∀ v ∈ T, (Set.range fun k : K => ρ k v).Finite)
    (hfd : FiniteDimensional ℂ ↥(T ⊓ Representation.invariants (ρ.comp K.subtype)))
    {J : Type*} (S : J → Finset G) (ev : J → ℂ) (hφS : ∀ j, ∑ g ∈ S j, ρ g φ = ev j • φ)
    (hP : ∀ z ∈ T, (∀ k : K, ρ k z = z) → (∀ j, ∑ g ∈ S j, ρ g z = ev j • z) → ∃ c : ℂ, z = c • φ)
    (Y : Submodule ℂ E) (hYT : Y ≤ T) (hY : ∀ g, ∀ y ∈ Y, ρ g y ∈ Y) (hY0 : Y ≠ ⊥) : φ ∈ Y := by
  have hφT : φ ∈ T := by rw [hT]; exact Submodule.subset_span ⟨1, by simp⟩
  have hTg : ∀ g, ∀ v ∈ T, ρ g v ∈ T := by
    intro g v hv
    rw [hT] at hv ⊢
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h, rfl⟩ := hx
      exact Submodule.subset_span ⟨g * h, by show ρ (g * h) φ = _; rw [map_mul, Module.End.mul_apply]⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

  have hadj : ∀ g, ∀ v ∈ T, ∀ w ∈ T, ⟪ι v, ι (ρ g w)⟫_ℂ = ⟪ι (ρ g⁻¹ v), ι w⟫_ℂ := by
    intro g v hv w hw
    rw [← hunit g⁻¹ v hv _ (hTg g w hw), ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      Module.End.one_apply]

  have havg : ∀ z ∈ T, (∀ k : K, ρ k z = z) → ∀ v (hv : v ∈ T),
      ⟪ι z, ι (orbitSum ρ K v (horb v hv))⟫_ℂ = ((horb v hv).toFinset.card : ℂ) * ⟪ι z, ι v⟫_ℂ := by
    intro z hz hzK v hv
    unfold orbitSum
    rw [map_sum, inner_sum, ← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun w hw => ?_
    rw [Set.Finite.mem_toFinset] at hw
    obtain ⟨k, rfl⟩ := hw
    rw [hadj _ z hz v hv, ← Subgroup.coe_inv, hzK k⁻¹]

  obtain ⟨y, hyY, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  have hyT := hYT hyY
  obtain ⟨g, hg⟩ : ∃ g : G, ⟪ι φ, ι (ρ g y)⟫_ℂ ≠ 0 := by
    by_contra! hall
    have horth : ∀ t ∈ T, ⟪ι t, ι y⟫_ℂ = 0 := by
      intro t ht
      rw [hT] at ht
      induction ht using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨h, rfl⟩ := hx
        have := hall h⁻¹
        rw [hadj _ φ hφT y hyT, inv_inv] at this
        exact this
      | zero => rw [map_zero, inner_zero_left]
      | add x x' _ _ hx hx' => rw [map_add, inner_add_left, hx, hx', add_zero]
      | smul c x _ hx => rw [map_smul, inner_smul_left, hx, mul_zero]
    exact hy0 (hinj y hyT (inner_self_eq_zero.1 (horth y hyT)))
  set y' := ρ g y
  have hy'Y : y' ∈ Y := hY g y hyY
  have hy'T : y' ∈ T := hYT hy'Y
  set s := orbitSum ρ K y' (horb y' hy'T)
  have hsY : s ∈ Y := orbitSum_mem _ hY hy'Y
  have hsK : ∀ k : K, ρ k s = s := orbitSum_fixed _
  have hφs : ⟪ι φ, ι s⟫_ℂ ≠ 0 := by
    rw [havg φ hφT hφK y' hy'T]
    exact mul_ne_zero (Nat.cast_ne_zero.2 (card_orbit_pos _).ne') hg

  set M : Submodule ℂ E := Y ⊓ (T ⊓ Representation.invariants (ρ.comp K.subtype))
  have hMfd : FiniteDimensional ℂ M :=
    Submodule.finiteDimensional_of_le (inf_le_right : M ≤ T ⊓ Representation.invariants (ρ.comp K.subtype))
  set Mι : Submodule ℂ H := M.map ι
  have hMιfd : FiniteDimensional ℂ Mι := inferInstance
  haveI : CompleteSpace Mι := FiniteDimensional.complete ℂ Mι
  obtain ⟨u, huM, w, hw, hφw⟩ := Mι.exists_add_mem_mem_orthogonal (ι φ)
  obtain ⟨m, hmM, hmP⟩ := Submodule.mem_map.1 huM
  have hmY : m ∈ Y := hmM.1
  have hmT : m ∈ T := hmM.2.1
  have hmK : ∀ k : K, ρ k m = m := fun k => hmM.2.2 k
  set z := φ - m
  have hzT : z ∈ T := sub_mem hφT hmT
  have hzK : ∀ k : K, ρ k z = z := fun k => by rw [map_sub, hφK, hmK]
  have hzι : ι z ∈ Mιᗮ := by
    rw [map_sub, hmP, hφw, add_sub_cancel_left]
    exact hw

  have hzY : ∀ v ∈ Y, ⟪ι z, ι v⟫_ℂ = 0 := by
    intro v hvY
    have hvT := hYT hvY
    have hsv : orbitSum ρ K v (horb v hvT) ∈ M :=
      ⟨orbitSum_mem _ hY hvY, orbitSum_mem _ hTg hvT, fun k => orbitSum_fixed _ k⟩
    have h0 : ⟪ι z, ι (orbitSum ρ K v (horb v hvT))⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hsv) hzι
    rw [havg z hzT hzK v hvT] at h0
    exact (mul_eq_zero.1 h0).resolve_left (Nat.cast_ne_zero.2 (card_orbit_pos _).ne')

  have hzE : ∀ j, ∑ g ∈ S j, ρ g z = ev j • z := by
    intro j
    set D := ∑ g ∈ S j, ρ g z - ev j • z
    have hDY : D ∈ Y := by
      have e : D = -(∑ g ∈ S j, ρ g m - ev j • m) := by
        simp only [D, z, map_sub, Finset.sum_sub_distrib, hφS, smul_sub]
        abel
      rw [e]
      exact neg_mem (sub_mem (Submodule.sum_mem _ fun g _ => hY g m hmY) (Submodule.smul_mem _ _ hmY))
    have hDT := hYT hDY
    have hDorth : ∀ v ∈ Y, ⟪ι D, ι v⟫_ℂ = 0 := by
      intro v hvY
      have hvT := hYT hvY
      simp only [D, map_sub, map_sum, map_smul, inner_sub_left, sum_inner, inner_smul_left, hzY v hvY,
        mul_zero, sub_zero]
      refine Finset.sum_eq_zero fun g _ => ?_
      rw [← hunit g⁻¹ _ (hTg g z hzT) v hvT, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
      exact hzY _ (hY _ _ hvY)
    have := hinj D hDT (inner_self_eq_zero.1 (hDorth D hDY))
    exact sub_eq_zero.1 this

  obtain ⟨c, hc⟩ := hP z hzT hzK hzE
  have hzs := hzY s hsY
  rw [hc, map_smul, inner_smul_left] at hzs
  have hc0 : c = 0 := by
    have := (mul_eq_zero.1 hzs).resolve_right hφs
    simpa using this
  have hz0 : z = 0 := by rw [hc, hc0, zero_smul]
  have : φ = m := sub_eq_zero.1 hz0
  rw [this]
  exact hmY

end GL2Classical

end

end GroundTheory.Automorphic
end

section
open NumberField Matrix CongruenceSubgroup ModularForm Complex Filter
open UpperHalfPlane hiding I I_re I_im
open scoped MatrixGroups ModularForm Real InnerProductSpace Manifold NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace GL2Classical

open AdelicGLn AutomorphicForm

set_option linter.unusedSectionVars false

variable {N : ℕ} [NeZero N] {k : ℤ}

theorem descend_archLift_mul_borelGL (f : ℍ → ℂ) {β : GL (Fin 2) ℝ} (hβ : 0 < β.det.val) (z : ℍ) :
    (Real.sqrt z.im : ℂ) ^ (-k) * archLift k f (β * borelGL z) =
      ((Real.sqrt β.det.val : ℂ) ^ k * (((β.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹) * (f ∣[k] β) z := by
  have hy := z.im_pos
  rw [archLift, map_mul, Units.val_mul, det_borelGL, mul_smul, borelGL_smul_I,
    denom_mul_of_det_pos _ (det_borelGL_pos z), borelGL_smul_I, denom_borelGL, mul_one,
    Real.sqrt_mul hβ.le, slash_apply, σ_of_det_pos hβ, abs_of_pos hβ]
  have hs : (Real.sqrt z.im : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hy).ne'
  have hd : ((β.det.val : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hβ.ne'
  have e1 : (Real.sqrt z.im : ℂ) ^ (-k) * (Real.sqrt z.im : ℂ) ^ k = 1 := by
    rw [← zpow_add₀ hs, neg_add_cancel, zpow_zero]
  have e2 : (((β.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹ * ((β.det.val : ℝ) : ℂ) ^ (k - 1) = 1 :=
    inv_mul_cancel₀ (zpow_ne_zero _ hd)
  push_cast
  rw [mul_zpow]
  set A := (Real.sqrt β.det.val : ℂ) ^ k * f (β • z) * denom β (z : ℂ) ^ (-k)
  linear_combination A * e1 - A * e2

theorem exists_eq_finiteDiagonal_mul_pos (g : FiniteAdelicGL ℚ 2) :
    ∃ ξ : GL (Fin 2) ℚ, ∃ u ∈ Gamma0Level N, 0 < (ξ.det.val : ℚ) ∧ g = finiteDiagonal ℚ 2 ξ * u := by
  obtain ⟨γ, u, hu, rfl⟩ := exists_eq_finiteDiagonal_mul N g
  by_cases hd : 0 < (γ.det.val : ℚ)
  · exact ⟨γ, u, hu, hd, rfl⟩
  · refine ⟨γ * epsilon, finiteDiagonal ℚ 2 epsilon * u, mul_mem (finiteDiagonal_epsilon_mem N) hu, ?_, ?_⟩
    · have hne : (γ.det.val : ℚ) ≠ 0 := γ.det.ne_zero
      have hneg : (γ.det.val : ℚ) < 0 := lt_of_le_of_ne (not_lt.1 hd) hne
      have he : (epsilon.det.val : ℚ) = -1 := by
        rw [Matrix.GeneralLinearGroup.val_det_apply]
        simp [epsilon, Matrix.det_fin_two_of]
      rw [map_mul, Units.val_mul, he]
      linarith
    · have hee : epsilon * epsilon = 1 := by
        conv_lhs => rw [← epsilon_inv]
        exact inv_mul_cancel _
      rw [map_mul, mul_assoc, ← mul_assoc (finiteDiagonal ℚ 2 epsilon), ← map_mul, hee, map_one, one_mul]

theorem descend_finRightRep_liftEquiv (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (g : FiniteAdelicGL ℚ 2) :
    ∃ δ : GL (Fin 2) ℚ, ∃ c : ℂ,
      descend k (finRightRep g (liftEquiv N k f : AdelicGL ℚ 2 → ℂ)) = c • ((f : ℍ → ℂ) ∣[k] toReal δ) := by
  have hf : ∀ γ ∈ (Gamma0 N : Subgroup (GL (Fin 2) ℝ)), (f : ℍ → ℂ) ∣[k] γ = f :=
    fun γ hγ => SlashInvariantForm.slash_action_eqn f γ hγ
  obtain ⟨ξ, u, hu, hξ, rfl⟩ := exists_eq_finiteDiagonal_mul_pos (N := N) g
  have hβ : 0 < ((toReal ξ)⁻¹).det.val := by
    have := det_toReal_inv_mul_pos ξ hξ (h := 1) (by simp)
    simpa using this
  refine ⟨ξ⁻¹, (Real.sqrt ((toReal ξ)⁻¹).det.val : ℂ) ^ k *
    ((((toReal ξ)⁻¹.det.val : ℝ) : ℂ) ^ (k - 1))⁻¹, ?_⟩
  funext z
  simp only [descend, finRightRep_apply, liftEquiv_apply, Pi.smul_apply, smul_eq_mul]
  rw [map_mul, ← mul_assoc, (isWeightLevel_adelicLift hf).right_level _ _ hu,
    realEmb_mul_finEmb_finiteDiagonal,
    adelicLift_apply hf ξ (det_toReal_inv_mul_pos ξ hξ (det_borelGL_pos z)) (one_mem _), map_inv]
  exact descend_archLift_mul_borelGL f hβ z

variable (k) in

def holoBddSpace : Submodule ℂ (ℍ → ℂ) where
  carrier := {F | MDiff F ∧ ∀ σ : SL(2, ℤ), IsBoundedAtImInfty (F ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)}
  add_mem' {F G} hF hG := ⟨hF.1.add hG.1, fun σ => by
    rw [SlashAction.add_slash]
    exact (hF.2 σ).add (hG.2 σ)⟩
  zero_mem' := ⟨mdifferentiable_const, fun σ => by
    rw [SlashAction.zero_slash]
    exact zero_form_isBoundedAtImInfty⟩
  smul_mem' c F hF := ⟨hF.1.const_smul c, fun σ => by
    have hpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ σ).det.val := by
      rw [Matrix.SpecialLinearGroup.det_mapGL]; exact one_pos
    rw [ModularForm.smul_slash, σ_of_det_pos hpos]
    exact (hF.2 σ).const_smul_left c⟩

theorem slash_toReal_mem_holoBddSpace (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (δ : GL (Fin 2) ℚ) : (f : ℍ → ℂ) ∣[k] toReal δ ∈ holoBddSpace k := by
  refine ⟨f.holo'.slash k _, fun σ => ?_⟩
  rw [← SlashAction.slash_mul, ← toReal_mapGL, ← map_mul]
  exact isBoundedAtImInfty_slash_toReal f _

theorem descend_mem_holoBddSpace (f : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ)) :
    descend k ψ ∈ holoBddSpace k := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    obtain ⟨δ, c, hc⟩ := descend_finRightRep_liftEquiv f.toSlashInvariantForm g
    rw [hc]
    exact Submodule.smul_mem _ c (slash_toReal_mem_holoBddSpace f δ)
  | zero =>
    have : descend k (0 : AdelicGL ℚ 2 → ℂ) = 0 := by funext z; simp [descend]
    rw [this]
    exact zero_mem _
  | add x y _ _ hx hy =>
    have : descend k (x + y) = descend k x + descend k y := by funext z; simp [descend, mul_add]
    rw [this]
    exact add_mem hx hy
  | smul c x _ hx =>
    have : descend k (c • x) = c • descend k x := by funext z; simp [descend]; ring
    rw [this]
    exact Submodule.smul_mem _ c hx

theorem isLeftInvariant_of_mem_translateSpan {φ : AdelicGL ℚ 2 → ℂ} (hφ : IsLeftInvariant φ)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan φ) : IsLeftInvariant ψ := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro γ x
    simp only [finRightRep_apply, mul_assoc]
    exact hφ γ _
  | zero => intro γ x; rfl
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

theorem right_kGL_of_mem_translateSpan {φ : AdelicGL ℚ 2 → ℂ}
    (hφ : ∀ g (w : ℂ) (hw : w ≠ 0), φ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * φ g)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan φ) :
    ∀ g (w : ℂ) (hw : w ≠ 0), ψ (g * realEmb (kGL w hw)) = (w / (‖w‖ : ℂ)) ^ (-k) * ψ g := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    intro g w hw
    simp only [finRightRep_apply]
    rw [mul_assoc, realEmb_mul_finEmb_comm, ← mul_assoc, hφ]
  | zero => intro g w hw; simp
  | add x y _ _ hx hy => intro g w hw; simp [hx g w hw, hy g w hw, mul_add]
  | smul c x _ hx => intro g w hw; simp [hx g w hw]; ring

theorem isWeightLevel_of_mem_translateSpan (f : SlashInvariantForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f : AdelicGL ℚ 2 → ℂ))
    (hK : ∀ u ∈ Gamma0Level N, finRightRep u ψ = ψ) : IsWeightLevel N k ψ :=
  ⟨isLeftInvariant_of_mem_translateSpan (liftEquiv N k f).2.isLeftInvariant hψ,
    fun g u hu => congrFun (hK u hu) g,
    right_kGL_of_mem_translateSpan (liftEquiv N k f).2.right_kGL hψ⟩

theorem exists_cuspForm_of_mem_translateSpan (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : AdelicGL ℚ 2 → ℂ} (hψ : ψ ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ))
    (hK : ∀ u ∈ Gamma0Level N, finRightRep u ψ = ψ) :
    ∃ F : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k,
      (liftEquiv N k F.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) = ψ := by
  have hW := isWeightLevel_of_mem_translateSpan f.toSlashInvariantForm hψ hK
  set Fs := (liftEquiv N k).symm ⟨ψ, hW⟩
  have hFs : (Fs : ℍ → ℂ) = descend k ψ := funext fun z => liftEquiv_symm_apply _ z
  have hmem : descend k ψ ∈ holoBddSpace k := descend_mem_holoBddSpace (CuspForm.toModularFormₗ f) hψ
  let Fm : ModularForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k :=
    { toSlashInvariantForm := Fs
      holo' := by
        change MDiff (Fs : ℍ → ℂ)
        rw [hFs]
        exact hmem.1
      bdd_at_cusps' := fun {c} hc => by
        rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z, isCusp_SL2Z_iff'] at hc
        obtain ⟨σ, rfl⟩ := hc
        rw [OnePoint.isBoundedAt_iff rfl]
        change IsBoundedAtImInfty ((Fs : ℍ → ℂ) ∣[k] Matrix.SpecialLinearGroup.mapGL ℝ σ)
        rw [hFs]
        exact hmem.2 σ }
  have hlift : liftEquiv N k Fm.toSlashInvariantForm = ⟨ψ, hW⟩ := (liftEquiv N k).apply_symm_apply _
  obtain ⟨F, hF⟩ := exists_cuspForm_of_liftEquiv_mem_cuspForms Fm (by
    rw [hlift]
    exact translateSpan_le_cuspForms f hψ)
  refine ⟨F, ?_⟩
  have : F.toSlashInvariantForm = Fm.toSlashInvariantForm := SlashInvariantForm.ext fun z => congrFun hF z
  rw [this, hlift]

theorem posIdele_fst_rat (r : ℝ) (hr : 0 < r) :
    ((Reduction.posIdele (K := ℚ) r hr : Global.IdeleGroup ℚ) : 𝔸[ℚ]).1 =
      Global.RationalIdeles.realEquiv.symm r := by
  apply Global.RationalIdeles.realEquiv.injective
  rw [RingEquiv.apply_symm_apply, Global.RationalIdeles.realEquiv_apply]
  have := Reduction.infiniteProj_posIdele (K := ℚ) r hr default
  rw [← Global.IdeleGroup.coe_infiniteProj, this]
  simp [Global.posRealToUnits, Global.posRealElem, Global.RationalIdeles.isReal_infinitePlace]
  exact RingEquiv.apply_symm_apply (InfinitePlace.Completion.ringEquivRealOfIsReal _) r

theorem exists_centralSection_eq_realEmb (s : {r : ℝ // 0 < r}) :
    ∃ (r : ℝ) (hr : 0 < r), Reduction.centralSection ℚ 2 s = realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne')) := by
  set t := Reduction.rpowHom ((2 * Module.finrank ℚ ℚ : ℝ))⁻¹ s
  refine ⟨t.1, t.2, ?_⟩
  have hc : Reduction.centralSection ℚ 2 s =
      Reduction.diagUnits 2 (fun _ => Reduction.posIdele (K := ℚ) t.1 t.2) := rfl
  rw [hc]
  apply (AdelicGLn.prodEquiv ℚ 2).injective
  rw [prodEquiv_realEmb]
  refine Prod.ext ?_ ?_
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [AdelicGLn.prodEquiv_apply_fst]
    simp only [Reduction.coe_diagUnits]
    change _ = Global.RationalIdeles.realEquiv.symm ((kGL (t.1 : ℂ) _ : Matrix (Fin 2) (Fin 2) ℝ) a b)
    rw [coe_kGL]
    fin_cases a <;> fin_cases b <;> simp [posIdele_fst_rat]
  · exact Reduction.prodEquiv_diagUnits_posIdele_snd (fun _ => t.1) (fun _ => t.2)

theorem apply_centralSection_mul {ψ : AdelicGL ℚ 2 → ℂ}
    (hψ : ∀ x (r : ℝ) (hr : 0 < r), ψ (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = ψ x)
    (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) : ψ (Reduction.centralSection ℚ 2 s * x) = ψ x := by
  obtain ⟨r, hr, hs⟩ := exists_centralSection_eq_realEmb s
  rw [Reduction.centralSection_mul_comm, hs, hψ _ _ hr]

def liftCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : cuspForms ℚ 2 :=
  ⟨(liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ), liftEquiv_mem_cuspForms f⟩

def translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) : Submodule ℂ (cuspForms ℚ 2) :=
  Submodule.span ℂ (Set.range fun g : FiniteAdelicGL ℚ 2 => finRepCusp ℚ 2 g (liftCusp f))

theorem coe_mem_translateSpan (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k) {ψ : cuspForms ℚ 2}
    (hψ : ψ ∈ translateSpanCusp f) :
    (ψ : AdelicGL ℚ 2 → ℂ) ∈ translateSpan (liftEquiv N k f.toSlashInvariantForm : AdelicGL ℚ 2 → ℂ) := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    exact Submodule.subset_span ⟨g, rfl⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul c x _ hx => exact Submodule.smul_mem _ c hx

theorem posScalar_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (x : AdelicGL ℚ 2) (r : ℝ) (hr : 0 < r) :
    (ψ : AdelicGL ℚ 2 → ℂ) (x * realEmb (kGL (r : ℂ) (by exact_mod_cast hr.ne'))) = (ψ : AdelicGL ℚ 2 → ℂ) x := by
  rw [right_kGL_of_mem_translateSpan (liftEquiv N k f.toSlashInvariantForm).2.right_kGL
    (coe_mem_translateSpan f hψ)]
  have hs' : (r : ℂ) / (‖(r : ℂ)‖ : ℂ) = 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr.le, div_self (by exact_mod_cast hr.ne')]
  rw [hs', _root_.one_zpow, one_mul]

theorem centralSection_of_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) (s : {r : ℝ // 0 < r}) (x : AdelicGL ℚ 2) :
    (ψ : AdelicGL ℚ 2 → ℂ) (Reduction.centralSection ℚ 2 s * x) = (ψ : AdelicGL ℚ 2 → ℂ) x :=
  apply_centralSection_mul (posScalar_of_mem_translateSpanCusp f hψ) s x

theorem finRepCusp_mem_translateSpanCusp (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) k)
    (g : FiniteAdelicGL ℚ 2) {ψ : cuspForms ℚ 2} (hψ : ψ ∈ translateSpanCusp f) :
    finRepCusp ℚ 2 g ψ ∈ translateSpanCusp f := by
  induction hψ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨h, rfl⟩ := hx
    exact Submodule.subset_span ⟨g * h, by
      show finRepCusp ℚ 2 (g * h) (liftCusp f) = _
      rw [map_mul, Module.End.mul_apply]⟩
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

end GL2Classical

end

end GroundTheory.Automorphic
end
