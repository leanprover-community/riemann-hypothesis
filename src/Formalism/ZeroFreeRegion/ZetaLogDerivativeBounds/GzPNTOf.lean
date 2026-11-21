import Formalism.ZeroFreeRegion.SmallHeightLogDeriv
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.IntegralEqIntervalIntegralAddCompl
import Formalism.ZeroFreeRegion.ZetaLogDerivativeBounds.NormIntegralComplLe

section
open Complex

noncomputable section

namespace Formalism.ZF

open ArithmeticFunction in
theorem zetaPrimeSum_nonneg_and_le (y : ℝ) (hy : 1 ≤ y) :
    0 ≤ Formalism.Sz y ∧ Formalism.Sz y ≤ y * y * Real.log y := by
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hterm : ∀ n ∈ Finset.Icc 1 ⌊y⌋₊, 0 ≤ ArithmeticFunction.vonMangoldt n * (y / n - 1) ∧
      ArithmeticFunction.vonMangoldt n * (y / n - 1) ≤ Real.log y * y := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn1' : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hnpos : (0 : ℝ) < n := by linarith
    have hny : (n : ℝ) ≤ y := (Nat.cast_le.mpr hn2).trans (Nat.floor_le hy0)
    have h1 : 0 ≤ y / n - 1 := by
      rw [sub_nonneg, le_div_iff₀ hnpos]
      linarith
    have h2 : y / n - 1 ≤ y := by
      have : y / n ≤ y := div_le_self hy0 hn1'
      linarith
    have hΛ : ArithmeticFunction.vonMangoldt n ≤ Real.log y :=
      ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnpos hny)
    exact ⟨mul_nonneg ArithmeticFunction.vonMangoldt_nonneg h1, mul_le_mul hΛ h2 h1 hlog⟩
  unfold Formalism.Sz
  refine ⟨Finset.sum_nonneg fun n hn => (hterm n hn).1, ?_⟩
  calc ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / n - 1)
        ≤ ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, Real.log y * y := Finset.sum_le_sum fun n hn => (hterm n hn).2
    _ = (⌊y⌋₊ : ℝ) * (Real.log y * y) := by simp
    _ ≤ y * (Real.log y * y) := mul_le_mul_of_nonneg_right (Nat.floor_le hy0) (mul_nonneg hlog hy0)
    _ = y * y * Real.log y := by ring

theorem abs_zetaPrimeSumError_le_of_one_le (y : ℝ) (hy : 1 ≤ y) :
    |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) := by
  obtain ⟨hS0, hS1⟩ := zetaPrimeSum_nonneg_and_le y hy
  have hy0 : (0 : ℝ) ≤ y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hγ1 := Real.one_half_lt_eulerMascheroniConstant
  have hγ2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hp1 : 0 ≤ y * Real.log y := mul_nonneg hy0 hlog
  have hp2 : 0 ≤ y * (y * Real.log y) := mul_nonneg hy0 hp1
  have hγy : Real.eulerMascheroniConstant * y ≤ y := by nlinarith
  have hγy0 : 0 ≤ Real.eulerMascheroniConstant * y := by nlinarith
  unfold Formalism.Gz
  rw [abs_le]
  constructor <;> nlinarith

end Formalism.ZF
end
end

section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

theorem norm_perronIntegrand (y : ℝ) (hy : 0 < y) (w : ℂ) :
    ‖Fy y w‖ = ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖) := by
  simp only [Fy, norm_div, norm_mul, norm_neg, Complex.norm_cpow_eq_rpow_re_of_pos hy]

theorem one_sub_div_log_le (c c' T v : ℝ) (hc : 0 < c) (hcc : c ≤ c') (hT : 0 ≤ T) (hv : |v| ≤ T) :
    1 - c' / Real.log (|v| + 2) ≤ 1 - c / Real.log (T + 2) := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hv0 : Real.log 2 ≤ Real.log (|v| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg v])
  have hvT : Real.log (|v| + 2) ≤ Real.log (T + 2) :=
    Real.log_le_log (by linarith [abs_nonneg v]) (by linarith)
  have hpos : 0 < Real.log (|v| + 2) := lt_of_lt_of_le h2 hv0
  have e1 : c / Real.log (T + 2) ≤ c / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_left hc.le hpos hvT
  have e2 : c / Real.log (|v| + 2) ≤ c' / Real.log (|v| + 2) :=
    div_le_div_of_nonneg_right hcc hpos.le
  linarith

theorem riemannZeta_ne_zero_of_mem_rectangle (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 := by
  intro w h1 _ h3 h4
  exact hZ w h4 ((one_sub_div_log_le c c₀ T w.im hc hcc hT h3).trans h1)

theorem norm_perronIntegrand_le_right (C₂ : ℝ)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (y T t : ℝ) (hy : 1 < y) (hT : 0 < T) (ht : T ≤ |t|) :
    ‖Fy y (((1 + 1 / Real.log y : ℝ) : ℂ) + t * I)‖ ≤
      (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
  set w : ℂ := ((1 + 1 / Real.log y : ℝ) : ℂ) + t * I with hw
  have hl : 0 < Real.log y := Real.log_pos hy
  have hre : w.re = 1 + 1 / Real.log y := by simp [hw]
  have him : w.im = t := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ Real.log y + C₂ := by
    have := hR w (by rw [hre]; have := one_div_pos.mpr hl; linarith)
    rw [hre] at this
    simpa using this
  have hpow : y ^ w.re = Real.exp 1 * y := by
    rw [hre, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hl.ne']
    ring
  have ht0 : 0 < |t| := lt_of_lt_of_le hT ht
  have hw1 : |t| ≤ ‖w‖ := by rw [← him]; exact Complex.abs_im_le_norm w
  have hw2 : |t| ≤ ‖w - 1‖ := by
    have : (w - 1).im = t := by simp [him]
    rw [← this]; exact Complex.abs_im_le_norm _
  have hden : t ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by
    rw [← sq_abs]; nlinarith [abs_nonneg t]
  have hnum : 0 ≤ Real.log y + C₂ := le_trans (norm_nonneg _) hζ
  rw [hpow]
  have htp : 0 < t ^ 2 := by rw [← sq_abs]; exact pow_pos ht0 2
  calc ‖deriv riemannZeta w / riemannZeta w‖ * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖)
      ≤ (Real.log y + C₂) * (Real.exp 1 * y) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (Real.log y + C₂) * (Real.exp 1 * y) / t ^ 2 := by
        apply div_le_div_of_nonneg_left (mul_nonneg hnum (by positivity)) htp hden

theorem norm_perronIntegrand_le_horizontal (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T x v σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 1 ≤ y) (hT : 1 ≤ T) (hv : |v| = T)
    (hx1 : 1 - c / Real.log (T + 2) ≤ x) (hx2 : x ≤ σ₀) :
    ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
  set w : ℂ := (x : ℂ) + (v : ℂ) * I with hw
  have hre : w.re = x := by simp [hw]
  have him : w.im = v := by simp [hw]
  have hy0 : 0 < y := by linarith
  rw [norm_perronIntegrand y hy0 w]
  have hw1 : T ≤ ‖w‖ := by rw [← hv, ← him]; exact Complex.abs_im_le_norm w
  have hw2 : T ≤ ‖w - 1‖ := by
    have : (w - 1).im = v := by simp [him]
    rw [← hv, ← this]; exact Complex.abs_im_le_norm _
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre]
    exact (one_sub_div_log_le c c₁ T w.im hc hcc (by linarith) (by rw [him, hv])).trans hx1
  have hD' := hD w hne hreg
  rw [him, hv] at hD'
  have hinv : ‖1 / (w - 1)‖ ≤ 1 := by
    rw [norm_div, norm_one]
    exact (div_le_one (by linarith)).mpr (by linarith)
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * Real.log (T + 2) ^ 2 + 1 := add_le_add hD' hinv
  have hpow : y ^ w.re ≤ y ^ σ₀ := by
    rw [hre]; exact Real.rpow_le_rpow_of_exponent_le hy hx2
  have hden : T ^ 2 ≤ ‖w‖ * ‖w - 1‖ := by nlinarith
  have htp : 0 < T ^ 2 := by positivity
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ w.re / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * Real.log (T + 2) ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
        apply div_le_div_of_nonneg_left (by positivity) htp hden

theorem norm_perronIntegrand_le_left (c₁ C₁ : ℝ) (hC₁ : 0 ≤ C₁)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (c y T u : ℝ) (hc : 0 < c) (hcc : c ≤ c₁) (hy : 0 < y) (hT : 0 ≤ T) (hu : |u| ≤ T)
    (hhalf : 1 / 2 ≤ 1 - c / Real.log (T + 2)) :
    ‖Fy y (((1 - c / Real.log (T + 2) : ℝ) : ℂ) + u * I)‖ ≤
      (C₁ * Real.log (T + 2) ^ 2 + Real.log (T + 2) / c) * y ^ (1 - c / Real.log (T + 2)) *
        (2 * Real.log (T + 2) / c) := by
  set L := Real.log (T + 2) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  set w : ℂ := (((1 - c / L : ℝ)) : ℂ) + u * I with hw
  have hre : w.re = 1 - c / L := by simp [hw]
  have him : w.im = u := by simp [hw]
  rw [norm_perronIntegrand y hy w]
  have hcL : 0 < c / L := div_pos hc hL
  have hw1 : 1 / 2 ≤ ‖w‖ := by
    have := Complex.abs_re_le_norm w
    rw [hre, abs_of_pos (by linarith)] at this; linarith
  have hw2 : c / L ≤ ‖w - 1‖ := by
    have h := Complex.abs_re_le_norm (w - 1)
    have : (w - 1).re = -(c / L) := by simp [hre]
    rw [this, abs_neg, abs_of_pos hcL] at h; exact h
  have hne : w ≠ 1 := by
    intro h
    have : (w - 1) = 0 := by rw [h]; ring
    rw [this, norm_zero] at hw2; linarith
  have hreg : 1 - c₁ / Real.log (|w.im| + 2) ≤ w.re := by
    rw [hre, him]
    exact one_sub_div_log_le c c₁ T u hc hcc hT hu
  have hD' := hD w hne hreg
  rw [him] at hD'
  have hlogu : Real.log (|u| + 2) ^ 2 ≤ L ^ 2 := by
    have h0 : 0 ≤ Real.log (|u| + 2) := Real.log_nonneg (by linarith [abs_nonneg u])
    have h1 : Real.log (|u| + 2) ≤ L := Real.log_le_log (by linarith [abs_nonneg u]) (by linarith)
    exact pow_le_pow_left₀ h0 h1 2
  have hinv : ‖1 / (w - 1)‖ ≤ L / c := by
    rw [norm_div, norm_one]
    have : 0 < ‖w - 1‖ := lt_of_lt_of_le hcL hw2
    rw [div_le_div_iff₀ this hc]
    have := mul_le_mul_of_nonneg_left hw2 hL.le
    rw [mul_div_cancel₀ _ hL.ne'] at this
    linarith
  have hζ : ‖deriv riemannZeta w / riemannZeta w‖ ≤ C₁ * L ^ 2 + L / c := by
    calc ‖deriv riemannZeta w / riemannZeta w‖
        = ‖(deriv riemannZeta w / riemannZeta w + 1 / (w - 1)) - 1 / (w - 1)‖ := by ring_nf
      _ ≤ ‖deriv riemannZeta w / riemannZeta w + 1 / (w - 1)‖ + ‖1 / (w - 1)‖ := norm_sub_le _ _
      _ ≤ C₁ * L ^ 2 + L / c := add_le_add (hD'.trans (mul_le_mul_of_nonneg_left hlogu hC₁)) hinv
  have hden : c / (2 * L) ≤ ‖w‖ * ‖w - 1‖ := by
    have : c / (2 * L) = (1 / 2) * (c / L) := by field_simp
    rw [this]
    exact mul_le_mul hw1 hw2 hcL.le (by linarith)
  have hden0 : 0 < c / (2 * L) := by positivity
  rw [hre]
  calc ‖deriv riemannZeta w / riemannZeta w‖ * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖)
      ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (‖w‖ * ‖w - 1‖) := by
        gcongr
    _ ≤ (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) / (c / (2 * L)) := by
        apply div_le_div_of_nonneg_left (by positivity) hden0 hden
    _ = (C₁ * L ^ 2 + L / c) * y ^ (1 - c / L) * (2 * L / c) := by
        field_simp

end Formalism.ZF
end
end

section
open Complex MeasureTheory

noncomputable section

namespace Formalism.ZF

set_option maxHeartbeats 1000000 in
theorem abs_zetaPrimeSumError_le_of_large (c₀ c₁ C₁ C₂ : ℝ) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (hD : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ C₁ * Real.log (|s.im| + 2) ^ 2)
    (hR : ∀ s : ℂ, 1 < s.re → ‖deriv riemannZeta s / riemannZeta s‖ ≤ 1 / (s.re - 1) + C₂)
    (hP : Perron) (hRS : RectShift)
    (c : ℝ) (hc : 0 < c) (hc2 : c ≤ 1 / 2) (hc0 : c ≤ c₀) (hc1 : c ≤ c₁)
    (y : ℝ) (hy : 2 ≤ y) (hs8 : 8 / c ≤ Real.sqrt (Real.log y))
    (hs1 : 1 ≤ Real.sqrt (Real.log y)) :
    |Formalism.Gz y| ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) *
        (6 * (8 / c) ^ 3) * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  obtain ⟨s, hs⟩ : ∃ s, s = Real.sqrt (Real.log y) := ⟨_, rfl⟩
  rw [← hs] at hs8 hs1 ⊢
  have hy0 : 0 < y := by linarith
  have hy1 : 1 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos hy1
  have hℓ : Real.log y = s ^ 2 := by rw [hs, Real.sq_sqrt hlogy.le]
  have hs0 : 0 < s := by linarith
  have hs3 : 1 ≤ s ^ 3 := one_le_pow₀ hs1
  have hs23 : s ^ 2 ≤ s ^ 3 := pow_le_pow_right₀ hs1 (by norm_num)
  obtain ⟨T, hTdef⟩ : ∃ T, T = Real.exp (c * s / 4) := ⟨_, rfl⟩
  obtain ⟨hT1, hL1, hLs⟩ := log_exp_add_two_bounds c s hc hs8
  rw [← hTdef] at hT1 hL1 hLs
  have hT0 : 0 < T := by linarith
  obtain ⟨L, hLdef⟩ : ∃ L, L = Real.log (T + 2) := ⟨_, rfl⟩
  rw [← hLdef] at hL1 hLs
  have hL0 : 0 < L := by linarith
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ₀ : ℝ, σ₀ = 1 + 1 / Real.log y := ⟨_, rfl⟩
  obtain ⟨σ₁, hσ₁⟩ : ∃ σ₁ : ℝ, σ₁ = 1 - c / L := ⟨_, rfl⟩
  have hinvl : 0 < 1 / Real.log y := one_div_pos.mpr hlogy
  have hinvl1 : 1 / Real.log y ≤ 1 := by
    rw [div_le_one hlogy, hℓ]
    exact one_le_pow₀ hs1
  have hσ₀1 : 1 < σ₀ := by rw [hσ₀]; linarith
  have hcL : c / L ≤ 1 / 2 := by
    rw [div_le_iff₀ hL0]
    linarith
  have hcL0 : 0 < c / L := div_pos hc hL0
  have hσ₁0 : 0 < σ₁ := by rw [hσ₁]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁]; linarith
  have hσ₁h : 1 / 2 ≤ σ₁ := by rw [hσ₁]; linarith
  have hσ01 : σ₁ ≤ σ₀ := by linarith
  obtain ⟨hint, hperron⟩ := hP y hy1.le σ₀ hσ₀1
  have hzf := riemannZeta_ne_zero_of_mem_rectangle c₀ hZ c T σ₀ hc hc0 hT0.le
  rw [← hLdef, ← hσ₁] at hzf
  have hrect := hRS y hy0 σ₁ σ₀ T hσ₁0 hσ₁1 hσ₀1 hT0 hzf
  simp only [rectInt] at hrect
  rw [integral_eq_intervalIntegral_add_compl _ hint T hT0.le] at hperron
  have halg := norm_sub_le_of_rectangle_identity _ _ _ _ _ _ _ hperron hrect
  have hcast : ((Formalism.Gz y : ℝ) : ℂ) = ((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y) := by
    simp only [Formalism.Gz]
    push_cast
    ring
  have hGz : |Formalism.Gz y| = ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := by
    rw [← hcast, Complex.norm_real, Real.norm_eq_abs]
  have hE := norm_integral_compl_le (fun t : ℝ => Fy y ((σ₀ : ℂ) + t * I))
    ((Real.log y + C₂) * (Real.exp 1 * y)) T
    (mul_nonneg (by linarith) (mul_nonneg (Real.exp_pos 1).le hy0.le)) hT0 (fun t ht => by
      have h := norm_perronIntegrand_le_right C₂ hR y T t hy1 hT0 ht
      rw [← hσ₀] at h
      exact h)
  have hHx : ∀ v : ℝ, |v| = T → ∀ x ∈ Set.uIoc σ₁ σ₀,
      ‖Fy y ((x : ℂ) + (v : ℂ) * I)‖ ≤ (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 := by
    intro v hv x hx
    rw [Set.uIoc_of_le hσ01] at hx
    have h := norm_perronIntegrand_le_horizontal c₁ C₁ hC₁ hD c y T x v σ₀ hc hc1 hy1.le hT1 hv
      (by rw [← hLdef, ← hσ₁]; exact hx.1.le) hx.2
    rw [← hLdef] at h
    exact h
  have ha := intervalIntegral.norm_integral_le_of_norm_le_const
    (hHx (-T) (by rw [abs_neg, abs_of_pos hT0]))
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (hHx T (abs_of_pos hT0))
  have hV := intervalIntegral.norm_integral_le_of_norm_le_const (a := -T) (b := T)
    (f := fun u : ℝ => Fy y ((σ₁ : ℂ) + u * I))
    (C := (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c)) (fun u hu => by
      rw [Set.uIoc_of_le (by linarith)] at hu
      have h := norm_perronIntegrand_le_left c₁ C₁ hC₁ hD c y T u hc hc1 hy0 hT0.le
        (abs_le.mpr ⟨hu.1.le, hu.2⟩) (by rw [← hLdef, ← hσ₁]; exact hσ₁h)
      rw [← hLdef, ← hσ₁] at h
      exact h)
  beta_reduce at hE hV
  obtain ⟨E', hE'def⟩ : ∃ E', E' = Real.exp (-(c * s / 4)) := ⟨_, rfl⟩
  have hE'0 : 0 < E' := by rw [hE'def]; exact Real.exp_pos _
  have hTE : T * E' = 1 := by
    rw [hTdef, hE'def, ← Real.exp_add]
    simp
  have hE'T : E' = T⁻¹ := eq_inv_of_mul_eq_one_right hTE
  have hE'1 : E' ≤ 1 := by rw [hE'T]; exact inv_le_one_of_one_le₀ hT1
  have hE'2 : E' ^ 2 ≤ E' := by
    rw [sq]
    exact mul_le_of_le_one_left hE'0.le hE'1
  have hey : 0 ≤ Real.exp 1 * y := mul_nonneg (Real.exp_pos 1).le hy0.le
  have hyσ₀ : y ^ σ₀ = Real.exp 1 * y := by
    rw [hσ₀, Real.rpow_add hy0, Real.rpow_one, Real.rpow_def_of_pos hy0,
      mul_one_div_cancel hlogy.ne']
    ring
  have hlp := exp_mul_rpow_le y c L s hy0 hℓ hc hc2 hL0 hLs hs0
  rw [← hTdef, ← hσ₁, ← hE'def] at hlp
  have hpe := pow_three_mul_exp_le c s hc hs0.le
  rw [← hE'def] at hpe
  have hLs' : L ≤ s / 4 := by
    have := mul_le_mul_of_nonneg_right hc2 hs0.le
    linarith
  have hLc : L / c ≤ s / 2 := by
    rw [div_le_iff₀ hc]
    linarith
  have hLc0 : 0 ≤ L / c := div_nonneg hL0.le hc.le
  have hL2 : L ^ 2 ≤ s ^ 2 / 16 := by
    calc L ^ 2 ≤ (s / 4) ^ 2 := pow_le_pow_left₀ hL0.le hLs' 2
      _ = s ^ 2 / 16 := by ring
  have hL3 : L ^ 2 ≤ s ^ 3 := by linarith [sq_nonneg s]
  have hlogC : Real.log y + C₂ ≤ (1 + C₂) * s ^ 3 := by
    rw [hℓ]
    calc s ^ 2 + C₂ ≤ s ^ 3 + C₂ * s ^ 3 := add_le_add hs23 (le_mul_of_one_le_right hC₂ hs3)
      _ = _ := by ring
  have hB1 : ‖∫ t in (Set.Ioc (-T) T)ᶜ, Fy y ((σ₀ : ℂ) + t * I)‖ ≤
      2 * Real.pi * ((1 + C₂) * s ^ 3 * (Real.exp 1 * y) * E') := by
    calc _ ≤ 2 * Real.pi * ((Real.log y + C₂) * (Real.exp 1 * y)) / T := hE
      _ = 2 * Real.pi * ((Real.log y + C₂) * (Real.exp 1 * y) * E') := by rw [hE'T]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hE'0.le
        exact mul_le_mul_of_nonneg_right hlogC hey
  have hA1 : C₁ * L ^ 2 + 1 ≤ (C₁ + 1) * s ^ 3 := by
    calc C₁ * L ^ 2 + 1 ≤ C₁ * s ^ 3 + s ^ 3 := add_le_add (mul_le_mul_of_nonneg_left hL3 hC₁) hs3
      _ = _ := by ring
  have hd : |σ₀ - σ₁| ≤ 2 := by
    rw [abs_of_nonneg (by linarith)]
    rw [hσ₀, hσ₁]
    linarith
  have hHb : (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 * |σ₀ - σ₁| ≤
      (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 := by
    rw [show (C₁ * L ^ 2 + 1) * y ^ σ₀ / T ^ 2 = (C₁ * L ^ 2 + 1) * (Real.exp 1 * y) * E' ^ 2 by
      rw [hyσ₀, hE'T]; ring]
    have hX0 : 0 ≤ (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) :=
      mul_nonneg (mul_nonneg (by linarith) (pow_nonneg hs0.le 3)) hey
    exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hA1 hey) hE'2 (sq_nonneg _) hX0) hd
      (abs_nonneg _) (mul_nonneg hX0 hE'0.le)
  have hq1 : L ^ 2 * (L / c) ≤ s ^ 3 := by
    calc L ^ 2 * (L / c) ≤ s ^ 2 / 16 * (s / 2) := mul_le_mul hL2 hLc hLc0 (by positivity)
      _ = s ^ 3 / 32 := by ring
      _ ≤ s ^ 3 := by linarith
  have hq2 : (L / c) ^ 2 ≤ s ^ 3 := by
    calc (L / c) ^ 2 ≤ (s / 2) ^ 2 := pow_le_pow_left₀ hLc0 hLc 2
      _ = s ^ 2 / 4 := by ring
      _ ≤ s ^ 2 := by linarith [sq_nonneg s]
      _ ≤ s ^ 3 := hs23
  have hq : (C₁ * L ^ 2 + L / c) * (L / c) ≤ (C₁ + 1) * s ^ 3 := by
    calc (C₁ * L ^ 2 + L / c) * (L / c) = C₁ * (L ^ 2 * (L / c)) + (L / c) ^ 2 := by ring
      _ ≤ C₁ * s ^ 3 + s ^ 3 := add_le_add (mul_le_mul_of_nonneg_left hq1 hC₁) hq2
      _ = _ := by ring
  have hCb : (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c) * |T - -T| ≤
      4 * ((C₁ + 1) * s ^ 3) * (y * E') := by
    rw [show |T - -T| = 2 * T by rw [sub_neg_eq_add, abs_of_pos (by linarith)]; ring]
    calc (C₁ * L ^ 2 + L / c) * y ^ σ₁ * (2 * L / c) * (2 * T)
        = 4 * ((C₁ * L ^ 2 + L / c) * (L / c)) * (T * y ^ σ₁) := by ring
      _ ≤ 4 * ((C₁ + 1) * s ^ 3) * (y * E') :=
        mul_le_mul (by linarith [hq]) hlp (mul_nonneg hT0.le (Real.rpow_nonneg hy0.le _))
          (mul_nonneg (by norm_num) (mul_nonneg (by linarith) (pow_nonneg hs0.le 3)))
  have hG0 : 0 ≤ ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := norm_nonneg _
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hK0 : 0 ≤ (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y := by
    apply mul_nonneg _ hy0.le
    have h1 : 0 ≤ 2 * Real.pi * Real.exp 1 * (1 + C₂) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ 4 * Real.exp 1 * (C₁ + 1) := mul_nonneg (by positivity) (by linarith)
    linarith
  rw [hGz]
  have hsum : ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ ≤
      (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y *
        (s ^ 3 * E') := by
    calc _ ≤ 2 * Real.pi * ‖((Formalism.Sz y : ℝ) : ℂ) -
      ((y : ℂ) * Real.log y - (1 + Real.eulerMascheroniConstant) * y)‖ := le_mul_of_one_le_left hG0 hpi
      _ ≤ _ := halg
      _ ≤ 2 * Real.pi * ((1 + C₂) * s ^ 3 * (Real.exp 1 * y) * E') +
            (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 +
            (C₁ + 1) * s ^ 3 * (Real.exp 1 * y) * E' * 2 + 4 * ((C₁ + 1) * s ^ 3) * (y * E') :=
          add_le_add (add_le_add (add_le_add hB1 (ha.trans hHb)) (hb.trans hHb)) (hV.trans hCb)
      _ = _ := by ring
  calc _ ≤ _ := hsum
    _ ≤ (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (C₁ + 1) + 4 * (C₁ + 1)) * y *
        (6 * (8 / c) ^ 3 * Real.exp (-(c / 8) * s)) := mul_le_mul_of_nonneg_left hpe hK0
    _ = _ := by ring

end Formalism.ZF
end
end

section
open Complex

noncomputable section

namespace Formalism.ZF

private theorem abs_zetaPrimeSumError_le_of_sqrt_log_lt (c : ℝ) (hc : 0 < c) (y : ℝ) (hy : 2 ≤ y)
    (hs : Real.sqrt (Real.log y) < 8 / c) :
    |Formalism.Gz y| ≤
      ((Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1) * y *
        Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by
  have hy0 : 0 < y := by linarith
  have hlog : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  have hsq : 0 ≤ Real.sqrt (Real.log y) := Real.sqrt_nonneg _
  have hlogL : Real.log y ≤ (8 / c) ^ 2 := by
    calc Real.log y = Real.sqrt (Real.log y) ^ 2 := (Real.sq_sqrt hlog).symm
      _ ≤ (8 / c) ^ 2 := pow_le_pow_left₀ hsq hs.le 2
  have hyL : y ≤ Real.exp ((8 / c) ^ 2) := by
    calc y = Real.exp (Real.log y) := (Real.exp_log hy0).symm
      _ ≤ Real.exp ((8 / c) ^ 2) := Real.exp_le_exp.mpr hlogL
  have hinner : y * Real.log y + Real.log y + 2 ≤
      Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 := by
    have := mul_le_mul hyL hlogL hlog (Real.exp_pos _).le
    linarith
  have hcs : (c / 8) * Real.sqrt (Real.log y) ≤ 1 := by
    calc (c / 8) * Real.sqrt (Real.log y) ≤ (c / 8) * (8 / c) :=
          mul_le_mul_of_nonneg_left hs.le (by positivity)
      _ = 1 := by field_simp
  have hexp : Real.exp (-1) ≤ Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    Real.exp_le_exp.mpr (by linarith)
  set M : ℝ := Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2 with hM
  have hM0 : 0 ≤ M := by positivity
  have hMe : M = M * Real.exp 1 * Real.exp (-1) := by
    rw [mul_assoc, ← Real.exp_add]; simp
  calc |Formalism.Gz y| ≤ y * (y * Real.log y + Real.log y + 2) :=
        abs_zetaPrimeSumError_le_of_one_le y (by linarith)
    _ ≤ y * M := mul_le_mul_of_nonneg_left hinner hy0.le
    _ = y * (M * Real.exp 1 * Real.exp (-1)) := by rw [← hMe]
    _ ≤ y * (M * Real.exp 1 * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by
        apply mul_le_mul_of_nonneg_left _ hy0.le
        exact mul_le_mul_of_nonneg_left hexp (by positivity)
    _ = M * Real.exp 1 * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

theorem zetaPrimeSumErrorBoundOfBounds : GzPNTOf := by
  intro hZF hLD hRH hP hRS
  obtain ⟨c₀, hc₀, hZ⟩ := hZF
  obtain ⟨c₁, C₁, hc₁, hD⟩ := hLD
  obtain ⟨C₂, hC₂, hR⟩ := hRH
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = max C₁ 0 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := hDdef ▸ le_max_right _ _
  have hD' : ∀ s : ℂ, s ≠ 1 → 1 - c₁ / Real.log (|s.im| + 2) ≤ s.re →
      ‖deriv riemannZeta s / riemannZeta s + 1 / (s - 1)‖ ≤ D * Real.log (|s.im| + 2) ^ 2 := by
    intro s hs hre
    exact (hD s hs hre).trans
      (mul_le_mul_of_nonneg_right (hDdef ▸ le_max_left _ _) (sq_nonneg _))
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ, c = min (min c₀ c₁) (1 / 2) := ⟨_, rfl⟩
  have hc : 0 < c := hcdef ▸ lt_min (lt_min hc₀ hc₁) (by norm_num)
  have hc2 : c ≤ 1 / 2 := hcdef ▸ min_le_right _ _
  have hcc₀ : c ≤ c₀ := hcdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hcc₁ : c ≤ c₁ := hcdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (2 * Real.pi * Real.exp 1 * (1 + C₂) + 4 * Real.exp 1 * (D + 1) +
      4 * (D + 1)) * (6 * (8 / c) ^ 3) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B =
      (Real.exp ((8 / c) ^ 2) * (8 / c) ^ 2 + (8 / c) ^ 2 + 2) * Real.exp 1 := ⟨_, rfl⟩
  refine ⟨c / 8, max A B, div_pos hc (by norm_num), ?_⟩
  intro y hy
  have hy0 : 0 ≤ y := by linarith
  have hyE : 0 ≤ y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) :=
    mul_nonneg hy0 (Real.exp_pos _).le
  have h8c : 16 ≤ 8 / c := by
    rw [le_div_iff₀ hc]; linarith
  by_cases hs : 8 / c ≤ Real.sqrt (Real.log y)
  · have hs1 : 1 ≤ Real.sqrt (Real.log y) := by linarith
    have h := abs_zetaPrimeSumError_le_of_large c₀ c₁ D C₂ hD0 hC₂ hZ hD' hR hP hRS
      c hc hc2 hcc₀ hcc₁ y hy hs hs1
    rw [← hA] at h
    calc |Formalism.Gz y| ≤ A * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = A * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring
  · rw [not_le] at hs
    have h := abs_zetaPrimeSumError_le_of_sqrt_log_lt c hc y hy hs
    rw [← hB] at h
    calc |Formalism.Gz y| ≤ B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := h
      _ = B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) := by ring
      _ ≤ max A B * (y * Real.exp (-(c / 8) * Real.sqrt (Real.log y))) :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hyE
      _ = max A B * y * Real.exp (-(c / 8) * Real.sqrt (Real.log y)) := by ring

end Formalism.ZF
end
end
