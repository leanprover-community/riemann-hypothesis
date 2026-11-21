import Mathlib
import Formalism.PeriodIntegrals.DiscIn
import Formalism.PeriodIntegrals.ZerosWindowIn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.Assemble
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.ExplicitFormulaFromGluing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronKernelB
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronLOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.PerronTruncOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.GoodHeightExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LStructC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthFE
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExplicitFormula.LGrowthDefs

section
namespace PI.EF.PK

open Complex MeasureTheory intervalIntegral Real

lemma seg_bound (f : ℝ → ℂ) (K a b : ℝ) (hab : a ≤ b) (h : ∀ x, a ≤ x → x ≤ b → ‖f x‖ ≤ K) :
    ‖∫ x in a..b, f x‖ ≤ K * (b - a) := by
  have hK := intervalIntegral.norm_integral_le_of_norm_le_const (f := f) (C := K) (a := a) (b := b)
    (fun x hx => by
      rw [Set.uIoc_of_le hab] at hx
      exact h x hx.1.le hx.2)
  rwa [abs_of_nonneg (sub_nonneg.mpr hab)] at hK

lemma continuous_inv_sqrt : Continuous fun t : ℝ => 2 * (√(1 + (2 * t) ^ 2))⁻¹ :=
  continuous_const.mul ((continuous_const.add ((continuous_const.mul continuous_id).pow 2)).sqrt.inv₀
    (fun t => (Real.sqrt_pos.mpr (by positivity : (0 : ℝ) < 1 + (2 * t) ^ 2)).ne'))

lemma integral_inv_sqrt (T : ℝ) :
    ∫ t in -T..T, 2 * (√(1 + (2 * t) ^ 2))⁻¹ = 2 * Real.arsinh (2 * T) := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t => Real.arsinh (2 * t)) (2 * (√(1 + (2 * t) ^ 2))⁻¹) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => 2 * t) 2 t := by
      simpa using (hasDerivAt_id t).const_mul (2 : ℝ)
    have h2 := (Real.hasDerivAt_arsinh (2 * t)).comp t h1
    rw [mul_comm _ (2 : ℝ)] at h2
    exact h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t)
    (continuous_inv_sqrt.intervalIntegrable _ _)]
  simp only [mul_neg, Real.arsinh_neg]
  ring

lemma arsinh_le (x : ℝ) (hx : 0 ≤ x) : Real.arsinh x ≤ Real.log (1 + 2 * x) := by
  have hs0 : 0 < √(1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs : √(1 + x ^ 2) ≤ 1 + x := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  unfold Real.arsinh
  exact Real.log_le_log (by linarith) (by linarith)

lemma norm_upow_div (u : ℝ) (hu : 1 ≤ u) (s : ℂ) (c m : ℝ) (hm : 0 < m) (hsc : s.re ≤ c)
    (hsm : m ≤ ‖s‖) : ‖(u : ℂ) ^ s / s‖ ≤ u ^ c / m := by
  rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
  exact div_le_div₀ (Real.rpow_pos_of_pos (by linarith) _).le
    (Real.rpow_le_rpow_of_exponent_le hu hsc) hm hsm

lemma norm_upow_div_left (u : ℝ) (hu : 1 ≤ u) (t : ℝ) :
    ‖(u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤
      2 * (√(1 + (2 * t) ^ 2))⁻¹ := by
  have hsq : 0 < √(1 + (2 * t) ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hm : 0 < √(1 + (2 * t) ^ 2) / 2 := by positivity
  have hsm : √(1 + (2 * t) ^ 2) / 2 ≤ ‖(((-1 / 2 : ℝ) : ℂ) + t * I)‖ := by
    rw [Complex.norm_add_mul_I, Real.le_sqrt hm.le, div_pow, Real.sq_sqrt (by positivity)]
    · exact le_of_eq (by ring)
    · positivity
  have h1 := norm_upow_div u hu (((-1 / 2 : ℝ) : ℂ) + t * I) (-1 / 2) _ hm (by simp) hsm
  calc _ ≤ u ^ (-1 / 2 : ℝ) / (√(1 + (2 * t) ^ 2) / 2) := h1
    _ ≤ 1 / (√(1 + (2 * t) ^ 2) / 2) := by
        gcongr
        exact Real.rpow_le_one_of_one_le_of_nonpos hu (by norm_num)
    _ = 2 * (√(1 + (2 * t) ^ 2))⁻¹ := by field_simp

lemma combine {B Tp R Lf : ℂ} {b1 b2 b3 : ℝ} (h1 : ‖B‖ ≤ b1) (h2 : ‖Tp‖ ≤ b2) (h3 : ‖Lf‖ ≤ b3) :
    ‖B - Tp + I * R - I * Lf + -(I * R)‖ ≤ b1 + b2 + b3 := by
  have e : B - Tp + I * R - I * Lf + -(I * R) = B - Tp - I * Lf := by ring
  rw [e]
  have hI : ‖I * Lf‖ = ‖Lf‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have hs := norm_sub_le (B - Tp) (I * Lf)
  have hs2 := norm_sub_le B Tp
  linarith

lemma cLine_le_three {u : ℝ} (hu : 2 ≤ u) : cLine u ≤ 3 := by
  unfold cLine
  have h2 : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl : Real.log 2 ≤ Real.log u := Real.log_le_log (by norm_num) hu
  have hpos : 0 < Real.log u := by linarith
  have h3 : 1 / Real.log u ≤ 2 := by rw [div_le_iff₀ hpos]; linarith
  linarith

lemma rpow_cLine_le {u : ℝ} (hu : 2 ≤ u) : u ^ cLine u ≤ 3 * u := by
  have hu0 : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos (by linarith)
  unfold cLine
  rw [Real.rpow_add hu0, Real.rpow_one, Real.rpow_def_of_pos hu0, mul_one_div_cancel hl.ne']
  have := Real.exp_one_lt_d9
  nlinarith

lemma log_le_two_mul {X Y : ℝ} (hX : 0 < X) (hXY : X ≤ Y ^ 2) : Real.log X ≤ 2 * Real.log Y := by
  calc Real.log X ≤ Real.log (Y ^ 2) := Real.log_le_log hX hXY
    _ = 2 * Real.log Y := by rw [Real.log_pow]; push_cast; ring

lemma log_facts {N : ℕ} {u T T' : ℝ} (hN : (1 : ℝ) ≤ N) (hT : 2 ≤ T) (hTu : T ≤ u) (hTT' : T ≤ T')
    (hT'1 : T' ≤ T + 1) :
    0 ≤ Real.log (N * u * T) ∧ Real.log (N * T') ≤ Real.log (N * u * T) ∧
      0 ≤ Real.log (N * T') ∧ Real.log (N * (T' + 2)) ≤ 2 * Real.log (N * u * T) ∧
      Real.log (1 + 2 * (2 * T')) ≤ 2 * Real.log (N * u * T) ∧ 0 ≤ Real.log (N * (T' + 2)) ∧
      0 ≤ Real.log (N * u) := by
  have hT0 : 0 < T := by linarith
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hN0 : 0 < (N : ℝ) := by linarith
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hNu : 2 ≤ (N : ℝ) * u := by nlinarith
  have hNuT : 4 ≤ (N : ℝ) * u * T := by nlinarith
  have hY2 : (N : ℝ) * (4 * T ^ 2) ≤ ((N : ℝ) * u * T) ^ 2 := by
    have h1 : (N : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith
    have h2 : 4 * T ^ 2 ≤ u ^ 2 * T ^ 2 := by
      have hu4 : 4 ≤ u ^ 2 := by nlinarith
      exact mul_le_mul_of_nonneg_right hu4 (sq_nonneg T)
    calc (N : ℝ) * (4 * T ^ 2) ≤ (N : ℝ) ^ 2 * (u ^ 2 * T ^ 2) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((N : ℝ) * u * T) ^ 2 := by ring
  have hNT' : 1 ≤ (N : ℝ) * T' := by nlinarith
  have hNT'2 : 1 ≤ (N : ℝ) * (T' + 2) := by nlinarith
  refine ⟨Real.log_nonneg (by linarith), Real.log_le_log (by nlinarith) ?_, Real.log_nonneg hNT', ?_, ?_,
    Real.log_nonneg hNT'2, Real.log_nonneg (by linarith)⟩
  · have h : T' ≤ u * T := by nlinarith
    calc (N : ℝ) * T' ≤ N * (u * T) := mul_le_mul_of_nonneg_left h hN0.le
      _ = N * u * T := by ring
  · apply log_le_two_mul (by nlinarith)
    calc (N : ℝ) * (T' + 2) ≤ N * (4 * T ^ 2) := mul_le_mul_of_nonneg_left (by nlinarith) hN0.le
      _ ≤ _ := hY2
  · apply log_le_two_mul (by nlinarith)
    calc 1 + 2 * (2 * T') ≤ (N : ℝ) * (4 * T ^ 2) := by nlinarith
      _ ≤ _ := hY2

lemma hor_side (G : ℂ → ℂ) (u c T' A h : ℝ) (hu : 1 ≤ u) (hc : -1 / 2 ≤ c) (hT'0 : 0 < T')
    (hA : 0 ≤ A) (hh : |h| = T') (hb : ∀ σ : ℝ, -1 / 2 ≤ σ → σ ≤ c → ‖G ((σ : ℂ) + h * I)‖ ≤ A) :
    ‖∫ x : ℝ in (-1 / 2)..c, G ((x : ℂ) + h * I) * ((u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I))‖ ≤
      A * (u ^ c / T') * (c - -1 / 2) := by
  refine seg_bound _ _ _ _ hc (fun x hx1 hx2 => ?_)
  rw [norm_mul]
  have h1 := hb x hx1 hx2
  have him : |h| ≤ ‖(x : ℂ) + h * I‖ := by
    have := Complex.abs_im_le_norm ((x : ℂ) + h * I)
    simpa using this
  have h2 : ‖(u : ℂ) ^ ((x : ℂ) + h * I) / ((x : ℂ) + h * I)‖ ≤ u ^ c / T' :=
    norm_upow_div u hu _ c T' hT'0 (by simpa using hx2) (by rw [← hh]; exact him)
  exact mul_le_mul h1 h2 (norm_nonneg _) hA

lemma left_side (G : ℂ → ℂ) (u T' K2 : ℝ) (hu : 1 ≤ u) (hT'0 : 0 < T') (hK20 : 0 ≤ K2)
    (hb : ∀ t : ℝ, |t| ≤ T' → ‖G (((-1 / 2 : ℝ) : ℂ) + t * I)‖ ≤ K2) :
    ‖∫ t : ℝ in -T'..T', G (((-1 / 2 : ℝ) : ℂ) + t * I) *
        ((u : ℂ) ^ (((-1 / 2 : ℝ) : ℂ) + t * I) / (((-1 / 2 : ℝ) : ℂ) + t * I))‖ ≤
      K2 * (2 * Real.arsinh (2 * T')) := by
  have hle : -T' ≤ T' := by linarith
  calc _ ≤ ∫ t in -T'..T', K2 * (2 * (√(1 + (2 * t) ^ 2))⁻¹) := by
        refine intervalIntegral.norm_integral_le_of_norm_le hle
          (Filter.Eventually.of_forall (fun t ht => ?_))
          ((continuous_const.mul continuous_inv_sqrt).intervalIntegrable _ _)
        rw [norm_mul]
        have ht' : |t| ≤ T' := abs_le.mpr ⟨ht.1.le, ht.2⟩
        exact mul_le_mul (hb t ht') (norm_upow_div_left u hu t) (norm_nonneg _) hK20
    _ = K2 * (2 * Real.arsinh (2 * T')) := by
        rw [intervalIntegral.integral_const_mul, integral_inv_sqrt]

lemma vert_cancel (G k : ℝ → ℂ) (T' : ℝ) :
    2 * π * I * ((1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ in -T'..T', -G t * k t) =
      -(I * ∫ t : ℝ in -T'..T', G t * k t) := by
  have h : ∫ t : ℝ in -T'..T', -G t * k t = -∫ t : ℝ in -T'..T', G t * k t := by
    simp only [neg_mul]
    exact intervalIntegral.integral_neg
  rw [h]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  field_simp

lemma sides_arith {C1 C2 u T T' c l1 l2 as large₂ lNu uc : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hT0 : 0 < T)
    (hu0 : 0 < u) (hTu : T ≤ u) (hTT' : T ≤ T') (hc1 : 1 < c) (hc3 : c ≤ 3) (huc0 : 0 ≤ uc)
    (huc : uc ≤ 3 * u)
    (hLg0 : 0 ≤ large₂) (hl1 : l1 ≤ large₂) (hl1' : 0 ≤ l1) (hl2 : l2 ≤ 2 * large₂) (has : as ≤ 2 * large₂)
    (has0 : 0 ≤ as) (hlNu : 0 ≤ lNu) :
    C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) + C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) +
      C2 * l2 * (2 * as) ≤ (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) := by
  have hT'0 : 0 < T' := by linarith
  have hq : uc / T' ≤ 3 * u / T := by
    rw [div_le_div_iff₀ hT'0 hT0]
    nlinarith
  have hl1sq : l1 ^ 2 ≤ large₂ ^ 2 := by nlinarith
  have hcc : c - -1 / 2 ≤ 7 / 2 := by linarith
  have hcc0 : 0 ≤ c - -1 / 2 := by linarith
  have hq0 : 0 ≤ uc / T' := div_nonneg huc0 hT'0.le
  have hY0 : 0 ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_nonneg (mul_nonneg hC1 (sq_nonneg _)) (div_nonneg (by linarith) hT0.le)
  have hX : C1 * l1 ^ 2 * (uc / T') ≤ C1 * large₂ ^ 2 * (3 * u / T) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl1sq hC1) hq hq0 (mul_nonneg hC1 (sq_nonneg _))
  have hA : C1 * l1 ^ 2 * (uc / T') * (c - -1 / 2) ≤ C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) :=
    mul_le_mul hX hcc hcc0 hY0
  have hB : C2 * l2 * (2 * as) ≤ C2 * (2 * large₂) * (2 * (2 * large₂)) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hl2 hC2) (by linarith) (by linarith)
      (mul_nonneg hC2 (by linarith))
  have e1 : C1 * large₂ ^ 2 * (3 * u / T) * (7 / 2) = 21 / 2 * (C1 * (u * large₂ ^ 2 / T)) := by ring
  have e2 : C2 * (2 * large₂) * (2 * (2 * large₂)) = 8 * (C2 * large₂ ^ 2) := by ring
  have h3 : large₂ ^ 2 ≤ u * large₂ ^ 2 / T := by
    rw [le_div_iff₀ hT0]
    nlinarith [sq_nonneg large₂]
  have h4 : C2 * large₂ ^ 2 ≤ C2 * (u * large₂ ^ 2 / T) := mul_le_mul_of_nonneg_left h3 hC2
  have h5 : 0 ≤ (21 * C1 + 8 * C2) * lNu := mul_nonneg (by linarith) hlNu
  have e3 : (21 * C1 + 8 * C2) * (u * large₂ ^ 2 / T + lNu) =
      21 * (C1 * (u * large₂ ^ 2 / T)) + 8 * (C2 * (u * large₂ ^ 2 / T)) + (21 * C1 + 8 * C2) * lNu := by ring
  rw [e3]
  linarith

theorem sidesBound_of {κ C1 C2 : ℝ} (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2) (hH : LogDerivHoriz κ C1)
    (hL : LogDerivLeft C2) : SidesBound κ (21 * C1 + 8 * C2) := by
  intro N _ χ hχ u T T' hT hTu hTT' hT'1 hgood
  have hu2 : 2 ≤ u := le_trans hT hTu
  have hT'2 : 2 ≤ T' := le_trans hT hTT'
  have hT'0 : 0 < T' := by linarith
  have hc1 : 1 < cLine u := one_lt_cLine hu2
  have hc3 : cLine u ≤ 3 := cLine_le_three hu2
  have hN : (1 : ℝ) ≤ N := Nat.one_le_cast.mpr (Nat.pos_of_ne_zero (NeZero.ne N))
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6, hf7⟩ := log_facts hN hT hTu hTT' hT'1

  have hbot := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) (-T') (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (by rw [abs_neg, abs_of_pos hT'0])
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).2)
  have htop := hor_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u (cLine u) T'
    (C1 * Real.log (N * T') ^ 2) T' (by linarith) (by linarith) hT'0
    (mul_nonneg hC1 (sq_nonneg _)) (abs_of_pos hT'0)
    (fun σ h1 h2 => (hH N χ hχ T' hT'2 hgood σ h1 (by linarith)).1)
  have hleft := left_side (fun s => logDeriv (DirichletCharacter.LFunction χ) s) u T'
    (C2 * Real.log (N * (T' + 2))) (by linarith) hT'0 (mul_nonneg hC2 hf6)
    (fun t ht => le_trans (hL N χ hχ t) (mul_le_mul_of_nonneg_left
      (Real.log_le_log (mul_pos (by linarith) (by positivity))
        (mul_le_mul_of_nonneg_left (by linarith) (by linarith))) hC2))

  have hv := vert_cancel (fun t => logDeriv (DirichletCharacter.LFunction χ) ((cLine u : ℂ) + t * I))
    (fun t => (u : ℂ) ^ ((cLine u : ℂ) + t * I) / ((cLine u : ℂ) + t * I)) T'
  unfold rectInt vertInt
  rw [hv]
  simp only [smul_eq_mul]
  refine le_trans (combine hbot htop hleft) ?_
  exact sides_arith hC1 hC2 (by linarith) (by linarith) hTu hTT' hc1 hc3
    (Real.rpow_nonneg (by linarith) _) (rpow_cLine_le hu2) hf1 hf2 hf3 hf4
    ((arsinh_le (2 * T') (by linarith)).trans hf5) (Real.arsinh_nonneg_iff.mpr (by linarith)) hf7

end PI.EF.PK
end

section
namespace PI.EF

theorem perron_gluing_sides : GlueSides := by
  rintro κ _ ⟨C1, hC1, hH⟩ ⟨C2, hC2, hL⟩
  exact ⟨21 * C1 + 8 * C2, by positivity, PK.sidesBound_of hC1.le hC2.le hH hL⟩

end PI.EF
end

section
namespace PI.EF.Loc

open Complex Metric Set Filter Topology

theorem logDeriv_bound_of_zero_free (hDL : PI.DiscLog) {g : ℂ → ℂ} {s₀ : ℂ} {r R M : ℝ}
    (hr : 0 < r) (hrR : r < R) (hM : 0 < M) (hg : DifferentiableOn ℂ g (ball s₀ R))
    (hz : ∀ z ∈ ball s₀ R, g z ≠ 0) (hb : ∀ z ∈ ball s₀ R, ‖g z‖ ≤ Real.exp M * ‖g s₀‖) :
    ∀ z ∈ closedBall s₀ r, ‖deriv g z / g z‖ ≤ 4 * (r + R) / (R - r) ^ 2 * M := by
  intro z hzr
  obtain ⟨L, hL0, hLd, hLe⟩ := hDL g s₀ R hg hz
  have hR : 0 < R := hr.trans hrR
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hg0 : 0 < ‖g s₀‖ := norm_pos_iff.mpr (hz s₀ hs₀)
  have hLdiff : DifferentiableOn ℂ L (ball s₀ R) := fun x hx =>
    (hLd x hx).differentiableAt.differentiableWithinAt
  have hre : ∀ x ∈ ball s₀ R, (L x).re ≤ M := by
    intro x hx
    have h1 := hb x hx
    rw [hLe x hx, norm_mul, Complex.norm_exp, mul_comm (Real.exp M)] at h1
    exact Real.exp_le_exp.mp (le_of_mul_le_mul_left h1 hg0)
  have hmem : ∀ u ∈ ball (0 : ℂ) R, s₀ + u ∈ ball s₀ R := by
    intro u hu
    rw [mem_ball_zero_iff] at hu
    simpa [dist_eq_norm] using hu
  have hFd : DifferentiableOn ℂ (fun u => L (s₀ + u)) (ball 0 R) := by
    intro u hu
    have h1 : DifferentiableAt ℂ L (s₀ + u) := (hLd _ (hmem u hu)).differentiableAt
    have h2 : DifferentiableAt ℂ (fun v : ℂ => s₀ + v) u := differentiableAt_id.const_add s₀
    exact (h1.comp u h2).differentiableWithinAt
  have hFre : MapsTo (fun u => L (s₀ + u)) (ball 0 R) {w | w.re ≤ M} :=
    fun u hu => hre _ (hmem u hu)
  have hF0 : (fun u => L (s₀ + u)) 0 = 0 := by simp [hL0]
  have hρR : (r + R) / 2 < R := by linarith
  have hbound : ∀ x ∈ closedBall s₀ ((r + R) / 2),
      ‖L x‖ ≤ 2 * M * ((r + R) / 2) / (R - (r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx
    have hu : x - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball_zero_iff]; linarith
    have h1 := Complex.borelCaratheodory_zero hM hFd hFre hR hu hF0
    have e : s₀ + (x - s₀) = x := by ring
    simp only [e] at h1
    refine h1.trans ?_
    have hpos : 0 < R - (r + R) / 2 := by linarith
    rw [div_le_div_iff₀ (by linarith) hpos]
    nlinarith [mul_nonneg (mul_nonneg hM.le hR.le) (sub_nonneg.mpr hx)]
  have hδ : 0 < (R - r) / 2 := by linarith
  have hzr' : ‖z - s₀‖ ≤ r := by rw [mem_closedBall, dist_eq_norm] at hzr; exact hzr
  have hsub : closedBall z ((R - r) / 2) ⊆ closedBall s₀ ((r + R) / 2) := by
    intro x hx
    rw [mem_closedBall, dist_eq_norm] at hx ⊢
    have : ‖x - s₀‖ ≤ ‖x - z‖ + ‖z - s₀‖ := by
      have := norm_add_le (x - z) (z - s₀)
      simpa using this
    linarith
  have hsubB : closedBall s₀ ((r + R) / 2) ⊆ ball s₀ R := closedBall_subset_ball hρR
  have hdc : DiffContOnCl ℂ L (ball z ((R - r) / 2)) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball z hδ.ne']
    exact hLdiff.mono (hsub.trans hsubB)
  have hc := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hδ hdc
    (fun x hx => hbound x (hsub (sphere_subset_closedBall hx)))
  have hzB : z ∈ ball s₀ R := hsubB (hsub (mem_closedBall_self hδ.le))
  rw [(hLd z hzB).deriv] at hc
  refine hc.trans (le_of_eq ?_)
  have e1 : R - (r + R) / 2 = (R - r) / 2 := by ring
  have hne : R - r ≠ 0 := by linarith
  rw [e1]
  field_simp
  ring

end PI.EF.Loc
end

section
noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology ComplexConjugate

def refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) : ℂ := ((R : ℂ) ^ 2 - conj (ρ - s₀) * (z - s₀)) / R

lemma norm_refl_sphere {s₀ ρ z : ℂ} {R : ℝ} (hR : 0 < R) (hz : z ∈ sphere s₀ R) :
    ‖refl s₀ R ρ z‖ = ‖z - ρ‖ := by
  have hw : ‖z - s₀‖ = R := by rwa [mem_sphere_iff_norm] at hz
  have hR2 : (R : ℂ) ^ 2 = (z - s₀) * conj (z - s₀) := by
    rw [mul_conj, normSq_eq_norm_sq, hw]
    push_cast
    ring
  have hk : (z - s₀) * conj (z - s₀) - conj (ρ - s₀) * (z - s₀) = (z - s₀) * conj (z - ρ) := by
    simp only [map_sub]
    ring
  unfold refl
  rw [hR2, hk, norm_div, norm_mul, Complex.norm_conj, hw, Complex.norm_real, Real.norm_of_nonneg hR.le]
  field_simp

lemma le_norm_refl {s₀ ρ z : ℂ} {R R' : ℝ} (hR : 0 < R) (hρ : ρ ∈ closedBall s₀ R')
    (hz : z ∈ closedBall s₀ R) : R - R' ≤ ‖refl s₀ R ρ z‖ := by
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  have hw : ‖z - s₀‖ ≤ R := by rwa [mem_closedBall, dist_eq_norm] at hz
  unfold refl
  rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hR.le, le_div_iff₀ hR]
  have h1 : ‖(R : ℂ) ^ 2‖ = R ^ 2 := by
    rw [norm_pow, Complex.norm_real, Real.norm_of_nonneg hR.le]
  have h2 : ‖conj (ρ - s₀) * (z - s₀)‖ ≤ R' * R := by
    rw [norm_mul, Complex.norm_conj]
    exact mul_le_mul ha hw (norm_nonneg _) ((norm_nonneg _).trans ha)
  have h3 := norm_sub_norm_le ((R : ℂ) ^ 2) (conj (ρ - s₀) * (z - s₀))
  rw [h1] at h3
  nlinarith

lemma refl_center {s₀ ρ : ℂ} {R : ℝ} (hR : 0 < R) : refl s₀ R ρ s₀ = R := by
  have h : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  unfold refl
  rw [sub_self, mul_zero, sub_zero, pow_two, mul_div_assoc, div_self h, mul_one]

lemma hasDerivAt_refl (s₀ : ℂ) (R : ℝ) (ρ z : ℂ) :
    HasDerivAt (refl s₀ R ρ) (-(conj (ρ - s₀) * 1) / R) z :=
  ((((hasDerivAt_id' z).sub_const s₀).const_mul (conj (ρ - s₀))).const_sub ((R : ℂ) ^ 2)).div_const (R : ℂ)

lemma differentiable_refl (s₀ : ℂ) (R : ℝ) (ρ : ℂ) : Differentiable ℂ (refl s₀ R ρ) :=
  fun z => (hasDerivAt_refl s₀ R ρ z).differentiableAt

lemma norm_logDeriv_refl_le {s₀ ρ z : ℂ} {R R' : ℝ} (hR'R : R' < R) (hR : 0 < R)
    (hρ : ρ ∈ closedBall s₀ R') (hz : z ∈ closedBall s₀ R) :
    ‖logDeriv (refl s₀ R ρ) z‖ ≤ R' / (R * (R - R')) := by
  have hpos : 0 < R - R' := sub_pos.mpr hR'R
  have hl := le_norm_refl hR hρ hz
  have hn : 0 < ‖refl s₀ R ρ z‖ := lt_of_lt_of_le hpos hl
  have ha : ‖ρ - s₀‖ ≤ R' := by rwa [mem_closedBall, dist_eq_norm] at hρ
  rw [logDeriv_apply, (hasDerivAt_refl s₀ R ρ z).deriv, norm_div, norm_div, norm_neg, mul_one,
    Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg hR.le, div_div,
    div_le_div_iff₀ (mul_pos hR hn) (mul_pos hR hpos)]
  have h4 := mul_le_mul ha hl hpos.le ((norm_nonneg _).trans ha)
  nlinarith

lemma logDeriv_prod_pow_mul {Z : Finset ℂ} {m : ℂ → ℕ} {φ : ℂ → ℂ → ℂ} {h : ℂ → ℂ} {s : ℂ}
    (hφ : ∀ ρ ∈ Z, φ ρ s ≠ 0) (hφd : ∀ ρ ∈ Z, DifferentiableAt ℂ (φ ρ) s) (hh : h s ≠ 0)
    (hhd : DifferentiableAt ℂ h s) :
    logDeriv (fun z => (∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) * h z) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (φ ρ) s) + logDeriv h s := by
  have hP : (∏ ρ ∈ Z, (φ ρ s) ^ (m ρ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)
  have hPd : DifferentiableAt ℂ (fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) s :=
    by
      have h5 := DifferentiableAt.finset_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
      rwa [Finset.prod_fn] at h5
  rw [logDeriv_mul (f := fun z => ∏ ρ ∈ Z, (φ ρ z) ^ (m ρ)) (g := h) (x := s) hP hh hPd hhd]
  congr 1
  have h6 := logDeriv_prod (f := fun ρ z => (φ ρ z) ^ (m ρ)) (s := Z) (x := s)
    (fun ρ hρ => pow_ne_zero _ (hφ ρ hρ)) (fun ρ hρ => (hφd ρ hρ).pow _)
  rw [h6]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  exact logDeriv_fun_pow (hφd ρ hρ) (m ρ)

lemma order_eq_of_factor {f h : ℂ → ℂ} {Z : Finset ℂ} {m : ℂ → ℕ} {ρ : ℂ} (hρ : ρ ∈ Z) {U : Set ℂ}
    (hU : U ∈ 𝓝 ρ) (hf : AnalyticAt ℂ f ρ) (hh : DifferentiableOn ℂ h U) (hhρ : h ρ ≠ 0)
    (hfac : ∀ z ∈ U, f z = (∏ ρ' ∈ Z, (z - ρ') ^ (m ρ')) * h z) :
    analyticOrderNatAt f ρ = m ρ := by
  have hha : AnalyticAt ℂ h ρ := hh.analyticAt hU
  have hg : AnalyticAt ℂ (fun z => (∏ ρ' ∈ Z.erase ρ, (z - ρ') ^ (m ρ')) * h z) ρ :=
    by
      have h7 := Finset.analyticAt_prod (𝕜 := ℂ) (Z.erase ρ) (f := fun ρ' z => (z - ρ') ^ (m ρ')) (c := ρ)
        (fun ρ' _ => by fun_prop)
      rw [Finset.prod_fn] at h7
      exact h7.mul hha
  have hg0 : (∏ ρ' ∈ Z.erase ρ, (ρ - ρ') ^ (m ρ')) * h ρ ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ' hρ' =>
      pow_ne_zero _ (sub_ne_zero.mpr (Finset.ne_of_mem_erase hρ').symm)) hhρ
  have hord : analyticOrderAt f ρ = (m ρ : ℕ∞) := by
    rw [hf.analyticOrderAt_eq_natCast]
    refine ⟨_, hg, hg0, ?_⟩
    filter_upwards [hU] with z hz
    rw [hfac z hz, ← Finset.mul_prod_erase Z (fun ρ' => (z - ρ') ^ (m ρ')) hρ, smul_eq_mul, mul_assoc]
  simp [analyticOrderNatAt, hord]

end PI.EF.Loc
end
end

section
noncomputable section

namespace PI.EF.Loc

open Complex Metric Set Filter Topology

def locC (r R' R : ℝ) : ℝ :=
  4 * (r + R') / (R' - r) ^ 2 + R' / (R * (R - R')) / Real.log (R / R')

lemma locC_pos {r R' R : ℝ} (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) : 0 < locC r R' R := by
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  have h1 : 0 < 4 * (r + R') / (R' - r) ^ 2 :=
    div_pos (by linarith) (pow_pos (by linarith) 2)
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have h2 : 0 < R' / (R * (R - R')) / Real.log (R / R') :=
    div_pos (div_pos hR' (mul_pos hR (by linarith))) hlog
  unfold locC
  linarith

section core

variable {r R' R M : ℝ} {f h : ℂ → ℂ} {s₀ : ℂ} {Z : Finset ℂ} {m : ℂ → ℕ}

def gfun (s₀ : ℂ) (R : ℝ) (Z : Finset ℂ) (m : ℂ → ℕ) (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  (∏ ρ ∈ Z, (refl s₀ R ρ z) ^ (m ρ)) * h z

private theorem differentiableOn_gfun_of_differentiableOn {U : Set ℂ} (hh : DifferentiableOn ℂ h U) :
    DifferentiableOn ℂ (gfun s₀ R Z m h) U := by
  have e : gfun s₀ R Z m h = fun z => (∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) * h z := rfl
  rw [e]
  refine DifferentiableOn.mul ?_ hh
  have hd : Differentiable ℂ (fun z => ∏ ρ ∈ Z, refl s₀ R ρ z ^ m ρ) := by
    first
      | exact Differentiable.finset_prod fun ρ _ => (differentiable_refl s₀ R ρ).pow (m ρ)
      | (have hbd := differentiable_refl s₀ R; fun_prop)
  exact hd.differentiableOn

lemma gfun_bounds (hR' : 0 < R') (hR'R : R' < R)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    (∀ z ∈ closedBall s₀ R, ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * ‖gfun s₀ R Z m h s₀‖) ∧
      ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * Real.log (R / R') ≤ M := by
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∑ ρ ∈ Z, m ρ = N := ⟨_, rfl⟩
  have hs₀R' : s₀ ∈ closedBall s₀ R' := mem_closedBall_self hR'.le
  have hs₀R : s₀ ∈ closedBall s₀ R := mem_closedBall_self hR.le
  have hhs₀ : h s₀ ≠ 0 := hh0 s₀ hs₀R'
  have hg₀ : gfun s₀ R Z m h s₀ = (R : ℂ) ^ N * h s₀ := by
    have hc : ∀ ρ ∈ Z, refl s₀ R ρ s₀ ^ m ρ = (R : ℂ) ^ m ρ := fun ρ _ => by
      rw [refl_center hR]
    simp only [gfun]
    rw [Finset.prod_congr rfl hc, Finset.prod_pow_eq_pow_sum, hN]
  have hg₀n : ‖gfun s₀ R Z m h s₀‖ = R ^ N * ‖h s₀‖ := by
    rw [hg₀, norm_mul, norm_pow]
    rw [Complex.norm_real, Real.norm_of_nonneg hR.le]
  have hf₀ : ‖f s₀‖ ≤ R' ^ N * ‖h s₀‖ := by
    rw [hfac s₀ hs₀R, norm_mul, norm_prod]
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    calc ∏ ρ ∈ Z, ‖(s₀ - ρ) ^ m ρ‖ = ∏ ρ ∈ Z, ‖s₀ - ρ‖ ^ m ρ := by simp only [norm_pow]
      _ ≤ ∏ ρ ∈ Z, R' ^ m ρ := by
        refine Finset.prod_le_prod (fun ρ _ => by positivity) fun ρ hρ => ?_
        have hρ' : ρ ∈ closedBall s₀ R' := ((hZ ρ).1 hρ).1
        rw [mem_closedBall, dist_eq_norm] at hρ'
        rw [norm_sub_rev]
        exact pow_le_pow_left₀ (norm_nonneg _) hρ' _
      _ = R' ^ N := by rw [Finset.prod_pow_eq_pow_sum, hN]
  have hsphere : ∀ z ∈ sphere s₀ R, ‖gfun s₀ R Z m h z‖ = ‖f z‖ := by
    intro z hz
    rw [hfac z (sphere_subset_closedBall hz)]
    simp only [gfun, norm_mul, norm_prod, norm_pow, norm_refl_sphere hR hz]
  have hdc : DiffContOnCl ℂ (gfun s₀ R Z m h) (ball s₀ R) := by
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball s₀ hR.ne']
    exact differentiableOn_gfun_of_differentiableOn hh
  have hmax : ∀ z ∈ closedBall s₀ R,
      ‖gfun s₀ R Z m h z‖ ≤ Real.exp M * (R' ^ N * ‖h s₀‖) := by
    intro z hz
    refine Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hdc ?_
      (by rwa [closure_ball s₀ hR.ne'])
    intro w hw
    rw [frontier_ball s₀ hR.ne'] at hw
    rw [hsphere w hw]
    exact (hb w (sphere_subset_closedBall hw)).trans
      (mul_le_mul_of_nonneg_left hf₀ (Real.exp_pos M).le)
  have hkey : R ^ N ≤ Real.exp M * R' ^ N := by
    have h1 := hmax s₀ hs₀R
    rw [hg₀n, ← mul_assoc] at h1
    exact le_of_mul_le_mul_right h1 (norm_pos_iff.mpr hhs₀)
  refine ⟨fun z hz => ?_, ?_⟩
  · rw [hg₀n]
    refine (hmax z hz).trans ?_
    have hp : R' ^ N ≤ R ^ N := pow_le_pow_left₀ hR'.le hR'R.le N
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hp (norm_nonneg _))
      (Real.exp_pos M).le
  · rw [hN]
    have hl := Real.log_le_log (pow_pos hR N) hkey
    rw [Real.log_mul (Real.exp_pos M).ne' (pow_pos hR' N).ne', Real.log_exp, Real.log_pow,
      Real.log_pow] at hl
    rw [Real.log_div hR.ne' hR'.ne', mul_sub]
    linarith

theorem core (hDL : PI.DiscLog) (hr : 0 < r) (hrR' : r < R') (hR'R : R' < R) (hM : 0 < M)
    (hZ : ∀ ρ : ℂ, ρ ∈ Z ↔ (ρ ∈ closedBall s₀ R' ∧ f ρ = 0))
    (hh : DifferentiableOn ℂ h (closedBall s₀ R)) (hh0 : ∀ z ∈ closedBall s₀ R', h z ≠ 0)
    (hfac : ∀ z ∈ closedBall s₀ R, f z = (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
      ‖logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  intro s hs hfs
  have hR' : 0 < R' := hr.trans hrR'
  have hR : 0 < R := hR'.trans hR'R
  obtain ⟨hg, hN⟩ := gfun_bounds hR' hR'R hZ hh hh0 hfac hb
  have hsR' : s ∈ closedBall s₀ R' := closedBall_subset_closedBall hrR'.le hs
  have hsball : s ∈ ball s₀ R := closedBall_subset_ball (hrR'.trans hR'R) hs
  have hsR : s ∈ closedBall s₀ R := ball_subset_closedBall hsball
  have hnhds : closedBall s₀ R ∈ 𝓝 s :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hsball) ball_subset_closedBall
  have hhs : h s ≠ 0 := hh0 s hsR'
  have hhd : DifferentiableAt ℂ h s := hh.differentiableAt hnhds
  have hρs : ∀ ρ ∈ Z, s - ρ ≠ 0 := by
    intro ρ hρ h0
    have hsρ : s = ρ := sub_eq_zero.mp h0
    exact hfs (by rw [hsρ]; exact ((hZ ρ).1 hρ).2)
  have hfeq : f =ᶠ[𝓝 s] fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z :=
    Filter.eventually_of_mem hnhds fun z hz => hfac z hz
  have hlf : logDeriv f s = (∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ)) + logDeriv h s := by
    have e1 : logDeriv f s = logDeriv (fun z => (∏ ρ ∈ Z, (z - ρ) ^ m ρ) * h z) s := by
      rw [logDeriv_apply, logDeriv_apply, hfeq.deriv_eq, hfeq.eq_of_nhds]
    rw [e1]
    refine (logDeriv_prod_pow_mul (φ := fun ρ z => z - ρ) (h := h) hρs
      (fun ρ _ => by fun_prop) hhs hhd).trans ?_
    congr 1
    refine Finset.sum_congr rfl fun ρ _ => ?_
    show (m ρ : ℂ) * logDeriv (fun z => z - ρ) s = (m ρ : ℂ) / (s - ρ)
    simp only [logDeriv_apply, deriv_sub_const, deriv_id'']
    ring
  have hBne : ∀ z ∈ closedBall s₀ R, ∀ ρ ∈ Z, refl s₀ R ρ z ≠ 0 := by
    intro z hz ρ hρ h0
    have h1 := le_norm_refl (R' := R') hR ((hZ ρ).1 hρ).1 hz
    rw [h0, norm_zero] at h1
    linarith
  have hlg : logDeriv (gfun s₀ R Z m h) s =
      (∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s) + logDeriv h s :=
    logDeriv_prod_pow_mul (φ := fun ρ => refl s₀ R ρ) (fun ρ hρ => hBne s hsR ρ hρ)
      (fun ρ _ => (differentiable_refl s₀ R ρ).differentiableAt) hhs hhd
  have hsub : ball s₀ R' ⊆ closedBall s₀ R :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall hR'R.le)
  have hgne : ∀ z ∈ ball s₀ R', gfun s₀ R Z m h z ≠ 0 := by
    intro z hz
    simp only [gfun]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun ρ hρ => pow_ne_zero _ (hBne z (hsub hz) ρ hρ))
      (hh0 z (ball_subset_closedBall hz))
  have hLg := logDeriv_bound_of_zero_free hDL hr hrR' hM
    (differentiableOn_gfun_of_differentiableOn (hh.mono hsub)) hgne (fun z hz => hg z (hsub hz)) s hs
  have hLg' : ‖logDeriv (gfun s₀ R Z m h) s‖ ≤ 4 * (r + R') / (R' - r) ^ 2 * M := by
    rw [logDeriv_apply]
    exact hLg
  have hK : 0 ≤ R' / (R * (R - R')) := div_nonneg hR'.le (mul_pos hR (by linarith)).le
  have hlog : 0 < Real.log (R / R') := Real.log_pos ((one_lt_div hR').mpr hR'R)
  have hNle : ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) ≤ M / Real.log (R / R') := by
    exact (le_div_iff₀ hlog).mpr hN
  have hsumB : ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ ≤
      R' / (R * (R - R')) / Real.log (R / R') * M := by
    calc ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖
        ≤ ∑ ρ ∈ Z, ‖(m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sum_le _ _
      _ ≤ ∑ ρ ∈ Z, (m ρ : ℝ) * (R' / (R * (R - R'))) := by
          refine Finset.sum_le_sum fun ρ hρ => ?_
          rw [norm_mul]
          have hn : ‖(m ρ : ℂ)‖ = (m ρ : ℝ) := by
            exact Complex.norm_natCast _
          rw [hn]
          exact mul_le_mul_of_nonneg_left
            (norm_logDeriv_refl_le hR'R hR ((hZ ρ).1 hρ).1 hsR) (Nat.cast_nonneg _)
      _ = ((∑ ρ ∈ Z, m ρ : ℕ) : ℝ) * (R' / (R * (R - R'))) := by
          rw [Nat.cast_sum, Finset.sum_mul]
      _ ≤ M / Real.log (R / R') * (R' / (R * (R - R'))) :=
          mul_le_mul_of_nonneg_right hNle hK
      _ = R' / (R * (R - R')) / Real.log (R / R') * M := by ring
  have hdiff : logDeriv f s - ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) =
      logDeriv (gfun s₀ R Z m h) s -
        ∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s := by
    rw [hlf, hlg]
    ring
  rw [hdiff]
  calc _ ≤ ‖logDeriv (gfun s₀ R Z m h) s‖ +
        ‖∑ ρ ∈ Z, (m ρ : ℂ) * logDeriv (refl s₀ R ρ) s‖ := norm_sub_le _ _
    _ ≤ 4 * (r + R') / (R' - r) ^ 2 * M + R' / (R * (R - R')) / Real.log (R / R') * M :=
        add_le_add hLg' hsumB
    _ = locC r R' R * M := by
        unfold locC
        ring

end core

theorem local_abstract (hDF : PI.DiscFactor) (hDL : PI.DiscLog) {r R' R : ℝ} (hr : 0 < r)
    (hrR' : r < R') (hR'R : R' < R) (f : ℂ → ℂ) (s₀ : ℂ) (M : ℝ)
    (hf : AnalyticOnNhd ℂ f (closedBall s₀ R)) (hf0 : f s₀ ≠ 0) (hM : 0 ≤ M)
    (hb : ∀ s ∈ closedBall s₀ R, ‖f s‖ ≤ Real.exp M * ‖f s₀‖) :
    ({ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0}).Finite ∧
      ∀ s ∈ closedBall s₀ r, f s ≠ 0 →
        ‖logDeriv f s - ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0},
            (analyticOrderNatAt f ρ : ℂ) / (s - ρ)‖ ≤ locC r R' R * M := by
  have hR' : 0 < R' := hr.trans hrR'
  have hfd : DifferentiableOn ℂ f (closedBall s₀ R) := hf.differentiableOn
  obtain ⟨Z, m, h, hZ, -, hh, hh0, hfac⟩ := hDF f s₀ R R' hR' hR'R hfd hf0
  have hset : {ρ | ρ ∈ closedBall s₀ R' ∧ f ρ = 0} = (Z : Set ℂ) := by
    ext ρ
    simp only [Set.mem_ofPred_eq, Finset.mem_coe]
    exact (hZ ρ).symm
  have hord : ∀ ρ ∈ Z, analyticOrderNatAt f ρ = m ρ := by
    intro ρ hρ
    have hρR : ρ ∈ ball s₀ R := closedBall_subset_ball hR'R ((hZ ρ).1 hρ).1
    exact order_eq_of_factor hρ (isOpen_ball.mem_nhds hρR)
      (hf ρ (ball_subset_closedBall hρR)) (hh.mono ball_subset_closedBall)
      (hh0 ρ ((hZ ρ).1 hρ).1) fun z hz => hfac z (ball_subset_closedBall hz)
  refine ⟨by rw [hset]; exact Z.finite_toSet, ?_⟩
  intro s hs hfs
  have hsum : ∑ ρ ∈ Z, (analyticOrderNatAt f ρ : ℂ) / (s - ρ) = ∑ ρ ∈ Z, (m ρ : ℂ) / (s - ρ) :=
    Finset.sum_congr rfl fun ρ hρ => by rw [hord ρ hρ]
  rw [hset, finsum_mem_coe_finset, hsum]
  have hC : 0 < locC r R' R := locC_pos hr hrR' hR'R
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεC : 0 < ε / locC r R' R := div_pos hε hC
  have hM' : 0 < M + ε / locC r R' R := add_pos_of_nonneg_of_pos hM hεC
  have hb' : ∀ z ∈ closedBall s₀ R,
      ‖f z‖ ≤ Real.exp (M + ε / locC r R' R) * ‖f s₀‖ := fun z hz =>
    (hb z hz).trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith)) (norm_nonneg _))
  have key := core hDL hr hrR' hR'R hM' hZ hh hh0 hfac hb' s hs hfs
  have hCε : locC r R' R * (ε / locC r R' R) = ε := by
    exact mul_div_cancel₀ ε hC.ne'
  calc _ ≤ locC r R' R * (M + ε / locC r R' R) := key
    _ = locC r R' R * M + ε := by rw [mul_add, hCε]

end PI.EF.Loc
end
end

section
namespace PI.EF

theorem localAbstract_of (hDF : PI.DiscFactor) (hDL : PI.DiscLog) : LocalAbstract := by
  intro r R' R hr hrR' hR'R
  exact ⟨Loc.locC r R' R, Loc.locC_pos hr hrR' hR'R, fun f s₀ M hf hf0 hM hb =>
    Loc.local_abstract hDF hDL hr hrR' hR'R f s₀ M hf hf0 hM hb⟩

end PI.EF
end

section
noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

lemma one_le_level (N : ℕ) [NeZero N] : (1 : ℝ) ≤ N := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)

def LL (N : ℕ) (t : ℝ) : ℝ := Real.log (N * (|t| + 2))

lemma two_le_arg (N : ℕ) [NeZero N] (t : ℝ) : (2 : ℝ) ≤ N * (|t| + 2) := by
  have h1 := one_le_level N
  have h2 : (2 : ℝ) ≤ |t| + 2 := by linarith [abs_nonneg t]
  calc (2 : ℝ) = 1 * 2 := by ring
    _ ≤ N * (|t| + 2) := mul_le_mul h1 h2 (by norm_num) (by linarith)

lemma log_two_le_LL (N : ℕ) [NeZero N] (t : ℝ) : Real.log 2 ≤ LL N t := Real.log_le_log (by norm_num) (two_le_arg N t)

lemma one_le_two_LL (N : ℕ) [NeZero N] (t : ℝ) : 1 ≤ 2 * LL N t := by
  have h1 := log_two_le_LL N t
  have h2 := Real.log_two_gt_d9
  linarith

lemma Lent_eq (χ : DirichletCharacter ℂ N) {z : ℂ} (hz : z ≠ 1) :
    Lent χ z = (1 + del1 χ * (z - 2)) * LFunction χ z := by
  unfold Lent del1
  split_ifs with h
  · subst h
    have e : DirichletCharacter.LFunctionTrivChar₁ N z =
        (z - 1) * DirichletCharacter.LFunctionTrivChar N z := by
      simp [DirichletCharacter.LFunctionTrivChar₁, hz]
    rw [e]
    show (z - 1) * LFunction 1 z = (1 + 1 * (z - 2)) * LFunction 1 z
    ring
  · simp

lemma Lent_bound_ne {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) (hz : z ≠ 1) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  rw [Lent_eq χ hz]
  refine (hG N χ hχ z h1 h2).trans ?_
  have hN := one_le_level N
  have hb : (N : ℝ) * (|z.im| + 2) ≤ 4 * (N * (|t| + 2)) := by
    have := mul_le_mul_of_nonneg_left (show |z.im| + 2 ≤ 4 * (|t| + 2) by linarith [abs_nonneg t])
      (show (0 : ℝ) ≤ N by linarith)
    linarith
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hb hA.le) hC.le

lemma Lent_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {z : ℂ} (h1 : -4 ≤ z.re)
    (h2 : z.re ≤ 8) (h3 : |z.im| ≤ |t| + 6) :
    ‖Lent χ z‖ ≤ C * (4 * (N * (|t| + 2))) ^ A := by
  by_cases hz : z = 1
  · subst hz
    have hcont : Continuous (Lent χ) := by
      unfold Lent
      split_ifs with h
      · exact (DirichletCharacter.differentiable_LFunctionTrivChar₁ N).continuous
      · exact (DirichletCharacter.differentiable_LFunction h).continuous
    have hc : Continuous (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) :=
      (hcont.comp (continuous_const.add Complex.continuous_ofReal)).norm
    have h0 : ‖Lent χ 1‖ = ‖Lent χ (1 + ((0 : ℝ) : ℂ))‖ := by simp
    have hT : Filter.Tendsto (fun x : ℝ => ‖Lent χ (1 + (x : ℂ))‖) (nhdsWithin (0 : ℝ) {0}ᶜ)
        (nhds ‖Lent χ 1‖) := by
      rw [h0]
      exact (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    refine le_of_tendsto hT ?_
    have hmem : Set.Ioo (-1 : ℝ) 1 ∈ nhdsWithin (0 : ℝ) {0}ᶜ :=
      nhdsWithin_le_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
    filter_upwards [hmem, self_mem_nhdsWithin] with x hx hx0
    have hx1 : (1 + (x : ℂ)) ≠ 1 := by
      intro h
      apply hx0
      have h' := congrArg Complex.re h
      simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re] at h'
      show x = 0
      linarith
    refine Lent_bound_ne hA hC hG hχ ?_ ?_ ?_ hx1
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.1]
    · simp only [Complex.add_re, Complex.one_re, Complex.ofReal_re]
      linarith [hx.2]
    · simp only [Complex.add_im, Complex.one_im, Complex.ofReal_im, add_zero, abs_zero]
      positivity
  · exact Lent_bound_ne hA hC hG hχ h1 h2 h3 hz

def ctr (t : ℝ) : ℂ := 2 + t * I

@[simp] lemma ctr_re (t : ℝ) : (ctr t).re = 2 := by
  simp [ctr]
@[simp] lemma ctr_im (t : ℝ) : (ctr t).im = t := by
  simp [ctr]

lemma ctr_ne_one (t : ℝ) : ctr t ≠ 1 := by
  intro h
  have h' := congrArg Complex.re h
  rw [ctr_re] at h'
  norm_num at h'

lemma half_le_norm_Lent_ctr (hI : PI.LInvRight) (χ : DirichletCharacter ℂ N) (t : ℝ) :
    1 / 2 ≤ ‖Lent χ (ctr t)‖ := by
  have hL := hI N χ (ctr t) (by rw [ctr_re]; norm_num)
  have h21 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  rw [ctr_re, h21] at hL
  have hne := DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (s := ctr t)
    (Or.inr (ctr_ne_one t)) (by rw [ctr_re]; norm_num)
  have hpos : 0 < ‖LFunction χ (ctr t)‖ := norm_pos_iff.mpr hne
  have hL2 : 1 / 2 ≤ ‖LFunction χ (ctr t)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hL hpos.le
    rw [mul_inv_cancel₀ hpos.ne'] at h1
    linarith
  rw [Lent_eq χ (ctr_ne_one t), norm_mul]
  have hf : 1 ≤ ‖1 + del1 χ * (ctr t - 2)‖ := by
    have hre : (1 + del1 χ * (ctr t - 2)).re = 1 := by
      unfold del1 ctr
      split_ifs <;> norm_num
    have := Complex.abs_re_le_norm (1 + del1 χ * (ctr t - 2))
    rw [hre, abs_one] at this
    exact this
  have := mul_le_mul hf hL2 (by norm_num) (by positivity)
  linarith

def Mfun (A C : ℝ) (N : ℕ) (t : ℝ) : ℝ := |Real.log (2 * C)| + A * Real.log (4 * (N * (|t| + 2)))

lemma Mfun_nonneg {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) : 0 ≤ Mfun A C N t := by
  unfold Mfun
  have h := two_le_arg N t
  have h3 : 0 ≤ Real.log (4 * (N * (|t| + 2))) := Real.log_nonneg (by linarith)
  have h4 := abs_nonneg (Real.log (2 * C))
  have h5 := mul_nonneg hA.le h3
  linarith

lemma Mfun_le {A C : ℝ} (hA : 0 < A) (N : ℕ) [NeZero N] (t : ℝ) :
    Mfun A C N t ≤ (2 * |Real.log (2 * C)| + 3 * A) * LL N t := by
  unfold Mfun
  have hX : (0 : ℝ) < N * (|t| + 2) := by linarith [two_le_arg N t]
  have h4 : Real.log (4 * (N * (|t| + 2))) = Real.log 4 + LL N t := by
    rw [Real.log_mul (by norm_num) hX.ne']
    rfl
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h1 := one_le_two_LL N t
  have h2 := log_two_le_LL N t
  have ha := abs_nonneg (Real.log (2 * C))
  rw [h4, hl4]
  nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hA.le]

lemma le_exp_Mfun {A C : ℝ} (hC : 0 < C) (N : ℕ) [NeZero N] (t : ℝ) :
    2 * C * (4 * (N * (|t| + 2))) ^ A ≤ Real.exp (Mfun A C N t) := by
  unfold Mfun
  have hY : (0 : ℝ) < 4 * (N * (|t| + 2)) := by linarith [two_le_arg N t]
  rw [Real.exp_add, Real.rpow_def_of_pos hY, mul_comm (Real.log (4 * (N * (|t| + 2)))) A]
  have h2C : 2 * C ≤ Real.exp |Real.log (2 * C)| := by
    calc 2 * C = Real.exp (Real.log (2 * C)) := (Real.exp_log (by linarith)).symm
      _ ≤ _ := Real.exp_le_exp.mpr (le_abs_self _)
  exact mul_le_mul_of_nonneg_right h2C (Real.exp_pos _).le

theorem Lent_disc_bound {A C : ℝ} (hA : 0 < A) (hC : 0 < C) (hG : LGrowth A C) (hI : PI.LInvRight)
    {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) (t : ℝ) :
    ∀ z ∈ closedBall (ctr t) 6, ‖Lent χ z‖ ≤ Real.exp (Mfun A C N t) * ‖Lent χ (ctr t)‖ := by
  intro z hz
  have hz' : ‖z - ctr t‖ ≤ 6 := by rwa [Metric.mem_closedBall, dist_eq_norm] at hz
  have hre := (Complex.abs_re_le_norm (z - ctr t)).trans hz'
  have him := (Complex.abs_im_le_norm (z - ctr t)).trans hz'
  rw [Complex.sub_re, ctr_re] at hre
  rw [Complex.sub_im, ctr_im] at him
  have h1 : -4 ≤ z.re := by linarith [neg_abs_le (z.re - 2)]
  have h2 : z.re ≤ 8 := by linarith [le_abs_self (z.re - 2)]
  have h3 : |z.im| ≤ |t| + 6 := by
    have := abs_sub_abs_le_abs_sub z.im t
    linarith
  have hb := Lent_bound hA hC hG hχ h1 h2 h3
  have he := le_exp_Mfun (A := A) hC N t
  have hh := half_le_norm_Lent_ctr hI χ t
  have hE := Real.exp_pos (Mfun A C N t)
  have hP : 0 ≤ C * (4 * (N * (|t| + 2))) ^ A := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hh hE.le]

end PI.EF
end
end

section
noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

def DZ (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ := {ρ | ρ ∈ closedBall (ctr t) (11 / 4) ∧ Lent χ ρ = 0}

lemma norm_sub_ctr_sq (ρ : ℂ) (t : ℝ) : ‖ρ - ctr t‖ ^ 2 = (ρ.re - 2) ^ 2 + (ρ.im - t) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, ctr_re, ctr_im]
  ring

private lemma Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one (χ : DirichletCharacter ℂ N) {ρ : ℂ} (hρ : ρ ≠ 1) :
    Lent χ ρ = 0 ↔ LFunction χ ρ = 0 := by
  unfold Lent
  split_ifs with h
  · subst h
    simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hρ, sub_eq_zero]
  · exact Iff.rfl

lemma DZ_facts (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ} {ρ : ℂ}
    (hρ : ρ ∈ DZ χ t) :
    ρ ≠ 1 ∧ LFunction χ ρ = 0 ∧ |ρ.im - t| ≤ 3 ∧
      ((0 < ρ.re ∧ ρ.re < 1) ∨ (ρ = 0 ∧ χ.Even ∧ χ ≠ 1)) := by
  obtain ⟨hb, hz⟩ := hρ
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  have hsq := norm_sub_ctr_sq ρ t
  have hn := norm_nonneg (ρ - ctr t)
  have hx2 : ‖ρ - ctr t‖ ^ 2 ≤ (11 / 4) ^ 2 := by nlinarith
  have hre : -3 / 4 ≤ ρ.re := by nlinarith [sq_nonneg (ρ.im - t)]
  have him : |ρ.im - t| ≤ 3 := by
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (ρ.re - 2)]
  have hne : ρ ≠ 1 := by
    rintro rfl
    unfold Lent at hz
    split_ifs at hz with h
    · subst h
      first
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero _ hz
        | exact DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero hz
    · exact DirichletCharacter.LFunction_apply_one_ne_zero h hz
  have hL : LFunction χ ρ = 0 := (Lent_eq_zero_iff_LFunction_eq_zero_of_ne_one χ hne).1 hz
  refine ⟨hne, hL, him, ?_⟩
  rcases hZL N χ hχ ρ (by linarith) hne hL with h | h | ⟨rfl, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · norm_num at hre

lemma far_sum_le {Cw : ℝ} (hW : ZerosWindowWith Cw) (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) {t : ℝ} (s : ℂ) (hs : s.im = t) (E : Finset ℂ)
    (hE : ∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) :
    ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤
      Cw * Real.log (N * (|t + 2| + 2)) + Cw * Real.log (N * (|t - 2| + 2)) := by
  classical
  have hE' : ∀ ρ ∈ E, 1 ≤ ‖s - ρ‖ ∧ (ρ ∈ ZerosNear χ (t + 2) ∨ ρ ∈ ZerosNear χ (t - 2)) := by
    intro ρ hρ
    obtain ⟨hD, hN, h0⟩ := hE ρ hρ
    obtain ⟨-, hL, him, hcase⟩ := DZ_facts hZL hχ hD
    have hstrip : 0 < ρ.re ∧ ρ.re < 1 := by
      rcases hcase with h | ⟨h, -⟩
      · exact h
      · exact absurd h h0
    have hfar : 1 < |ρ.im - t| := by
      by_contra hc
      push_neg at hc
      exact hN ⟨hstrip.1, hstrip.2, hc, hL⟩
    refine ⟨?_, ?_⟩
    · calc (1 : ℝ) ≤ |ρ.im - t| := hfar.le
        _ = |(s - ρ).im| := by rw [Complex.sub_im, hs, abs_sub_comm]
        _ ≤ ‖s - ρ‖ := Complex.abs_im_le_norm _
    · rcases le_or_gt 0 (ρ.im - t) with h | h
      · left
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_nonneg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
      · right
        refine ⟨hstrip.1, hstrip.2, ?_, hL⟩
        rw [abs_of_neg h] at hfar him
        rw [abs_le]
        constructor <;> linarith
  obtain ⟨hfinP, hsumP⟩ := hW N χ hχ (t + 2)
  obtain ⟨hfinM, hsumM⟩ := hW N χ hχ (t - 2)
  have step1 : ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ ≤ ∑ ρ ∈ E, (mult χ ρ : ℝ) := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ρ hρ => ?_)
    rw [norm_div]
    have h1 := (hE' ρ hρ).1
    have hc : ‖(mult χ ρ : ℂ)‖ = (mult χ ρ : ℝ) := by
      first
        | exact Complex.norm_natCast _
        | simp
    rw [hc]
    exact div_le_self (Nat.cast_nonneg _) h1
  have step2 : ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤
      ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
    have hsub : E ⊆ hfinP.toFinset ∪ hfinM.toFinset := by
      intro ρ hρ
      rw [Finset.mem_union, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
      exact (hE' ρ hρ).2
    calc ∑ ρ ∈ E, (mult χ ρ : ℝ) ≤ ∑ ρ ∈ hfinP.toFinset ∪ hfinM.toFinset, (mult χ ρ : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) + ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) := by
          rw [← Finset.sum_union_inter]
          exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)
  have hP : ∑ ρ ∈ hfinP.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t + 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t + 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinP).symm
      _ ≤ _ := hsumP
  have hM : ∑ ρ ∈ hfinM.toFinset, (mult χ ρ : ℝ) ≤ Cw * Real.log (N * (|t - 2| + 2)) := by
    calc _ = ∑ᶠ ρ ∈ ZerosNear χ (t - 2), (mult χ ρ : ℝ) :=
          (finsum_mem_eq_finite_toFinset_sum _ hfinM).symm
      _ ≤ _ := hsumM
  linarith

lemma zero_term_le (hZL : ZeroLocus) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive) {t : ℝ}
    (s : ℂ) (hs : s.im = t) :
    ‖(open Classical in if (0 : ℂ) ∈ DZ χ t then (mult χ 0 : ℂ) / (s - 0) else 0) - eps0 χ / s‖
      ≤ 1 := by
  classical
  by_cases h0 : (0 : ℂ) ∈ DZ χ t
  · obtain ⟨-, hL, -, h⟩ := DZ_facts hZL hχ h0
    rcases h with h | h
    · simp at h
    · obtain ⟨-, he, h1⟩ := h
      have hm := (mult_zero_of_even hχ he h1).2
      simp only [h0, if_true, mult, hm, eps0, he, h1, ne_eq, not_false_eq_true, and_self, sub_zero]
      simp
  · simp only [h0, if_false, zero_sub, norm_neg]
    unfold eps0
    split_ifs with he
    · have hL := (mult_zero_of_even hχ he.1 he.2).1
      have h0' : ¬ ((0 : ℂ) ∈ closedBall (ctr t) (11 / 4)) := by
        intro hb
        exact h0 ⟨hb, (Lent_eq_zero_iff χ (by norm_num)).2 hL⟩
      rw [mem_closedBall, dist_eq_norm, not_le, zero_sub] at h0'
      have h1 := norm_sub_ctr_sq 0 t
      simp only [zero_re, zero_im, zero_sub] at h1
      have h2 : 1 < t ^ 2 := by nlinarith [norm_nonneg (-ctr t)]
      have h3 : 1 ≤ ‖s‖ := by
        have h4 := Complex.abs_im_le_norm s
        rw [hs] at h4
        have h5 : 1 < |t| := by
          by_contra h6
          have := abs_le.1 (not_lt.1 h6)
          nlinarith
        linarith
      rw [norm_div, norm_one]
      exact div_le_one_of_le₀ h3 (norm_nonneg _)
    · simp

end PI.EF
end
end

section
noncomputable section

namespace PI.EF

open Complex Metric Filter Topology Set DirichletCharacter

variable {N : ℕ} [NeZero N]

lemma log_window_le (N : ℕ) [NeZero N] {t u : ℝ} (hu : |u| ≤ |t| + 2) :
    Real.log (N * (|u| + 2)) ≤ 2 * LL N t := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne N)
  have ht := abs_nonneg t
  have hu0 := abs_nonneg u
  rw [LL.eq_1]
  have hpos : 0 < (N : ℝ) * (|u| + 2) := by positivity
  have h1 : (N : ℝ) * (|u| + 2) ≤ N * (|t| + 4) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h2 : |t| + 4 ≤ (|t| + 2) ^ 2 := by nlinarith
  have h3 : (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := by
    calc (N : ℝ) * (|t| + 4) ≤ (N : ℝ) ^ 2 * (|t| + 4) :=
          mul_le_mul_of_nonneg_right (by nlinarith) (by linarith)
      _ ≤ (N : ℝ) ^ 2 * (|t| + 2) ^ 2 := mul_le_mul_of_nonneg_left h2 (by positivity)
  calc Real.log (N * (|u| + 2)) ≤ Real.log ((N * (|t| + 2)) ^ 2) :=
        Real.log_le_log hpos (by rw [mul_pow]; linarith)
    _ = 2 * Real.log (N * (|t| + 2)) := by rw [Real.log_pow]; norm_num

theorem mem_ball_ctr (s : ℂ) (h1 : -1 / 2 ≤ s.re) (h2 : s.re ≤ 3) :
    s ∈ closedBall (ctr s.im) (5 / 2) := by
  rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
  have h : s - (2 + (s.im : ℂ) * Complex.I) = ((s.re - 2 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp
  rw [h, Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> linarith

lemma sum_DZ_eq {χ : DirichletCharacter ℂ N} (t : ℝ)
    (hfin : (DZ χ t).Finite) (F : ℂ → ℂ) :
    ∃ E : Finset ℂ, (∀ ρ ∈ E, ρ ∈ DZ χ t ∧ ρ ∉ ZerosNear χ t ∧ ρ ≠ 0) ∧
      ∑ᶠ ρ ∈ DZ χ t, F ρ = ∑ᶠ ρ ∈ ZerosNear χ t, F ρ + ∑ ρ ∈ E, F ρ +
        (open Classical in if (0 : ℂ) ∈ DZ χ t then F 0 else 0) := by
  classical
  have hsub : ZerosNear χ t ⊆ DZ χ t := by
    intro ρ hρ
    rw [ZerosNear.eq_1] at hρ
    obtain ⟨h0, h1, him, hL⟩ := hρ
    rw [DZ.eq_1, Set.mem_setOf_eq]
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, ctr.eq_1, Complex.dist_eq]
      have hre : (ρ - (2 + (t : ℂ) * Complex.I)).re = ρ.re - 2 := by simp
      have him' : (ρ - (2 + (t : ℂ) * Complex.I)).im = ρ.im - t := by simp
      obtain ⟨ha, hb⟩ := abs_le.mp him
      rw [← sq_le_sq₀ (norm_nonneg _) (by norm_num), Complex.sq_norm, Complex.normSq_apply,
        hre, him']
      nlinarith
    · have hne : ρ ≠ 1 := by
        intro h
        rw [h] at h1
        norm_num at h1
      rw [Lent.eq_1]
      split_ifs with hχ
      · subst hχ
        have key : DirichletCharacter.LFunctionTrivChar₁ N ρ =
            (ρ - 1) * DirichletCharacter.LFunctionTrivChar N ρ := by
          first
          | simp [DirichletCharacter.LFunctionTrivChar₁, Function.update_apply, hne]
          | (unfold DirichletCharacter.LFunctionTrivChar₁; rw [Function.update_of_ne hne])
          | exact DirichletCharacter.LFunctionTrivChar₁_apply_ne_one N hne
        rw [key]
        exact mul_eq_zero_of_right _ hL
      · exact hL
  have h0Z : (0 : ℂ) ∉ ZerosNear χ t := by
    intro h
    rw [ZerosNear.eq_1] at h
    obtain ⟨h0, -⟩ := h
    simp at h0
  have hZ : (ZerosNear χ t).Finite := hfin.subset hsub
  refine ⟨(hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter (fun ρ => ρ ≠ 0), ?_, ?_⟩
  · intro ρ hρ
    simp only [Finset.mem_filter, Set.Finite.mem_toFinset] at hρ
    exact ⟨hρ.1.1, hρ.1.2, hρ.2⟩
  · rw [finsum_mem_eq_finite_toFinset_sum F hfin, finsum_mem_eq_finite_toFinset_sum F hZ,
      ← Finset.sum_filter_add_sum_filter_not hfin.toFinset (fun ρ => ρ ∈ ZerosNear χ t)]
    have e1 : hfin.toFinset.filter (fun ρ => ρ ∈ ZerosNear χ t) = hZ.toFinset := by
      ext ρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset]
      exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
    rw [e1, add_assoc]
    congr 1
    rw [← Finset.sum_filter_add_sum_filter_not
      (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)) (fun ρ => ρ ≠ 0)]
    congr 1
    split_ifs with hD
    · have e2 : (hfin.toFinset.filter (fun ρ => ρ ∉ ZerosNear χ t)).filter
          (fun ρ => ¬ ρ ≠ 0) = {0} := by
        ext ρ
        simp only [Finset.mem_filter, Set.Finite.mem_toFinset, Finset.mem_singleton, ne_eq,
          not_not]
        constructor
        · rintro ⟨-, h⟩
          exact h
        · rintro rfl
          exact ⟨⟨hD, h0Z⟩, rfl⟩
      rw [e2, Finset.sum_singleton]
    · apply Finset.sum_eq_zero
      intro ρ hρ
      simp only [Finset.mem_filter, Set.Finite.mem_toFinset, ne_eq, not_not] at hρ
      exact absurd (hρ.2 ▸ hρ.1.1) hD

theorem localLemma_of (hI : PI.LInvRight) : GlueLocalLemma := by
  intro hLA hG hZL hW
  obtain ⟨A, C, hA, hC, hG⟩ := hG
  obtain ⟨Cw, hCw, hW⟩ := hW
  obtain ⟨C₀, hC₀, hloc⟩ := hLA (5 / 2) (11 / 4) 6 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2, by positivity, ?_⟩
  intro N _ χ hχ s h1 h2 hLs hs1
  have hc0 : Lent χ (ctr s.im) ≠ 0 := by
    have := half_le_norm_Lent_ctr hI χ s.im
    exact norm_pos_iff.1 (lt_of_lt_of_le (by norm_num) this)
  obtain ⟨hfin, hbound⟩ := hloc (Lent χ) (ctr s.im) (Mfun A C N s.im)
    (fun z _ => (differentiable_Lent χ).analyticAt z) hc0 (Mfun_nonneg hA N s.im)
    (Lent_disc_bound hA hC hG hI hχ s.im)
  have hLs' : Lent χ s ≠ 0 := fun h => hLs ((Lent_eq_zero_iff χ hs1).1 h)
  have hb := hbound s (mem_ball_ctr s h1 h2) hLs'
  have hfin' : (DZ χ s.im).Finite := hfin
  have econgr : ∑ᶠ ρ ∈ {ρ | ρ ∈ closedBall (ctr s.im) (11 / 4) ∧ Lent χ ρ = 0},
      (analyticOrderNatAt (Lent χ) ρ : ℂ) / (s - ρ) =
      ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ) :=
    finsum_mem_congr rfl (fun ρ hρ => by rw [order_Lent χ (DZ_facts hZL hχ hρ).1])
  rw [econgr] at hb
  obtain ⟨E, hE, hdec⟩ := sum_DZ_eq s.im hfin' (fun ρ => (mult χ ρ : ℂ) / (s - ρ))
  have hfar := far_sum_le hW hZL hχ s rfl E hE
  have hzero := zero_term_le hZL hχ s rfl
  have hM := Mfun_le (C := C) hA N s.im
  have hw1 := log_window_le N (t := s.im) (u := s.im + 2)
    ((abs_add_le _ _).trans (by norm_num))
  have hw2 := log_window_le N (t := s.im) (u := s.im - 2)
    ((abs_sub _ _).trans (by norm_num))
  have hL1 := one_le_two_LL N s.im
  have key : logDeriv (LFunction χ) s - ∑ᶠ ρ ∈ ZerosNear χ s.im, (mult χ ρ : ℂ) / (s - ρ) -
      eps0 χ / s + del1 χ / (s - 1) =
      (logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)) +
        ∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ) +
        ((open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s) := by
    rw [logDeriv_Lent χ hs1 hLs, hdec]
    ring
  rw [key]
  have hMnn := Mfun_nonneg (C := C) hA N s.im
  calc _ ≤ ‖logDeriv (Lent χ) s - ∑ᶠ ρ ∈ DZ χ s.im, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖∑ ρ ∈ E, (mult χ ρ : ℂ) / (s - ρ)‖ +
        ‖(open Classical in if (0 : ℂ) ∈ DZ χ s.im then (mult χ 0 : ℂ) / (s - 0) else 0) -
          eps0 χ / s‖ := norm_add₃_le
    _ ≤ C₀ * Mfun A C N s.im + (Cw * Real.log (N * (|s.im + 2| + 2)) +
        Cw * Real.log (N * (|s.im - 2| + 2))) + 1 := add_le_add (add_le_add hb hfar) hzero
    _ ≤ C₀ * ((2 * |Real.log (2 * C)| + 3 * A) * LL N s.im) +
        (Cw * (2 * LL N s.im) + Cw * (2 * LL N s.im)) + 2 * LL N s.im := by
        gcongr
    _ = (C₀ * (2 * |Real.log (2 * C)| + 3 * A) + 4 * Cw + 2) * Real.log (N * (|s.im| + 2)) := by
        unfold LL
        ring

end PI.EF
end
end

section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

variable {N : ℕ} [NeZero N]

theorem L_right (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ1 : χ ≠ 1) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 8) :
    ‖LFunction χ w‖ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by
  have hre : 0 < w.re := by linarith
  have hb := hB N χ hχ1 w hre
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg w.im
  have hw : ‖w‖ ≤ 8 + |w.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im w).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hq : ‖w‖ / w.re ≤ 2 * (8 + |w.im|) := by
    rw [div_le_iff₀ hre]
    nlinarith [norm_nonneg w]
  calc ‖LFunction χ w‖ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + ‖w‖ / w.re) := hb
    _ ≤ 1 + 2 * ((N : ℝ) + 1) * (1 + 2 * (8 + |w.im|)) := by gcongr
    _ ≤ 37 * ((N : ℝ) * (|w.im| + 2)) := by nlinarith

theorem L_nontriv_growth (hB : PI.LBoundRight) {χ : DirichletCharacter ℂ N} (hχ : χ.IsPrimitive)
    (hχ1 : χ ≠ 1) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
  have hN : (1 : ℝ) ≤ N := by exact_mod_cast Nat.one_le_iff_ne_zero.2 (NeZero.ne N)
  have ht := abs_nonneg s.im
  have hX : (1 : ℝ) ≤ (N : ℝ) * (|s.im| + 2) := one_le_mul_of_one_le_of_one_le hN (by linarith)
  by_cases hr : 1 / 2 ≤ s.re
  · calc ‖LFunction χ s‖ ≤ 37 * ((N : ℝ) * (|s.im| + 2)) := L_right hB hχ1 hr h2
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
        have : (N : ℝ) * (|s.im| + 2) ≤ ((N : ℝ) * (|s.im| + 2)) ^ 7 := le_self_pow₀ hX (by norm_num)
        nlinarith
  · push_neg at hr
    have h0 : χ 0 = 0 := by
      by_cases hN1 : N = 1
      · subst hN1
        exfalso
        apply hχ1
        exact MulChar.ext fun a => by rw [Subsingleton.elim a 1]; simp
      · haveI : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
        exact χ.map_nonunit not_isUnit_zero
    have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
    have hL1 := norm_L_one_sub_le hχ hw1 hw2 (Or.inl h0)
    rw [sub_sub_cancel] at hL1
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.2 hχ1
    have hL2 := L_right hB hinv hw1 (by simp only [Complex.sub_re, Complex.one_re]; linarith)
    have hwim : |(1 - s).im| = |s.im| := by simp
    rw [hwim] at hL2
    have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      have e : |(1 - s + 1).im| = |s.im| := by simp
      have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
      rw [e, e2, abs_of_pos (by linarith)]
      linarith
    calc ‖LFunction χ s‖ ≤ 6 * (N : ℝ) ^ 5 * ‖1 - s + 1‖ ^ 5 * ‖LFunction χ⁻¹ (1 - s)‖ := hL1
      _ ≤ 6 * (N : ℝ) ^ 5 * (6 + |s.im|) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by gcongr
      _ ≤ 6 * (N : ℝ) ^ 5 * (3 * (|s.im| + 2)) ^ 5 * (37 * ((N : ℝ) * (|s.im| + 2))) := by
          gcongr
          linarith
      _ = 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 6 := by ring
      _ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hX (by norm_num)) (by norm_num)

theorem lGrowth_of (hB : PI.LBoundRight) {C : ℝ} (hZ : ZetaGrowth C) :
    LGrowth 7 (max C 53946) := by
  intro N _ χ hχ s h1 h2
  have e7 : ∀ x : ℝ, x ^ (7 : ℝ) = x ^ (7 : ℕ) := fun x => by
    rw [show (7 : ℝ) = ((7 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [e7]
  by_cases hc : χ = 1
  · subst hc
    have hN : N = 1 := by
      have h0 := hχ
      rw [DirichletCharacter.IsPrimitive, DirichletCharacter.conductor_one] at h0
      exact h0.symm
    subst hN
    simp only [del1, ↓reduceIte, one_mul]
    rw [show (1 : ℂ) + (s - 2) = s - 1 by ring, DirichletCharacter.LFunction_modOne_eq]
    refine le_trans (hZ s h1 h2) ?_
    simp only [Nat.cast_one, one_mul]
    gcongr
    exact le_max_left _ _
  · simp only [del1, hc, ↓reduceIte, zero_mul, add_zero, one_mul]
    calc ‖LFunction χ s‖ ≤ 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := L_nontriv_growth hB hχ hc h1 h2
      _ ≤ max C 53946 * ((N : ℝ) * (|s.im| + 2)) ^ 7 := by
          gcongr
          exact le_max_right _ _

end PI.EF
end
end

section
noncomputable section

namespace PI.EF

open Complex DirichletCharacter

theorem zeta_one_sub_le {w : ℂ} (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5) (h : w ≠ 1) :
    ‖riemannZeta (1 - w)‖ ≤ 6 * ‖w + 1‖ ^ 5 * ‖riemannZeta w‖ := by
  have hp : (1 : DirichletCharacter ℂ 1).IsPrimitive := DirichletCharacter.isPrimitive_one_level_one
  have h0 := norm_L_one_sub_le (N := 1) hp h1 h2 (Or.inr h)
  simpa [DirichletCharacter.LFunction_modOne_eq] using h0

theorem zeta_right (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : 1 / 2 ≤ s.re) (h2 : s.re ≤ 8) :
    ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := by
  by_cases hs : s = 1
  · subst hs
    simp only [sub_self, zero_mul, norm_zero]
    positivity
  have hre : 0 < s.re := by linarith
  have hb := hZ s hre hs
  have hn1 : 0 < ‖s - 1‖ := norm_pos_iff.2 (sub_ne_zero.2 hs)
  have ht := abs_nonneg s.im
  have hs_le : ‖s‖ ≤ 8 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im s).trans ?_
    rw [abs_of_pos hre]
    linarith
  have hs1_le : ‖s - 1‖ ≤ 7 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, sub_zero]
    have : |s.re - 1| ≤ 7 := by rw [abs_le]; constructor <;> linarith
    linarith
  have hinv : 1 / s.re ≤ 2 := by rw [div_le_iff₀ hre]; linarith
  rw [norm_mul]
  calc ‖s - 1‖ * ‖riemannZeta s‖ ≤ ‖s - 1‖ * (1 + 1 / ‖s - 1‖ + ‖s‖ * (1 + 1 / s.re)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = ‖s - 1‖ + 1 + ‖s - 1‖ * ‖s‖ * (1 + 1 / s.re) := by
        rw [mul_add, mul_add, mul_one_div_cancel hn1.ne']
        ring
    _ ≤ (7 + |s.im|) + 1 + (7 + |s.im|) * (8 + |s.im|) * (1 + 2) := by gcongr
    _ ≤ 51 * (|s.im| + 2) ^ 2 := by nlinarith

theorem zeta_left (hZ : PI.ZetaBoundRight) {s : ℂ} (h1 : -4 ≤ s.re) (h2 : s.re < 1 / 2)
    (h3 : 1 / 2 ≤ ‖s‖) : ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := by
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at h3
    norm_num at h3
  have hw1 : 1 / 2 ≤ (1 - s).re := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw2 : (1 - s).re ≤ 5 := by simp only [Complex.sub_re, Complex.one_re]; linarith
  have hw : (1 - s) ≠ 1 := by
    intro h0
    apply hs0
    linear_combination -h0
  have hz1 := zeta_one_sub_le hw1 hw2 hw
  rw [sub_sub_cancel] at hz1
  have hwre : 0 < (1 - s).re := by linarith
  have hz2 := hZ (1 - s) hwre hw
  have ht := abs_nonneg s.im
  have hwim : |(1 - s).im| = |s.im| := by simp
  have hn : ‖1 - s - 1‖ = ‖s‖ := by rw [show 1 - s - 1 = -s by ring, norm_neg]
  have hinv1 : 1 / ‖1 - s - 1‖ ≤ 2 := by
    rw [hn, div_le_iff₀ (by linarith)]
    linarith
  have hinv2 : 1 / (1 - s).re ≤ 2 := by rw [div_le_iff₀ hwre]; linarith
  have hw_le : ‖1 - s‖ ≤ 5 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hwim, abs_of_pos hwre]
    linarith
  have hw1_le : ‖1 - s + 1‖ ≤ 6 + |s.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    have e : |(1 - s + 1).im| = |s.im| := by simp
    have e2 : (1 - s + 1).re = (1 - s).re + 1 := by simp
    rw [e, e2, abs_of_pos (by linarith)]
    linarith
  have hzw : ‖riemannZeta (1 - s)‖ ≤ 18 + 3 * |s.im| := by
    calc ‖riemannZeta (1 - s)‖ ≤ 1 + 1 / ‖1 - s - 1‖ + ‖1 - s‖ * (1 + 1 / (1 - s).re) := hz2
      _ ≤ 1 + 2 + (5 + |s.im|) * (1 + 2) := by gcongr
      _ = 18 + 3 * |s.im| := by ring
  have hsn : ‖s - 1‖ = ‖1 - s‖ := norm_sub_rev _ _
  rw [norm_mul, hsn]
  calc ‖1 - s‖ * ‖riemannZeta s‖ ≤ ‖1 - s‖ * (6 * ‖1 - s + 1‖ ^ 5 * ‖riemannZeta (1 - s)‖) := by gcongr
    _ ≤ (5 + |s.im|) * (6 * (6 + |s.im|) ^ 5 * (18 + 3 * |s.im|)) := by gcongr
    _ ≤ (3 * (|s.im| + 2)) * (6 * (3 * (|s.im| + 2)) ^ 5 * (9 * (|s.im| + 2))) := by
        gcongr <;> linarith
    _ = 39366 * (|s.im| + 2) ^ 7 := by ring
    _ ≤ 48114 * (|s.im| + 2) ^ 7 := by gcongr; norm_num

theorem zetaGrowth_of (hZ : PI.ZetaBoundRight) : ZetaGrowth 300000 := by
  intro s hs1 hs2
  have ht := abs_nonneg s.im
  have h2 : (2 : ℝ) ≤ |s.im| + 2 := by linarith
  by_cases hr : 1 / 2 ≤ s.re
  · have hp7 : (|s.im| + 2) ^ 2 ≤ (|s.im| + 2) ^ 7 := pow_le_pow_right₀ (by linarith) (by norm_num)
    calc ‖(s - 1) * riemannZeta s‖ ≤ 51 * (|s.im| + 2) ^ 2 := zeta_right hZ hr hs2
      _ ≤ 300000 * (|s.im| + 2) ^ 7 := by nlinarith [pow_nonneg (by linarith : (0 : ℝ) ≤ |s.im| + 2) 2]
  · push_neg at hr
    by_cases hn : 1 / 2 ≤ ‖s‖
    · calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (|s.im| + 2) ^ 7 := zeta_left hZ hs1 hr hn
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr; norm_num
    · push_neg at hn
      have hK : ∀ z ∈ frontier (Metric.ball (0 : ℂ) (1 / 2)),
          ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by
        intro z hz
        rw [frontier_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0), mem_sphere_zero_iff_norm] at hz
        have hre : |z.re| ≤ 1 / 2 := (Complex.abs_re_le_norm z).trans hz.le
        have him : |z.im| ≤ 1 / 2 := (Complex.abs_im_le_norm z).trans hz.le
        have hzi := abs_nonneg z.im
        rcases lt_or_ge z.re (1 / 2) with hlt | hge
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 48114 * (|z.im| + 2) ^ 7 :=
                zeta_left hZ (by linarith [(abs_le.1 hre).1]) hlt (by rw [hz])
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by gcongr; linarith
        · calc ‖(z - 1) * riemannZeta z‖ ≤ 51 * (|z.im| + 2) ^ 2 :=
                zeta_right hZ hge (by linarith [(abs_le.1 hre).2])
            _ ≤ 51 * (5 / 2 : ℝ) ^ 2 := by gcongr; linarith
            _ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := by norm_num
      have hd : DiffContOnCl ℂ (fun z => (z - 1) * riemannZeta z) (Metric.ball (0 : ℂ) (1 / 2)) := by
        apply DifferentiableOn.diffContOnCl
        rw [closure_ball (0 : ℂ) (by norm_num : (1 / 2 : ℝ) ≠ 0)]
        intro z hz
        have hz1 : z ≠ 1 := by
          intro h
          rw [h, Metric.mem_closedBall, dist_zero_right, norm_one] at hz
          norm_num at hz
        exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hz1)).differentiableWithinAt
      have hmem : s ∈ closure (Metric.ball (0 : ℂ) (1 / 2)) := subset_closure (mem_ball_zero_iff.2 hn)
      have hb := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hd hK hmem
      calc ‖(s - 1) * riemannZeta s‖ ≤ 48114 * (5 / 2 : ℝ) ^ 7 := hb
        _ ≤ 300000 * 2 ^ 7 := by norm_num
        _ ≤ 300000 * (|s.im| + 2) ^ 7 := by gcongr

end PI.EF
end
end

section
namespace PI.EF


end PI.EF
end

section
noncomputable section

namespace PI.EF

theorem localLemma_of_helpers (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) :
    ∃ C, 0 < C ∧ LocalLemma C :=
  localLemma_of hLI (localAbstract_of hDF hDL)
    ⟨7, max 300000 53946, by norm_num, lt_max_of_lt_left (by norm_num),
      lGrowth_of hLB (zetaGrowth_of hZB)⟩ zeroLocus hZW

theorem explicitFormula_main (hZW : PI.ZerosWindow) (hDF : PI.DiscFactor) (hDL : PI.DiscLog)
    (hLB : PI.LBoundRight) (hZB : PI.ZetaBoundRight) (hLI : PI.LInvRight) : PI.ExplicitFormula :=
  explicitFormula_of_local hZW (localLemma_of_helpers hZW hDF hDL hLB hZB hLI) perron_gluing_sides

end PI.EF
end
end
