import Mathlib
import Formalism.GL3MeanSquares.HookFormulaTorsion.WeightedVonMangoldtSumIdentity

open Filter

namespace Formalism.HermitianLattices.ZeroFreeRegionGL2

private lemma ev_log_pow (K a : ℝ) (ha : 0 < a) (k : ℕ) :
    ∀ᶠ x : ℝ in atTop, K * Real.log x ^ k ≤ x ^ a := by
  have h1 : Asymptotics.IsLittleO atTop (fun x : ℝ => K * Real.log x ^ (k : ℝ)) (fun x => x ^ a) :=
    (isLittleO_log_rpow_rpow_atTop (k : ℝ) ha).const_mul_left K
  filter_upwards [h1.bound one_pos, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.rpow_natCast, one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hx0 a)] at hx
  exact le_trans (le_abs_self _) hx

private lemma ev_rpow_ge (K a : ℝ) (ha : 0 < a) : ∀ᶠ x : ℝ in atTop, K ≤ x ^ a := (tendsto_rpow_atTop ha).eventually_ge_atTop K

private lemma ev_log_ge (K : ℝ) : ∀ᶠ x : ℝ in atTop, K ≤ Real.log x := Real.tendsto_log_atTop.eventually_ge_atTop K

private lemma log_eight_le_seven : Real.log 8 ≤ 7 := by
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
  linarith

private lemma log_eight_nonneg : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)

private lemma exp_scale_pos (ε x : ℝ) : 0 < X1 ε x := by unfold X1; exact Real.exp_pos _
private lemma double_exp_scale_pos (ε x : ℝ) : 0 < X2 ε x := by unfold X2; exact Real.exp_pos _
private lemma log_exp_scale (ε x : ℝ) : Real.log (X1 ε x) = x ^ (ε / 5) := by unfold X1; exact Real.log_exp _
private lemma log_double_exp_scale (ε x : ℝ) : Real.log (X2 ε x) = x ^ (ε / 5) * Real.log x ^ 2 := by unfold X2; exact Real.log_exp _
private lemma exp_scale_rpow (ε x a : ℝ) : X1 ε x ^ a = Real.exp (x ^ (ε / 5) * a) := by unfold X1; rw [← Real.exp_mul]
private lemma double_exp_scale_rpow (ε x a : ℝ) : X2 ε x ^ a = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * a) := by unfold X2; rw [← Real.exp_mul]
private lemma log_8X1 (ε x : ℝ) : Real.log (8 * X1 ε x) = Real.log 8 + x ^ (ε / 5) := by
  rw [Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale]
private lemma log_8X1X2 (ε x : ℝ) :
    Real.log (8 * X1 ε x * X2 ε x) = Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2 := by
  rw [Real.log_mul (mul_pos (by norm_num) (exp_scale_pos ε x)).ne' (double_exp_scale_pos ε x).ne',
    Real.log_mul (by norm_num) (exp_scale_pos ε x).ne', log_exp_scale, log_double_exp_scale]

theorem numerical_bound_unit_modulus : UnitModulusIncrementConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow 801 (ε / 5) hε5 1, ev_log_pow 807 (ε / 5) hε5 3, ev_log_ge 1,
    ev_rpow_ge 7 (ε / 5) hε5, ev_rpow_ge ((20 / 13) * (|Real.log (4 * C)| + 2)) (ε / 5) hε5,
    ev_rpow_ge 2 (ε / 20) hε20, ev_log_pow (4 * C) ε hε 1, ev_rpow_ge 8 ε hε,
    eventually_ge_atTop (1 : ℝ)] with x hA hB hL hu7 huC hv hw hw8 hx1
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hA hw
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hLp : 0 < Real.log x := by linarith
  have hL3 : 0 < Real.log x ^ 3 := pow_pos hLp 3
  have hsq7 := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hl8)
  have hsqL := mul_nonneg (sq_nonneg (Real.log x)) (sub_nonneg.mpr hL)
  have hwp : 0 < x ^ ε := by positivity
  refine ⟨?_, by linarith, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have e : Real.exp (((400 : ℕ) : ℝ) * Real.log x) = x ^ 400 := by
      rw [Real.exp_nat_mul, Real.exp_log hx0]
    rw [← e, exp_scale_rpow]
    apply Real.exp_lt_exp.mpr
    push_cast
    linarith
  · rw [log_exp_scale]
    nlinarith
  · have hlog : Real.log (8 * (x ^ 400) ^ 2) = Real.log 8 + 800 * Real.log x := by
      rw [Real.log_mul (by norm_num) (pow_pos (pow_pos hx0 400) 2).ne', Real.log_pow, Real.log_pow]
      push_cast
      ring
    rw [log_exp_scale, hlog]
    nlinarith
  · rw [log_exp_scale]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  · rw [log_8X1]
    have := Real.rpow_le_rpow_of_exponent_le hx1 (show ε / 6 ≤ ε / 5 by linarith)
    linarith
  · rw [log_8X1]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ x ^ (ε / 5)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 20) - 2)]
  · have hsplit : x ^ (1 / 2 + ε) = x ^ (1 / 2 : ℝ) * x ^ ε := Real.rpow_add hx0 _ _
    have hs2 : (x ^ (1 / 2 : ℝ)) ^ 2 = x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
      norm_num
    have hden : (x ^ (1 / 2 + ε) / 2) ^ 2 = x * (x ^ ε) ^ 2 / 4 := by
      rw [hsplit, div_pow, mul_pow, hs2]
      ring
    rw [hden, Real.rpow_neg hx0.le, div_le_iff₀ (by positivity)]
    have hwne : x ^ ε ≠ 0 := hwp.ne'
    have hr : (x ^ ε)⁻¹ * (x * (x ^ ε) ^ 2 / 4) = x * x ^ ε / 4 := by
      field_simp
    rw [hr]
    nlinarith [mul_le_mul_of_nonneg_left hw hx0.le]
  · rw [Real.rpow_neg hx0.le, inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) hw8
  · have h8X : 8 * X1 ε x = Real.exp (Real.log 8 + x ^ (ε / 5)) := by
      unfold X1
      rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
    have hE : 4 * C * Real.exp ((Real.log 8 + x ^ (ε / 5)) * (1 / 4)) =
        Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (4 * C) + (Real.log 8 + x ^ (ε / 5)) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (4 * C))
      linarith
    rw [h8X, ← Real.exp_mul, exp_scale_rpow]
    linarith

theorem numerical_zero_density_bound : IncrementSizeConditions := by
  intro ε C hε hε1 hC
  have hε5 : 0 < ε / 5 := by positivity
  have hε20 : 0 < ε / 20 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_ge 5, ev_rpow_ge 16 (ε / 5) hε5,
    ev_rpow_ge (|Real.log (8 * C)| + 2) (ε / 5) hε5, ev_log_pow 3 (ε / 20) hε20 2,
    ev_rpow_ge 2 (1 / 2) (by norm_num), eventually_ge_atTop (1 : ℝ)] with x hL hu16 huC hv hs hx1
  have hx0 : (0 : ℝ) < x := by linarith
  have hl8 := log_eight_le_seven
  have hl80 := log_eight_nonneg
  have hu0 : 0 < x ^ (ε / 5) := by positivity
  have he : x ^ (ε / 6) ≤ x ^ (ε / 5) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hL2 : 25 ≤ Real.log x ^ 2 := by nlinarith
  have huL := mul_le_mul_of_nonneg_left hL2 hu0.le
  have h8 : 8 * X1 ε x * X2 ε x =
      Real.exp (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) := by
    unfold X1 X2
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m₀ hm0 hm
    have h16 : Real.log 16 ≤ 15 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 16 by norm_num)
      linarith
    have hlm : Real.log m₀ ≤ Real.log 16 + 3 * x ^ (ε / 5) := by
      have := Real.log_le_log hm0 hm
      rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
    rw [log_double_exp_scale]
    nlinarith [mul_le_mul_of_nonneg_left hlm (sq_nonneg (Real.log x)),
      mul_nonneg (sq_nonneg (Real.log x)) (by linarith : (0 : ℝ) ≤ x ^ (ε / 5) - Real.log 16)]
  · rw [log_double_exp_scale]
    nlinarith
  · rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [log_8X1X2]
    nlinarith [mul_nonneg hu0.le (sq_nonneg (Real.log x))]
  · rw [log_8X1X2]
    have hsp : x ^ (ε / 4) = x ^ (ε / 5) * x ^ (ε / 20) := by
      rw [← Real.rpow_add hx0]
      congr 1
      ring
    rw [hsp]
    nlinarith [mul_le_mul_of_nonneg_left hv hu0.le]
  · have hE : 8 * C * Real.exp ((Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) =
        Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) := by
      rw [Real.exp_add, Real.exp_log (mul_pos (by norm_num) hC)]
    have hle : Real.exp (Real.log (8 * C) +
          (Real.log 8 + x ^ (ε / 5) + x ^ (ε / 5) * Real.log x ^ 2) * (1 / 4)) ≤
        Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (9 / 10)) := by
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (8 * C))
      nlinarith
    rw [h8, ← Real.exp_mul, double_exp_scale_rpow]
    linarith
  · rw [Real.rpow_add hx0]
    have hwp : 0 < x ^ ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hs hwp.le]

theorem log_nonexceptional_bound : LogNE := by
  intro ε A hε hA
  have hε5 : 0 < ε / 5 := by positivity
  refine Filter.eventually_atTop.mp ?_
  filter_upwards [ev_log_pow A (ε / 5) hε5 1, ev_rpow_ge 3 (ε / 5) hε5, ev_log_ge 2,
    eventually_ge_atTop (1 : ℝ)] with x hAL hu3 hL hx1
  intro n q₁ d hn hnx hq1 hq1' hd hd'
  have hx0 : (0 : ℝ) < x := by linarith
  rw [pow_one] at hAL
  have hX1h : X1 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * (1 / 2)) := exp_scale_rpow ε x _
  have hX2h : X2 ε x ^ (1 / 2 : ℝ) = Real.exp (x ^ (ε / 5) * Real.log x ^ 2 * (1 / 2)) :=
    double_exp_scale_rpow ε x _
  have hX1p : 0 < X1 ε x ^ (1 / 2 : ℝ) := by rw [hX1h]; exact Real.exp_pos _
  have hX2p : 0 < X2 ε x ^ (1 / 2 : ℝ) := by rw [hX2h]; exact Real.exp_pos _
  have hq0 : (0 : ℝ) < q₁ := lt_trans hX1p hq1
  have hd0 : (0 : ℝ) < d := lt_trans hX2p hd
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : x ^ (ε / 5) / 2 < Real.log q₁ := by
    have := Real.log_lt_log hX1p hq1
    rw [hX1h, Real.log_exp] at this
    linarith
  have h2 : Real.log q₁ ≤ x ^ (ε / 5) := by
    have := Real.log_le_log hq0 hq1'
    rwa [log_exp_scale] at this
  have h3 : x ^ (ε / 5) * Real.log x ^ 2 / 2 < Real.log d := by
    have := Real.log_lt_log hX2p hd
    rw [hX2h, Real.log_exp] at this
    linarith
  have h4 : Real.log d ≤ x ^ (ε / 5) * Real.log x ^ 2 := by
    have := Real.log_le_log hd0 hd'
    rwa [log_double_exp_scale] at this
  have h5 : Real.log n ≤ A * Real.log x := by
    have := Real.log_le_log hn0 hnx
    rwa [Real.log_rpow hx0] at this
  refine ⟨h1, h2, h3, h4, ?_⟩
  have hlog4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith
  have hL4 : (4 : ℝ) ≤ Real.log x ^ 2 := by nlinarith
  have hu0 : (0 : ℝ) ≤ x ^ (ε / 5) := by positivity
  have huL := mul_le_mul_of_nonneg_left hL4 hu0
  push_cast
  rw [Real.log_mul (mul_pos (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0) hq0).ne' hd0.ne',
    Real.log_mul (mul_pos (show (0 : ℝ) < 4 by norm_num) hn0).ne' hq0.ne',
    Real.log_mul (show (4 : ℝ) ≠ 0 by norm_num) hn0.ne']
  nlinarith

open DirichletCharacter in
private lemma cond_mul_coprime {n : ℕ} [NeZero n] (A B : DirichletCharacter ℂ n)
    (h : A.conductor.Coprime B.conductor) : A.conductor * B.conductor ∣ (A * B).conductor := by
  have hA : A.conductor ∣ (A * B).conductor := by
    have h1 : A.conductor ∣ ((A * B).conductor).lcm (B⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) B⁻¹
      rwa [mul_inv_cancel_right] at this
    rw [conductor_inv] at h1
    have h2 : A.conductor ∣ (A * B).conductor * B.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.dvd_of_dvd_mul_right h2
  have hB : B.conductor ∣ (A * B).conductor := by
    have h1 : B.conductor ∣ ((A * B).conductor).lcm (A⁻¹).conductor := by
      have := conductor_mul_dvd_lcm_conductor (A * B) A⁻¹
      rwa [mul_comm A B, mul_inv_cancel_right, mul_comm B A] at this
    rw [conductor_inv] at h1
    have h2 : B.conductor ∣ (A * B).conductor * A.conductor := h1.trans (Nat.lcm_dvd_mul _ _)
    exact h.symm.dvd_of_dvd_mul_right h2
  exact h.mul_dvd_of_dvd_of_dvd hA hB







open Finset ArithmeticFunction in
private noncomputable def SS {t : ℕ} (θ : DirichletCharacter ℂ t) (x : ℝ) (q : ℕ) : ℝ :=
  ‖∑ n ∈ Icc 1 ⌊x ^ 400⌋₊, ((cN x n : ℝ) : ℂ) * θ (n : ZMod t) * ((jacobiSym (n : ℤ) q : ℤ) : ℂ)‖

open Classical in
private noncomputable def badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) :
    Finset ℕ :=
  P.filter (fun q => ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h))

open Classical in
private lemma mem_badSet {t : ℕ} [NeZero t] (θ : DirichletCharacter ℂ t) (Q : ℝ) (P : Finset ℕ) (q : ℕ) :
    q ∈ badSet θ Q P ↔ q ∈ P ∧ ∃ h : Fact q.Prime, ¬ ZeroFreeBox Q (@tw t θ q h) := by
  rw [badSet, Finset.mem_filter]









end Formalism.HermitianLattices.ZeroFreeRegionGL2
