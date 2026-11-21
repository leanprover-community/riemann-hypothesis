import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.BernoulliNumbers.MapGenBChar

section
open Finset UpperTheory.V.Bern

private theorem polybound_cast (k : ℕ) (x : ℚ) :
    (((Polynomial.bernoulli k).eval x : ℚ) : ℝ) = bernoulliFun k (x : ℝ) := by
  rw [bernoulliFun, Polynomial.eval_map_algebraMap, ← eq_ratCast (algebraMap ℚ ℝ) x,
    Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval, eq_ratCast]

private theorem polybound_norm_fourier (n : ℤ) (y : UnitAddCircle) : ‖fourier n y‖ = 1 := by
  rw [fourier_apply]; exact Circle.norm_coe _

private theorem polybound_big {k : ℕ} (hk : 2 ≤ k) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| ≤ 4 := by
  have hs := hasSum_one_div_nat_pow_mul_fourier hk hx
  have h2 : ∀ (m : ℤ) (y : UnitAddCircle), ‖fourier m y + (-1) ^ k * fourier (-m) y‖ ≤ 2 := by
    intro m y
    calc _ ≤ ‖fourier m y‖ + ‖(-1 : ℂ) ^ k * fourier (-m) y‖ := norm_add_le _ _
      _ = 2 := by
        rw [norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul, polybound_norm_fourier,
          polybound_norm_fourier]
        norm_num
  have hbound : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      ≤ 2 * (Real.pi ^ 2 / 6) := by
    rw [← hs.tsum_eq]
    refine tsum_of_norm_bounded (hasSum_zeta_two.mul_left 2) fun n ↦ ?_
    rw [norm_mul]
    have h1 : ‖1 / (n : ℂ) ^ k‖ ≤ 1 / (n : ℝ) ^ 2 := by
      rw [norm_div, norm_one, norm_pow, Complex.norm_natCast]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [zero_pow (by omega : k ≠ 0)]
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ hn1 hk)
    calc _ ≤ 1 / (n : ℝ) ^ 2 * 2 := mul_le_mul h1 (h2 _ _) (norm_nonneg _) (by positivity)
      _ = 2 * (1 / (n : ℝ) ^ 2) := mul_comm _ _
  have hnorm : ‖-(2 * (Real.pi : ℂ) * Complex.I) ^ k / (k.factorial : ℂ) * (bernoulliFun k x : ℂ)‖
      = (2 * Real.pi) ^ k / (k.factorial : ℝ) * |bernoulliFun k x| := by
    rw [norm_mul, norm_div, norm_neg, norm_pow, norm_mul, norm_mul, Complex.norm_I,
      Complex.norm_real, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos, mul_one, Complex.norm_two]
  rw [← hnorm]
  refine hbound.trans ?_
  nlinarith [Real.pi_pos, Real.pi_lt_d2]

theorem UpperTheory.V.Bern.b_polybound :
    ∀ (k : ℕ) (x : ℚ), 0 ≤ x → x ≤ 1 → |(((Polynomial.bernoulli k).eval x : ℚ) : ℝ)| ≤ 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro k x h0 h1
  have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast h0
  have hx1 : (x : ℝ) ≤ 1 := by exact_mod_cast h1
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  rcases lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp [Polynomial.bernoulli_zero]
    · simp only [Polynomial.bernoulli_one, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
        Nat.factorial_one, Nat.cast_one, pow_one]
      have key : |(x : ℝ) - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
      have : (1 : ℝ) / 2 ≤ 4 * 1 / (2 * Real.pi) := by
        rw [le_div_iff₀ hpi]
        nlinarith [Real.pi_lt_d2]
      linarith
  · have hb := polybound_big hk (x := (x : ℝ)) ⟨hx0, hx1⟩
    rw [polybound_cast]
    have hf : (0 : ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    rw [div_mul_eq_mul_div, div_le_iff₀ hf] at hb
    rw [le_div_iff₀ (pow_pos hpi k)]
    linarith [mul_comm (|bernoulliFun k x|) ((2 * Real.pi) ^ k)]
end

section
open Finset UpperTheory.V.Bern

theorem UpperTheory.V.Bern.b_upper :
    ∀ {N : ℕ} (k : ℕ) (Φ : ZMod N → ℂ), 0 < N → (∀ a, ‖Φ a‖ ≤ 1) → ‖genB k Φ‖ ≤ 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
  intro N k Φ hN hΦ
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  set C : ℝ := 4 * (k.factorial : ℝ) / (2 * Real.pi) ^ k with hC
  have hterm : ∀ a ∈ Icc 1 N,
      ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ ≤ (N : ℝ) ^ ((k : ℤ) - 1) * C := by
    intro a ha
    rw [Finset.mem_Icc] at ha
    have hx0 : (0 : ℚ) ≤ (a : ℚ) / N := by positivity
    have hx1 : (a : ℚ) / N ≤ 1 := by
      rw [div_le_one (by exact_mod_cast hN)]
      exact_mod_cast ha.2
    have hb : ‖algebraMap ℚ ℂ (bcoef N k a)‖ =
        (N : ℝ) ^ ((k : ℤ) - 1) * |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)| := by
      rw [eq_ratCast, ← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs, bcoef]
      push_cast
      rw [abs_mul, abs_of_pos (zpow_pos hNr _)]
    rw [norm_mul, hb]
    have hp := b_polybound k ((a : ℚ) / N) hx0 hx1
    calc ‖Φ (a : ZMod N)‖ * ((N : ℝ) ^ ((k : ℤ) - 1) *
          |((Polynomial.eval ((a : ℚ) / N) (Polynomial.bernoulli k) : ℚ) : ℝ)|)
        ≤ 1 * ((N : ℝ) ^ ((k : ℤ) - 1) * C) := by
          apply mul_le_mul (hΦ _) _ (by positivity) zero_le_one
          exact mul_le_mul_of_nonneg_left hp (zpow_pos hNr _).le
      _ = (N : ℝ) ^ ((k : ℤ) - 1) * C := one_mul _
  calc ‖genB k Φ‖ ≤ ∑ a ∈ Icc 1 N, ‖Φ (a : ZMod N) * algebraMap ℚ ℂ (bcoef N k a)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ a ∈ Icc 1 N, (N : ℝ) ^ ((k : ℤ) - 1) * C := Finset.sum_le_sum hterm
    _ = 4 * (N : ℝ) ^ k * (k.factorial : ℝ) / (2 * Real.pi) ^ k := by
        rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
          zpow_sub_one₀ hNr.ne', zpow_natCast, hC]
        field_simp
end
