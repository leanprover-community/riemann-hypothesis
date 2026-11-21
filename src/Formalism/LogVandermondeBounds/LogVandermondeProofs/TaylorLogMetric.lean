import Formalism.LogVandermondeBounds.EvenOddPowerQuotientEqualityCases

namespace Formalism.LogVandermondeBounds.TaylorLogMetric

open Finset

lemma key_ineq (x : ℚ) (hx : 2 ≤ x) :
    ∀ i j : ℕ, i ≤ j → (i, j) ≠ (0, 0) →
      x ^ 3 - 2 * x ^ 2 + 3 ≤ (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) := by
  have hq : 1 ≤ x ^ 2 := by nlinarith

  have step : ∀ i j : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + 1) - (x ^ 2 - 1) * ((i : ℚ) + (j + 1 : ℕ) + 1) := by
    intro i j
    have hA : 1 ≤ (x ^ 2) ^ j := one_le_pow₀ hq
    have hB : 1 ≤ x * (x ^ 2) ^ j := by nlinarith
    push_cast
    rw [pow_succ (x ^ 2) j]
    have hq0 : 0 ≤ x ^ 2 - 1 := by linarith
    nlinarith [mul_le_mul_of_nonneg_right hB hq0]
  have mono : ∀ i j k : ℕ, (x ^ 2) ^ i + x * (x ^ 2) ^ j - (x ^ 2 - 1) * ((i : ℚ) + j + 1) ≤
      (x ^ 2) ^ i + x * (x ^ 2) ^ (j + k) - (x ^ 2 - 1) * ((i : ℚ) + (j + k : ℕ) + 1) := by
    intro i j k
    induction k with
    | zero => simp
    | succ k ih => exact ih.trans (by simpa [Nat.add_assoc] using step i (j + k))

  have diag : ∀ m : ℕ, x ^ 3 - 2 * x ^ 2 + 3 ≤
      (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) - (x ^ 2 - 1) * (((m + 1 : ℕ) : ℚ) + (m + 1 : ℕ) + 1) := by
    intro m
    induction m with
    | zero => push_cast; ring_nf; linarith
    | succ m ih =>
      have hA : 1 ≤ (x ^ 2) ^ (m + 1) := one_le_pow₀ hq
      have hB : 2 ≤ (x ^ 2) ^ (m + 1) + x * (x ^ 2) ^ (m + 1) := by nlinarith
      refine ih.trans ?_
      push_cast at *
      rw [pow_succ (x ^ 2) (m + 1)]
      nlinarith
  intro i j hij hne
  rcases Nat.eq_zero_or_pos i with rfl | hi
  ·
    have hj : 1 ≤ j := by
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · exact absurd rfl hne
      · exact hj
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
    refine le_trans ?_ (mono 0 1 k)
    push_cast; ring_nf; linarith
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hi
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hij
    have := mono (1 + m) (1 + m) k
    have h2 := diag m
    rw [Nat.add_comm 1 m] at *
    linarith









end Formalism.LogVandermondeBounds.TaylorLogMetric
