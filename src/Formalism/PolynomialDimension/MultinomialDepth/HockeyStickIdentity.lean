import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames


def digitSum {m P : ℕ} (τ : Fin m → Fin P) : ℕ := ∑ i, (τ i : ℕ)


theorem digit_step (P g e : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (hkey : ∀ j : ℕ, (1 - t) * ((g : ℝ) + j + 1) ≤ (P : ℝ) * ((e : ℝ) + j + 1)) :
    ∀ j : ℕ, (1 - (j : ℝ) * t) * ((g + j).choose j : ℝ) ≤ (P : ℝ) ^ j * ((e + j).choose j : ℝ) := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hg : ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((g : ℝ) + j + 1) * ((g + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (g + j) j
      have h' : g + (j + 1) = g + j + 1 := by ring
      rw [h']
      have hc : (((g + j + 1) * (g + j).choose j : ℕ) : ℝ)
          = (((g + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have he : ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((e : ℝ) + j + 1) * ((e + j).choose j : ℝ) := by
      have := Nat.add_one_mul_choose_eq (e + j) j
      have h' : e + (j + 1) = e + j + 1 := by ring
      rw [h']
      have hc : (((e + j + 1) * (e + j).choose j : ℕ) : ℝ)
          = (((e + j + 1).choose (j + 1) * (j + 1) : ℕ) : ℝ) := by
        rw [this]
      push_cast at hc
      linarith
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hCg : (0 : ℝ) ≤ ((g + j).choose j : ℝ) := by positivity
    have hCe : (0 : ℝ) ≤ ((e + j).choose j : ℝ) := by positivity
    have hRHS : (0 : ℝ) ≤ (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) := by positivity
    push_cast
    by_cases hneg : 1 - ((j : ℝ) + 1) * t ≤ 0
    · have : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hneg (by positivity)
      linarith
    push Not at hneg
    have hA : 0 ≤ 1 - (j : ℝ) * t := by nlinarith
    have hB : 0 ≤ 1 - t := by nlinarith
    have hG : (0 : ℝ) ≤ (g : ℝ) + j + 1 := by positivity

    rw [← mul_le_mul_iff_of_pos_right hj1]
    have hL : (1 - ((j : ℝ) + 1) * t) * ((g + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) := by
      rw [mul_assoc, hg]
    have hR : (P : ℝ) ^ (j + 1) * ((e + (j + 1)).choose (j + 1) : ℝ) * ((j : ℝ) + 1)
        = ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) := by
      rw [mul_assoc, he, pow_succ]; ring
    rw [hL, hR]
    have h1 : (1 - ((j : ℝ) + 1) * t) ≤ (1 - (j : ℝ) * t) * (1 - t) := by
      nlinarith [mul_nonneg (Nat.cast_nonneg j : (0:ℝ) ≤ j) (mul_nonneg ht ht)]
    calc (1 - ((j : ℝ) + 1) * t) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ))
        ≤ ((1 - (j : ℝ) * t) * (1 - t)) * (((g : ℝ) + j + 1) * ((g + j).choose j : ℝ)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = ((1 - (j : ℝ) * t) * ((g + j).choose j : ℝ)) * ((1 - t) * ((g : ℝ) + j + 1)) := by ring
      _ ≤ ((P : ℝ) ^ j * ((e + j).choose j : ℝ)) * ((P : ℝ) * ((e : ℝ) + j + 1)) :=
          mul_le_mul ih (hkey j) (by positivity) (by positivity)


end Formalism.CountingSumsFrames
