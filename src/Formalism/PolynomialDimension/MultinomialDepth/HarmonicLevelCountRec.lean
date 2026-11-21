import Formalism.PolynomialDimension.DigitClassSize

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames

lemma dimPol_mono (k' : ℕ) {a b : ℕ} (h : a ≤ b) : dimPol k' a ≤ dimPol k' b :=
  Nat.choose_le_choose k' (by omega)


lemma dimPol_succ_vars (k' b : ℕ) : dimPol (k' + 1) b * (k' + 1) = (b + k' + 1) * dimPol k' b := by
  unfold dimPol
  rw [show b + (k' + 1) = b + k' + 1 by omega]
  exact (Nat.add_one_mul_choose_eq (b + k') k').symm


theorem harmonic_level_count_rec (k' : ℕ) : ∀ A B : ℕ,
    ∑ j ∈ range (min A B + 1), dimHar k' (A - j) (B - j) = dimPol k' A * dimPol k' B
  | 0, B => by simp [dimHar]
  | A + 1, 0 => by simp [dimHar]
  | A + 1, B + 1 => by
    rw [show min (A + 1) (B + 1) + 1 = (min A B + 1) + 1 by omega, Finset.sum_range_succ']
    have e : ∀ j ∈ range (min A B + 1),
        dimHar k' (A + 1 - (j + 1)) (B + 1 - (j + 1)) = dimHar k' (A - j) (B - j) := by
      intro j _
      rw [show A + 1 - (j + 1) = A - j by omega, show B + 1 - (j + 1) = B - j by omega]
    rw [Finset.sum_congr rfl e, harmonic_level_count_rec k' A B]
    have hle : dimPol k' A * dimPol k' B ≤ dimPol k' (A + 1) * dimPol k' (B + 1) :=
      Nat.mul_le_mul (dimPol_mono k' (by omega)) (dimPol_mono k' (by omega))
    simp only [dimHar, Nat.sub_zero, Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero,
      and_false, or_self, if_false]
    exact Nat.add_sub_cancel' hle

theorem harmonic_level_count : LevelCount :=
  fun k' A B => harmonic_level_count_rec k' A B


lemma dimPol_ratio (B J : ℕ) (hJ : J ≤ B) : ∀ k' : ℕ,
    (dimPol k' (B - J) : ℝ) ≤ (1 - (J : ℝ) / ((B : ℝ) + k' + 1)) ^ k' * dimPol k' B
  | 0 => by simp [dimPol]
  | k' + 1 => by
    have ih := dimPol_ratio B J hJ k'
    have h1 : (dimPol (k' + 1) (B - J) : ℝ) * ((k' : ℝ) + 1)
        = ((B : ℝ) - J + k' + 1) * dimPol k' (B - J) := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' (B - J))
      push_cast [Nat.cast_sub hJ] at this
      linarith
    have h2 : (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) = ((B : ℝ) + k' + 1) * dimPol k' B := by
      have := congrArg (Nat.cast : ℕ → ℝ) (dimPol_succ_vars k' B)
      push_cast at this
      linarith
    have hJB : (J : ℝ) ≤ B := by exact_mod_cast hJ
    have hB0 : (0 : ℝ) < (B : ℝ) + k' + 1 := by positivity
    have hB1 : (0 : ℝ) < (B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1 := by positivity
    set x := (J : ℝ) / ((B : ℝ) + k' + 1) with hx
    set y := (J : ℝ) / ((B : ℝ) + ((k' + 1 : ℕ) : ℝ) + 1) with hy
    have hx1 : x ≤ 1 := by rw [hx, div_le_one hB0]; linarith
    have hyx : y ≤ x := by
      rw [hx, hy]
      apply div_le_div_of_nonneg_left (by positivity) hB0
      push_cast; linarith
    have hxe : (1 - x) * ((B : ℝ) + k' + 1) = (B : ℝ) - J + k' + 1 := by
      rw [hx]; field_simp; ring
    have hP0 : (0 : ℝ) ≤ dimPol k' B := by positivity
    have hk : (0 : ℝ) < (k' : ℝ) + 1 := by positivity
    rw [← mul_le_mul_iff_of_pos_right hk, h1]
    calc ((B : ℝ) - J + k' + 1) * dimPol k' (B - J)
        ≤ ((B : ℝ) - J + k' + 1) * ((1 - x) ^ k' * dimPol k' B) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - x) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          rw [h2, ← hxe]; ring
      _ ≤ (1 - y) ^ (k' + 1) * ((dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact pow_le_pow_left₀ (by linarith) (by linarith) _
      _ = (1 - y) ^ (k' + 1) * (dimPol (k' + 1) B : ℝ) * ((k' : ℝ) + 1) := by ring

lemma tail_bound (k' A B J : ℕ) (hJ : J ≤ min A B) :
    ((dimPol k' (A - J) * dimPol k' (B - J) : ℕ) : ℝ) ≤
      (1 - (J : ℝ) / (B + k' + 1)) ^ k' * ((dimPol k' A * dimPol k' B : ℕ) : ℝ) := by
  have hJB' : J ≤ B := le_trans hJ (min_le_right A B)
  have hJB : (J:ℝ) ≤ B := by exact_mod_cast hJB'
  have hx0 : 0 ≤ 1 - (J:ℝ) / ((B:ℝ) + k' + 1) := by
    rw [sub_nonneg, div_le_one (by positivity)]; linarith
  have h1 : (dimPol k' (A - J) : ℝ) ≤ dimPol k' A := by
    exact_mod_cast dimPol_mono k' (Nat.sub_le A J)
  have h2 := dimPol_ratio B J hJB' k'
  rw [Nat.cast_mul, Nat.cast_mul]
  calc (dimPol k' (A - J) : ℝ) * dimPol k' (B - J)
      ≤ dimPol k' A * ((1 - (J:ℝ) / ((B:ℝ) + k' + 1)) ^ k' * dimPol k' B) :=
        mul_le_mul h1 h2 (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    _ = _ := by ring




end Formalism.CountingSumsFrames
