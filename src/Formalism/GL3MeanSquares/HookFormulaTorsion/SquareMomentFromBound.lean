import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset
open Formalism.LogVandermondeBounds.flipTwoThree (hookF Interlace B0 len)


theorem column_top_entry : LastColumnBound := by
  intro κ lam A bt S hbt hS h0 hl hmid
  have hsucc : ∀ j : Fin (κ + 1), lam j.succ ≤ S := by
    intro j
    by_cases hj : j.succ = Fin.last (κ + 1)
    · rw [hj, hl]; linarith
    · exact (hmid j.succ (Fin.succ_ne_zero j) hj).2
  have hsum : ∑ j : Fin (κ + 1), lam j.succ ≤ (κ + 1) * S := by
    calc ∑ j : Fin (κ + 1), lam j.succ ≤ ∑ _j : Fin (κ + 1), S := Finset.sum_le_sum fun j _ => hsucc j
      _ = (κ + 1) * S := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; push_cast; ring
  constructor
  · unfold wt
    rw [Fin.sum_univ_succ, h0]
    nlinarith
  · unfold wt plus
    rw [Fin.sum_univ_succ, h0, hl]
    have e : ∑ j : Fin (κ + 1), (lam j.succ - -bt) = ∑ j : Fin (κ + 1), lam j.succ + (κ + 1) * bt := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast; ring
    rw [e]
    nlinarith


theorem first_zeta_count : PackingCountBound := by
  intro f g u v hf hv hu
  have hfR : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hfv : 0 < (f : ℝ) / v := div_pos (by linarith) hv
  set t := 2 * Real.sqrt u / Real.sqrt (f / v) with ht
  have ht2 : t ^ 2 = 4 * u * v / f := by
    rw [ht, div_pow, mul_pow, Real.sq_sqrt hu, Real.sq_sqrt hfv.le]
    field_simp
    ring
  have huv : 0 ≤ 4 * u * v := by positivity
  have ht2' : t ^ 2 ≤ 4 * u * v := by
    rw [ht2]; exact div_le_self huv hfR
  have key : (1 + t) ^ 2 ≤ 2 * (1 + 4 * u * v) := by nlinarith [sq_nonneg (1 - t)]
  calc (1 + t) ^ (2 * g) = ((1 + t) ^ 2) ^ g := pow_mul _ _ _
    _ ≤ (2 * (1 + 4 * u * v)) ^ g := pow_le_pow_left₀ (sq_nonneg _) key g
    _ = 2 ^ g * (1 + 4 * u * v) ^ g := mul_pow _ _ _





end Formalism.HermitianLattices.TraceIntegrality
