module

public import Formalism.LFunctionBounds.PositivityBound
public import Formalism.LFunctionBounds.LFunctionBoundsProofs.LFunctionEqGOfOneLt

@[expose] public section

open Complex Filter Topology

noncomputable section

namespace Formalism.FX


open LFunctionPartialSum in
lemma LFunctionPartialSum.norm_tail_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {B : ℝ}
    (hB : ∀ M, ‖Ap χ M‖ ≤ B) {s : ℂ} (hs : 0 < s.re) (N : ℕ) :
    ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hc : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have hterm : ∀ i : ℕ, ‖dterm χ s (i + (N + 1))‖ ≤
      B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    simpa only [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm] using
      norm_dterm_le' χ hB hs (n := i + (N + 1)) (by lia)
  have hf0 : ∀ i : ℕ, 0 ≤ B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
    intro i
    refine mul_nonneg hB0 (mul_nonneg hc (sub_nonneg.mpr ?_))
    have hle : (((i + (N + 1) : ℕ) : ℝ)) ≤ (((i + 1 + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show i + (N + 1) ≤ i + 1 + (N + 1) by omega)
    have hpos : (0 : ℝ) < (((i + (N + 1) : ℕ) : ℝ)) := by
      exact_mod_cast (show 0 < i + (N + 1) by omega)
    first
    | exact Real.rpow_le_rpow_of_nonpos hpos hle (by linarith)
  have hpart : ∀ n : ℕ, ∑ i ∈ Finset.range n, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
      (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by
    intro n
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_range_sub']
    have hv0 : (((0 + (N + 1) : ℕ) : ℝ)) ^ (-s.re) = ((N : ℝ) + 1) ^ (-s.re) := by
      congr 1
      push_cast
      ring
    rw [hv0]
    have hvn : 0 ≤ (((n + (N + 1) : ℕ) : ℝ)) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    have hm := mul_nonneg (mul_nonneg hB0 hc) hvn
    nlinarith
  have hsf := summable_of_sum_range_le hf0 hpart
  have hsn : Summable (fun i : ℕ => ‖dterm χ s (i + (N + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm hsf
  calc ‖∑' i, dterm χ s (i + (N + 1))‖ ≤ ∑' i, ‖dterm χ s (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' i : ℕ, B * (‖s‖ / s.re * ((((i + (N + 1) : ℕ) : ℝ)) ^ (-s.re) -
        (((i + 1 + (N + 1) : ℕ) : ℝ)) ^ (-s.re))) := by
      first
      | exact Summable.tsum_le_tsum hterm hsn hsf
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := Real.tsum_le_of_sum_range_le hf0 hpart

open LFunctionPartialSum in
theorem l_function_partial_sum : LPartialSum := by
  intro q _ χ hχ B hB s hs N hN
  have hB' : ∀ M, ‖Ap χ M‖ ≤ B := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB' 0)
  rw [LFunction_eq_G χ hχ hB' hs, ← partial_identity χ s N]
  have hsum := summable_dterm χ hB' hs
  have hG : LFunctionPartialSum.G χ s = ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) :=
    (hsum.sum_add_tsum_nat_add (N + 1)).symm
  rw [hG]
  have e : ∑ n ∈ Finset.range (N + 1), dterm χ s n + ∑' i, dterm χ s (i + (N + 1)) -
      (∑ n ∈ Finset.range (N + 1), dterm χ s n + Ap χ N * ((N : ℂ) + 1) ^ (-s)) =
      ∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s) := by ring
  rw [e]
  have h1 := norm_tail_le χ hB' hs N
  have h2 : ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ ≤ B * ((N : ℝ) + 1) ^ (-s.re) := by
    rw [norm_mul, natCast_add_one_eq, Complex.norm_cpow_eq_rpow_re_of_pos (by positivity)]
    simp only [Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hB' N) (Real.rpow_nonneg (by positivity) _)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have h3 : ((N : ℝ) + 1) ^ (-s.re) ≤ (N : ℝ) ^ (-s.re) :=
    Real.rpow_le_rpow_of_nonpos hNpos (by linarith) (by linarith)
  have hq : 0 ≤ ‖s‖ / s.re := div_nonneg (norm_nonneg _) hs.le
  have h4 : 0 ≤ (N : ℝ) ^ (-s.re) := Real.rpow_nonneg hNpos.le _
  have h5 : 0 ≤ ((N : ℝ) + 1) ^ (-s.re) := Real.rpow_nonneg (by positivity) _
  calc ‖∑' i, dterm χ s (i + (N + 1)) - Ap χ N * ((N : ℂ) + 1) ^ (-s)‖
      ≤ ‖∑' i, dterm χ s (i + (N + 1))‖ + ‖Ap χ N * ((N : ℂ) + 1) ^ (-s)‖ := norm_sub_le _ _
    _ ≤ B * (‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) + B * ((N : ℝ) + 1) ^ (-s.re) := add_le_add h1 h2
    _ = B * (1 + ‖s‖ / s.re) * ((N : ℝ) + 1) ^ (-s.re) := by ring
    _ ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg hB0 (by linarith))
    _ ≤ 2 * B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) := by
        have : 0 ≤ B * (1 + ‖s‖ / s.re) * (N : ℝ) ^ (-s.re) :=
          mul_nonneg (mul_nonneg hB0 (by linarith)) h4
        linarith

end Formalism.FX
