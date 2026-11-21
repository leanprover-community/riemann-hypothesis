import Formalism.PeriodIntegrals.SzCt

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.G
open scoped BigOperators

namespace PI.SzCt.W

theorem N_le_N (D : D7) (j : ℕ) : D.R.N (j - 1) ≤ D.R.N j := by
  unfold Formalism.BasicNotions.Ranks.N
  have : (j - 1) * (D.R.t + 1) ≤ j * (D.R.t + 1) := Nat.mul_le_mul_right _ (Nat.sub_le j 1)
  omega

theorem N_succ (D : D7) (j : ℕ) (hj : 1 ≤ j) : D.R.N j = D.R.N (j - 1) + (D.R.t + 1) := by
  unfold Formalism.BasicNotions.Ranks.N
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  ring

theorem shift_pos (D : D7) (j i : ℕ) (hi : i < D.R.N (j - 1)) :
    0 < (((D.R.N (j - 1) : ℝ) + D.R.N j - 1 - 2 * (i : ℝ)) / 2) := by
  have h1 : (D.R.N (j - 1) : ℝ) ≤ D.R.N j := by exact_mod_cast N_le_N D j
  have h2 : (i : ℝ) + 1 ≤ D.R.N (j - 1) := by exact_mod_cast hi
  apply div_pos _ two_pos
  linarith

theorem nuRow_le (D : D7) (u : D.what₂.Word) (j : ℕ) (τ : D.what₂.Tau) (i : ℕ)
    (hi : i < D.R.N (j - 1)) :
    DV.nuRow D u j τ i ≤ ((DV.srcPar D u τ i : ℚ) : ℝ) + DV.wSz D j τ := by
  have := shift_pos D j i hi
  unfold DV.nuRow
  linarith

theorem srcPar_lt (D : D7) (u : D.what₂.Word) (τ : D.what₂.Tau) (i : ℕ) (h : i < D.R.k) :
    DV.srcPar D u τ i = (D.hcW u τ).u ⟨i, h⟩ := by
  unfold DV.srcPar
  rw [dif_pos h]

theorem wSz_eq (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    DV.wSz D j τ = (((D.hc τ).e ⟨j - 1, by omega⟩ : ℚ) : ℝ) := by
  unfold DV.wSz
  rw [dif_pos ⟨hj, hm⟩]

theorem wSz_eq_wj (D : D7) (j : ℕ) (τ : D.what₂.Tau) (hj : 1 ≤ j) (hm : j ≤ D.R.m) :
    DV.wSz D j τ = wj D j τ := by
  rw [wSz_eq D j τ hj hm]
  unfold wj
  rw [dif_pos (by omega)]



end PI.SzCt.W
