import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
open Finset

theorem sum_tele (f : ℕ → ℝ) {p n : ℕ} (hp : p ≤ n) :
    ∑ i ∈ Ico p n, (f (i + 1) - f i) = f n - f p := by
  induction n, hp using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    rw [Finset.sum_Ico_succ_top hk, ih]
    ring




end ReciprocityTheory.ChartRestriction.G.FD.TelescopingWeightedSums
