module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.AffineSplittingSpan.Transfer
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace PositivityTheory.KB.SplitAffineSpectral.PrismSpan

open PositivityTheory.KB.SplitAffineSpectral

variable {P : Type} [Group P]

def levSum (t : P) (lev : P → ℤ) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) : ℝ :=
  if 0 ≤ lev (y 0) then ∑ j ∈ Finset.range (lev (y 0)).toNat, w (fun i => t ^ (-((j : ℤ) + 1)) * y i)
  else -∑ j ∈ Finset.range (-lev (y 0)).toNat, w (fun i => t ^ (j : ℤ) * y i)

theorem levSum_spec (t : P) (lev : P → ℤ) (hlev : ∀ z, lev (t * z) = lev z + 1) {n : ℕ}
    (w : (Fin (n + 1) → P) → ℝ) (y : Fin (n + 1) → P) :
    levSum t lev w (fun i => t * y i) - levSum t lev w y = w y := by
  unfold levSum
  have e : ∀ k : ℤ, (fun i => t ^ k * (t * y i)) = fun i => t ^ (k + 1) * y i := by
    intro k
    funext i
    rw [← mul_assoc, ← zpow_add_one]
  simp only [hlev, e]
  generalize lev (y 0) = a
  rcases le_or_gt 0 a with h | h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [if_pos (by omega), if_pos h]
    rw [show ((m : ℤ) + 1).toNat = m + 1 by omega, Int.toNat_natCast, Finset.sum_range_succ']
    have ex : ∀ j : ℕ, -(((j + 1 : ℕ) : ℤ) + 1) + 1 = -((j : ℤ) + 1) := by
      intro j
      push_cast
      ring
    simp only [ex]
    simp
  · obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero h
    rcases m with _ | k
    · rw [if_pos (by omega), if_neg (by omega)]
      simp
    · rw [if_neg (by omega), if_neg (by omega)]
      rw [show (-(Int.negSucc (k + 1) + 1)).toNat = k + 1 by omega,
        show (-Int.negSucc (k + 1)).toNat = k + 1 + 1 by omega, Finset.sum_range_succ' _ (k + 1)]
      have ex : ∀ j : ℕ, ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) := by
        intro j
        push_cast
        rfl
      simp only [ex]
      simp

theorem levSum_inv (t : P) (lev : P → ℤ) (S : Set P) (hS : ∀ g ∈ S, ∀ z, lev (g * z) = lev z)
    (hc : ∀ g ∈ S, g * t = t * g) {n : ℕ} (w : (Fin (n + 1) → P) → ℝ) (hw : InvS S w) :
    InvS S (levSum t lev w) := by
  intro g hg y
  unfold levSum
  simp only [hS g hg]
  have hk : ∀ k : ℤ, (fun i => t ^ k * (g * y i)) = fun i => g * (t ^ k * y i) := by
    intro k; funext i
    rw [← mul_assoc, ← mul_assoc, ((Commute.zpow_right (hc g hg) k)).eq]
  simp only [hk, hw g hg]

end PositivityTheory.KB.SplitAffineSpectral.PrismSpan

end
