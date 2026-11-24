module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.Defs

@[expose] public section

namespace GlobalTheory

theorem sum_bound_of_step_diff :
    ∀ (a : ℕ → ℕ) (d p C : ℕ), 1 ≤ p →
      (∀ m : ℕ, a (m + p) ≤ a m + C * (d * (m + p + 1) ^ (d - 1))) →
      ∃ C' : ℕ, ∀ m : ℕ, a m ≤ C' * ((d + 1) * (m + 1) ^ d) := by
  intro a d p C hp h
  have key : ∀ m : ℕ, a m ≤ (∑ j ∈ Finset.range p, a j) + C * (d * (m + 1) ^ (d - 1)) * m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      by_cases hm : m < p
      · exact le_trans (Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 hm)) (Nat.le_add_right _ _)
      · obtain ⟨n, rfl⟩ : ∃ n, m = n + p := ⟨m - p, by omega⟩
        have h1 := ih n (by omega)
        have h2 := h n
        have h3 : C * (d * (n + 1) ^ (d - 1)) * n ≤ C * (d * (n + p + 1) ^ (d - 1)) * n := by
          gcongr
          omega
        have h4 : C * (d * (n + p + 1) ^ (d - 1)) * (n + 1)
            ≤ C * (d * (n + p + 1) ^ (d - 1)) * (n + p) := by
          gcongr
        rw [Nat.mul_succ] at h4
        omega
  refine ⟨(∑ j ∈ Finset.range p, a j) + C, fun m => (key m).trans ?_⟩
  have h1 : 1 ≤ (d + 1) * (m + 1) ^ d := Nat.succ_le_of_lt (by positivity)
  have h2 : d * (m + 1) ^ (d - 1) * m ≤ (d + 1) * (m + 1) ^ d := by
    cases d with
    | zero => simp
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, mul_assoc]
      gcongr <;> omega
  rw [add_mul, mul_assoc C]
  exact add_le_add (Nat.le_mul_of_pos_right _ h1) (Nat.mul_le_mul_left _ h2)

end GlobalTheory
