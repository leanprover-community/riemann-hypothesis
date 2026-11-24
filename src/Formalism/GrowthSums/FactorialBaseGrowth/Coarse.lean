module

public import Formalism.GrowthSums.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open scoped BigOperators
open Finset

namespace Formalism.GrowthSums

theorem factorial_add_prod (m k : ℕ) :
    (((m + k).factorial : ℕ) : ℚ) =
      (m.factorial : ℚ) * (k.factorial : ℚ) * ∏ y ∈ Ico 1 (k + 1), (1 + (m : ℚ) / y) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : m + (k + 1) = (m + k) + 1 := by omega
    rw [h1, Nat.factorial_succ (m + k), Nat.factorial_succ k,
      Finset.prod_Ico_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    rw [ih]
    have hk : (k : ℚ) + 1 ≠ 0 := by positivity
    field_simp
    ring

theorem coarseUnit_succ (P n : ℕ) (hP : 1 ≤ P) :
    coarseUnit P (n + 1) = coarseUnit P n * ∏ y ∈ Ico 1 P, (1 + (P : ℚ) * n / y) := by
  have hPq : (P : ℚ) ≠ 0 := by exact_mod_cast (show P ≠ 0 by omega)
  have key := factorial_add_prod (P * n) P
  push_cast at key
  rw [Finset.prod_Ico_succ_top hP, mul_div_cancel_left₀ _ hPq] at key
  have hfP : (P.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero P
  have hfn : (n.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hn1 : (n : ℚ) + 1 ≠ 0 := by positivity
  unfold coarseUnit
  rw [show P * (n + 1) = P * n + P by ring, key, Nat.factorial_succ n]
  push_cast
  field_simp
  ring

theorem blockFactorialQuotientProd : CoarseUnitProd := by
  intro P n hP
  induction n with
  | zero => simp [coarseUnit]
  | succ n ih => rw [coarseUnit_succ P n hP, ih, Finset.prod_range_succ]

end Formalism.GrowthSums
