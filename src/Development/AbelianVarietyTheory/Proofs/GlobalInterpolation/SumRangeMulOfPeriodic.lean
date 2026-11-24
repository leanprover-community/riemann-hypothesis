module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace GlobalTheory.PeriodicSumShift

theorem periodic_shift {K : Type} (g : ℕ → K) (N : ℕ) (h : ∀ i, g (N + i) = g i) :
    ∀ k i, g (N * k + i) = g i := by
  intro k
  induction k with
  | zero => intro i; simp
  | succ k ih => intro i; rw [Nat.mul_succ, add_assoc, ih, h]

theorem sum_range_mul_of_periodic : ∀ {K : Type} [inst : Field K] (g : ℕ → K) (N : ℕ),
    (∀ (i : ℕ), g (N + i) = g i) → ∀ (k : ℕ),
      ∑ i ∈ Finset.range (N * k), g i = (↑k : K) * ∑ i ∈ Finset.range N, g i := by
  intro K _ g N h k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp_rw [periodic_shift g N h k]
    push_cast; ring

end GlobalTheory.PeriodicSumShift
