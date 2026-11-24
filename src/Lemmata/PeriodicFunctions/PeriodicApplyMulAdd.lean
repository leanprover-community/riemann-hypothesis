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

open NumberField IsDedekindDomain Module

namespace Bl.PeriodicFunctions

variable {K : Type} [Field K]

private theorem periodic_apply_mul_add (M : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) (k x : ℕ) :
    g (M * k + x) = g x := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.mul_succ, show M * k + M + x = (M * k + x) + M by ring, hg, ih]

theorem goal1 (M m : ℕ) (g : ℕ → K) (hg : ∀ i, g (i + M) = g i) :
    ∑ i ∈ Finset.range (M * m), g i = (m : K) * ∑ i ∈ Finset.range M, g i := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih]
    simp only [periodic_apply_mul_add M g hg n]
    push_cast
    ring

end Bl.PeriodicFunctions
