module

public import Formalism.JumpKernelCokernel.Statement
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
