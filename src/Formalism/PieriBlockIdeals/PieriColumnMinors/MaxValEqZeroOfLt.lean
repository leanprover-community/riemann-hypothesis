module

public import Formalism.RankGapBounds.CloudMinFalse
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
public import Mathlib.Data.Nat.Prime.Factorial
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

open Finset

namespace Formalism.CohomologicalDescent

theorem max_val_eq_zero_of_lt (l n : ℕ) (h : n < l) : Formalism.RankGapBounds.JumpSetsAlt.maxVal l n = 0 := by
  unfold Formalism.RankGapBounds.JumpSetsAlt.maxVal
  apply le_antisymm _ (Nat.zero_le _)
  apply Finset.sup_le
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hp : l.Prime
  · apply le_of_eq
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hd
    have hdf : l ∣ n.factorial := hd.trans ⟨i.factorial * (n - i).factorial, by
      rw [← Nat.choose_mul_factorial_mul_factorial hi']; ring⟩
    have := (Nat.Prime.dvd_factorial hp).mp hdf
    omega
  · exact (Nat.factorization_eq_zero_of_not_prime _ hp).le

end Formalism.CohomologicalDescent
