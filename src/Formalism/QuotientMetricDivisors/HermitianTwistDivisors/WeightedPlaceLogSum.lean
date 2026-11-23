module

public import Formalism.QuotientMetricDivisors.ScalarLiftLowerBoundRows
public import Formalism.LogFactorialBounds.LogFactorialProofs.PrimeSum
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset NumberField IsDedekindDomain

noncomputable section

namespace Formalism.DivisionValues

namespace place_log_sum

end place_log_sum

theorem prime_log_sum_bound : PrimeLogSum := by
  intro Y hY s hs
  have hn : 1 ≤ ⌊Y⌋₊ := Nat.le_floor (by exact_mod_cast hY)
  have hnR : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by exact_mod_cast hn
  have hfl : (⌊Y⌋₊ : ℝ) ≤ Y := Nat.floor_le (by linarith)
  calc ∑ p ∈ s, Real.log (p : ℝ) / (p : ℝ)
      ≤ ∑ p ∈ Nat.primesLE ⌊Y⌋₊, Real.log (p : ℝ) / (p : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          exact Nat.mem_primesLE.2 ⟨Nat.le_floor (hs p hp).2, (hs p hp).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ ≤ Real.log (⌊Y⌋₊ : ℝ) + Real.log 4 := Formalism.LogFactorialBounds.sum_primesLE_log_div_le _ hn
    _ ≤ Real.log Y + Real.log 4 := by
        have := Real.log_le_log hnR hfl
        linarith

namespace place_log_sum

end place_log_sum

namespace place_log_sum

end place_log_sum

end Formalism.DivisionValues
