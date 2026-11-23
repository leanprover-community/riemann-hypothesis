module

public import Mathlib.Basic.Finite.Defs
public import Mathlib.Basic.Real.Basic
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCyclotomicExtensionQI
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.TwOrbMEqTwOrbUOfNormal
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Defs

@[expose] public section

open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.FinFix

theorem finite_den_bdd (N : ℕ) (hN : 0 < N) (R : ℝ) :
    {q : ℚ | (∃ k : ℤ, q * N = k) ∧ |(q : ℝ)| ≤ R}.Finite := by
  have hN' : (0 : ℚ) < N := by exact_mod_cast hN
  refine ((Set.finite_Icc (-⌈R * N⌉) ⌈R * N⌉).image (fun k : ℤ => (k : ℚ) / N)).subset ?_
  rintro q ⟨⟨k, hk⟩, hR⟩
  refine ⟨k, ?_, ?_⟩
  · have hkR : |(k : ℝ)| ≤ R * N := by
      have : (k : ℝ) = (q : ℝ) * N := by exact_mod_cast hk.symm
      rw [this, abs_mul, Nat.abs_cast]
      exact mul_le_mul_of_nonneg_right hR (Nat.cast_nonneg _)
    have h1 := abs_le.1 hkR
    constructor
    · have : -(R * N) ≤ (k : ℝ) := h1.1
      have h3 : (-⌈R * N⌉ : ℝ) ≤ k := by
        have := Int.le_ceil (R * N); push_cast; linarith
      exact_mod_cast h3
    · have h3 : (k : ℝ) ≤ ⌈R * N⌉ := le_trans h1.2 (Int.le_ceil _)
      exact_mod_cast h3
  · show (k : ℚ) / N = q
    rw [← hk]; field_simp

end GlobalTheory.FinFix
