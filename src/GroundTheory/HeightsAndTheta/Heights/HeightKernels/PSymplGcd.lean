module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

namespace PSymplGcd

theorem of_gcd_ne_zero (a b : ℤ) (hc : (Int.gcd a b : ℤ) ≠ 0) :
    ∃ c a' b' x y : ℤ, a = c * a' ∧ b = c * b' ∧ x * a' + y * b' = 1 := by
  obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
  obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
  refine ⟨(Int.gcd a b : ℤ), a', b', Int.gcdA a b, Int.gcdB a b, ha', hb', ?_⟩
  have h := Int.gcd_eq_gcd_ab a b
  apply mul_left_cancel₀ hc
  linear_combination (-Int.gcdA a b) * ha' - Int.gcdB a b * hb' - h

end PSymplGcd

theorem SymplGcd.proof : SymplGcd.Statement := by
  intro a b
  by_cases hc : (Int.gcd a b : ℤ) = 0
  · have h0 : Int.gcd a b = 0 := by exact_mod_cast hc
    obtain ⟨rfl, rfl⟩ := Int.gcd_eq_zero_iff.mp h0
    exact ⟨0, 1, 0, 1, 0, by ring, by ring, by ring⟩
  · exact PSymplGcd.of_gcd_ne_zero a b hc

end GroundTheory.Heights₂.Heights
