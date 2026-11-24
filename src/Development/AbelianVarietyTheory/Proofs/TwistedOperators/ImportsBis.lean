module

public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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

namespace GlobalTheory.OneAddPowBoundTwistedOperators

theorem one_add_pow_le : ∀ {L : ℝ}, (0 : ℝ) ≤ L → ∀ (N : ℕ), ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N * ((1 : ℝ) + L ^ N) := by
  intro L hL N
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ N := by positivity
  have hLN : (0 : ℝ) ≤ L ^ N := pow_nonneg hL N
  rcases le_total L 1 with h | h
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 : ℝ) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    nlinarith
  · have h1 : ((1 : ℝ) + L) ^ N ≤ (2 * L) ^ N := pow_le_pow_left₀ (by linarith) (by linarith) N
    rw [mul_pow] at h1
    nlinarith

end GlobalTheory.OneAddPowBoundTwistedOperators
