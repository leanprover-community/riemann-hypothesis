module

public import Formalism.TruncatedSeriesCounting.RamifiedValuationInequality
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
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains

private lemma hCoef_num (x : ℝ) (hx : 11 ≤ x) : 0 ≤ 7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32 := by

  have hy : 0 ≤ x - 11 := by linarith
  nlinarith [mul_nonneg (mul_nonneg hy hy) hy, mul_nonneg hy hy]

theorem h_coefficient_bound : HCoef := by
  intro x hx
  have h0 : (0 : ℝ) < x := by linarith
  have h1 : (0 : ℝ) < x - 1 := by linarith
  have hx0 : x ≠ 0 := ne_of_gt h0
  have hx1 : x - 1 ≠ 0 := ne_of_gt h1
  have key := hCoef_num x hx
  have e : 32 / x ^ 2 - (8 * (2 * x - 1) / (x - 1) ^ 3 + 8 / (x - 1) ^ 2 + 1 / (x * (x - 1)))
      = (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) := by
    field_simp
    ring
  have hd : 0 ≤ (7 * x ^ 3 - 78 * x ^ 2 + 95 * x - 32) / (x ^ 2 * (x - 1) ^ 3) :=
    div_nonneg key (by positivity)
  linarith

end Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains
