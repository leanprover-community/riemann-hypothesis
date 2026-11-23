module

public import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormPrimesImagQuadShortIntervalLowerBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
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

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.normPrimesImagQuad_short_interval_lower_bound : ∃ A c c' : ℝ, 0 < A ∧ 0 < c ∧ 0 < c' ∧ ∀ (d M : ℕ) (X h : ℝ), d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → 1 ≤ X → Real.log (4 * (d : ℝ) * (M : ℝ) ^ 2) ≤ c * Real.sqrt (Real.log X) → Real.exp (-c * Real.sqrt (Real.log X)) ≤ h → h ≤ 1 → c' * h * X / ((4 * (d : ℝ) * (M : ℝ) ^ 2) ^ A * Real.log X) ≤ ((GlobalTheory.Mem.An.normPrimes d M X (X * (1 + h))).card : ℝ) := by
  first | exact @GlobalTheory.Hk.normPrimes_short_interval_lower | exact GlobalTheory.Hk.normPrimes_short_interval_lower | (intros; apply GlobalTheory.Hk.normPrimes_short_interval_lower <;> assumption)
