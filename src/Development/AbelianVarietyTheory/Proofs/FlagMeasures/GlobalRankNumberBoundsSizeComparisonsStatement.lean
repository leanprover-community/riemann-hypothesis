module

public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SecondLabelsNonempty
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GlobalRankNumberBoundsSizeComparisons
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open GlobalTheory.Diag.PG

theorem _root_.GlobalTheory.T.globalRankNumberBounds_size_comparisons : ∀ eps CD : ℝ, 0 < eps → eps < 1 / 52 → 3 ≤ CD → ∀ C : ℝ, 0 < C → ∃ x0 : ℝ, ∀ x, x0 ≤ x → ∀ m f k lrd Del : ℝ, RankNums x eps CD m f k lrd Del → 1 ≤ Del ∧ C * (m * k * Del) ≤ Real.sqrt (bx x eps) ∧ max (k ^ C) (bx x eps ^ ((1 : ℝ) / 4)) ≤ Real.sqrt (bx x eps) ∧ 12 * k * Del ≤ Real.sqrt (bx x eps) ∧ Real.sqrt (bx x eps) ≤ bx x eps ^ 2 ∧ bx x eps ^ 2 ≤ bx x eps ^ (3 : ℝ) ∧ (C ≤ CD → (k * f * x ^ eps) ^ C ≤ Del) := by
  first | exact @GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | exact GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes | (intros; apply GlobalTheory.Diag.PG.SqrtBound.rankNums_sizes <;> assumption)
