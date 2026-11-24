module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Mathlib.NumberTheory.LSeries.Basic
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionFamilyContinuationGrowth
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical

theorem _root_.GlobalTheory.T.rayClassLFunctionFamily_continuation_growth : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  first | exact @GlobalTheory.Hk.RayCont.continuation_growth | exact GlobalTheory.Hk.RayCont.continuation_growth | (intros; apply GlobalTheory.Hk.RayCont.continuation_growth <;> assumption)
