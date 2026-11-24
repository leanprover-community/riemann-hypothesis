module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
public import Mathlib.Analysis.Analytic.Order
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionLogDerivLocalFormula
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

theorem _root_.GlobalTheory.T.rayClassLFunction_logDeriv_local_formula : ∃ C : ℝ, 0 < C ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (t : ℝ), {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}.Finite ∧ (∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℝ)) ≤ C * 𝓕.ell t ∧ ∀ s : ℂ, ‖s - (5 / 4 + t * I)‖ ≤ 1 / 2 → 𝓕.F χ s ≠ 0 → ‖deriv (𝓕.F χ) s / 𝓕.F χ s - ∑ᶠ w ∈ {w : ℂ | ‖w - (5 / 4 + t * I)‖ ≤ 3 / 5 ∧ 𝓕.F χ w = 0}, (analyticOrderNatAt (𝓕.F χ) w : ℂ) / (s - w)‖ ≤ C * 𝓕.ell t := by
  first | exact @GlobalTheory.HkLocal.logDeriv_local | exact GlobalTheory.HkLocal.logDeriv_local | (intros; apply GlobalTheory.HkLocal.logDeriv_local <;> assumption)
