module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulLintegralRpowLeOfShellBound
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis

@[expose] public section

open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal

theorem _root_.GlobalTheory.T.mul_lintegral_rpow_le_of_shell_bound' : ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (h : X → ℝ) (d : ℝ) (B : ℝ≥0∞), Measurable h → (∀ x, 0 < h x) → 0 < d → (∀ j : ℕ, μ {x | Real.exp (-(j + 1 : ℝ)) < h x ∧ h x ≤ Real.exp (-(j : ℝ))} ≤ B * ENNReal.ofReal (Real.exp (d * j))) → ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ENNReal.ofReal ε * ∫⁻ x, (if h x ≤ 1 then ENNReal.ofReal (h x ^ (d + ε)) else 0) ∂μ ≤ 2 * B := by
  first | exact @GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | exact GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound | (intros; apply GlobalTheory.ResLine.mul_lintegral_rpow_le_of_shell_bound <;> assumption)
