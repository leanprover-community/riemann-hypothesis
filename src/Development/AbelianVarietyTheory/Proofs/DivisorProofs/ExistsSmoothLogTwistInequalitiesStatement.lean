module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothLogTwistInequalities
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_smooth_log_twist_inequalities : ∀ T : ℝ, 300 ≤ T → ∃ κ : ℝ → ℝ, ContDiff ℝ ∞ κ ∧ (∃ C : ℝ, ∀ x, x ≤ 0 → |κ x| ≤ C) ∧ (∀ x, x ≤ 0 → 0 ≤ deriv κ x ∧ deriv κ x ≤ 1 ∧ 0 < deriv (deriv κ) x ∧ deriv κ x ^ 2 ≤ deriv (deriv κ) x ∧ wT T x / 8 ≤ (1 - deriv κ x ^ 2 / deriv (deriv κ) x) * Real.exp (κ x)) ∧ (∀ x, -T - 1 ≤ x → x ≤ -T + 1 → Real.exp (κ x) / deriv (deriv κ) x ≤ 16 / 3 ∧ wT T x / 8 ≤ (1 - 5 * (deriv κ x ^ 2 / deriv (deriv κ) x)) * Real.exp (κ x)) := by
  first | exact @GlobalTheory.OTY.exists_log_twist | exact GlobalTheory.OTY.exists_log_twist | (intros; apply GlobalTheory.OTY.exists_log_twist <;> assumption)
