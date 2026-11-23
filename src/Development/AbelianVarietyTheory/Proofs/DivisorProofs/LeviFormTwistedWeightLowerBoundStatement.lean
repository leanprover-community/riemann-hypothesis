module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviFormTwistedWeightLowerBound
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.leviForm_twisted_weight_lower_bound : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (z : M → V n) (φ ψ : M → ℝ) (δ : ℝ) (κ : ℝ → ℝ), IsLocalHomeomorph z → SmoothR n z φ → SmoothR n z ψ → (∀ x, ψ x ≤ 0) → 0 < δ → ContDiff ℝ ∞ κ → (∀ t, t ≤ 0 → 0 ≤ deriv κ t ∧ deriv κ t ≤ 1) → (∀ α ∈ Set.Icc (1 : ℝ) (1 + δ), LeviNonneg n z (fun x => φ x + α * ψ x)) → SmoothR n z (fun x => κ (δ * ψ x)) ∧ ∀ (x : M) (ξ : Fin n → ℂ), dbarDot n z (fun y => ((κ (δ * ψ y) : ℝ) : ℂ)) x ξ = ((deriv κ (δ * ψ x) * δ : ℝ) : ℂ) * dbarDot n z (fun y => (ψ y : ℂ)) x ξ ∧ deriv (deriv κ) (δ * ψ x) * (δ ^ 2 * ‖dbarDot n z (fun y => (ψ y : ℂ)) x ξ‖ ^ 2) ≤ (Levi n z (fun y => (φ y + ψ y) + κ (δ * ψ y)) x ξ).re := by
  first | exact @GlobalTheory.LeviTwistLower.main | exact GlobalTheory.LeviTwistLower.main | (intros; apply GlobalTheory.LeviTwistLower.main <;> assumption)
