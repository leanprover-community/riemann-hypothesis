module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PshNormalFrameQuadraticComparison
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
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatCalcA

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.psh_normal_frame_quadratic_comparison : ∀ (n : ℕ) (O : Set (V n)) (φ : V n → ℝ) (p : V n), IsOpen O → p ∈ O → ContDiffOn ℝ ∞ φ O → (∀ ξ : Fin n → ℂ, ξ ≠ 0 → 0 < (leviV n (fun w => ((φ w : ℝ) : ℂ)) p ξ).re) → ∃ (q : V n → ℂ) (c C ρ : ℝ), Differentiable ℂ q ∧ 0 < c ∧ 0 < C ∧ 0 < ρ ∧ closedBall p ρ ⊆ O ∧ ∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ φ v - 2 * (q v).re ∧ φ v - 2 * (q v).re ≤ C * ‖v - p‖ ^ 2 := by
  first | exact @GlobalTheory.psh_normal_frame | exact GlobalTheory.psh_normal_frame | (intros; apply GlobalTheory.psh_normal_frame <;> assumption)
