module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloLimitIncreasingWeights
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

theorem _root_.GlobalTheory.T.exists_holo_l2_bound_of_increasing_weights : ∀ (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M], ∀ (X : EtaleStein n M) (F0 : M → ℂ) (om : M → ℝ) (c : ℝ) (p : ℕ → M → ℝ) (q : M → ℝ) (F : ℕ → M → ℂ) (B : ℝ≥0∞), Continuous F0 → Continuous om → 0 < c → (∀ x, c ≤ om x ∧ om x ≤ 1) → (∀ k, SmoothR n X.z (p k)) → (∀ x, Antitone (fun k => p k x)) → (∀ x, Tendsto (fun k => p k x) atTop (𝓝 (q x))) → (∀ k, Holo n X.z (F k)) → B < ⊤ → (∀ k, ∫⁻ x, ENNReal.ofReal (‖F0 x - F k x‖ ^ 2 * (om x * Real.exp (-p k x))) ∂vol n X.z ≤ B) → ∃ G : M → ℂ, Holo n X.z G ∧ ∫⁻ x, ENNReal.ofReal (‖F0 x - G x‖ ^ 2 * (om x * Real.exp (-q x))) ∂vol n X.z ≤ B := by
  first | exact @GlobalTheory.holo_limit_increasing_weights | exact GlobalTheory.holo_limit_increasing_weights | (intros; apply GlobalTheory.holo_limit_increasing_weights <;> assumption)
