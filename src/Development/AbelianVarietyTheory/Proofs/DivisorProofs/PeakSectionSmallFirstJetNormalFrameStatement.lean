module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeakSectionSmallFirstJetNormalFrame
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

theorem _root_.GlobalTheory.T.peak_section_small_first_jet_normal_frame : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (H G : La) (i : ι) (p : V n) (r0 c Cq K : ℝ) (q : V n → ℂ), 0 < r0 → 0 < c → closedBall p r0 ⊆ (A.chart i).target → Differentiable ℂ q → (∀ v ∈ closedBall p r0, A.ph H i ((A.chart i).symm v) - 2 * (q v).re ≤ Cq * ‖v - p‖ ^ 2) → ∀ ε : ℝ, 0 < ε → ∃ k0 : ℕ, ∀ k ≥ k0, ∀ D : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) D → DifferentiableOn ℂ (D i ∘ (A.chart i).symm) (ball p r0) → n0 A (G + k • H) D ≤ ENNReal.ofReal (K * Real.exp (-c * k)) → ‖D i ((A.chart i).symm p) * Complex.exp (-(k * q p))‖ ≤ ε ∧ ‖fderiv ℂ (fun v => D i ((A.chart i).symm v) * Complex.exp (-(k * q v))) p‖ ≤ ε := by
  first | exact @GlobalTheory.JetSmall.main | exact GlobalTheory.JetSmall.main | (intros; apply GlobalTheory.JetSmall.main <;> assumption)
