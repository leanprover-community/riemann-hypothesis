module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeakSectionSmallDbarEnergy
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
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem _root_.GlobalTheory.T.exists_peak_section_small_dbar_energy : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (H G : La) (i : ι) (p : V n) (ρ c : ℝ) (q f : V n → ℂ), 0 < ρ → 0 < c → closedBall p ρ ⊆ (A.chart i).target → Differentiable ℂ q → Differentiable ℂ f → (∀ v ∈ closedBall p ρ, c * ‖v - p‖ ^ 2 ≤ A.ph H i ((A.chart i).symm v) - 2 * (q v).re) → ∃ K : ℝ, 0 ≤ K ∧ ∀ k : ℕ, ∃ F0 : ι → Y → ℂ, A.IsSSec (A.kap + (G + k • H)) F0 ∧ (∀ v ∈ ball p (ρ / 2), F0 i ((A.chart i).symm v) = f v * Complex.exp (k * q v)) ∧ (∀ j y, y ∉ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ → F0 j y = 0) ∧ n1 C (G + k • H) F0 ≤ ENNReal.ofReal (K * Real.exp (-(c * ρ ^ 2 / 4) * k)) := by
  first | exact @GlobalTheory.OTY.peak_section | exact GlobalTheory.OTY.peak_section | (intros; apply GlobalTheory.OTY.peak_section <;> assumption)
