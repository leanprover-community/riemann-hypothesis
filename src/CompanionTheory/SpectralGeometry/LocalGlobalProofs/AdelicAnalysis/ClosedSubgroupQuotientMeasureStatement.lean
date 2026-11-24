module

public import Mathlib.MeasureTheory.Group.Measure
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ClosedSubgroupQuotientMeasure
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

@[expose] public section

open MeasureTheory Topology
open scoped ENNReal NNReal Matrix

theorem _root_.GlobalTheory.T.closed_subgroup_quotient_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (G₁ : Type) [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* G), IsClosedEmbedding ι → ∀ (μ₁ : Measure G₁) [μ₁.IsHaarMeasure] [μ₁.IsMulRightInvariant], ∃ w : G → ℝ≥0∞, Measurable w ∧ ∀ g, ∫⁻ u, w (ι u * g) ∂μ₁ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | exact GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset | (intros; apply GlobalTheory.CompanionTheory.SW.exists_weight_mass_one_right_coset <;> assumption)
