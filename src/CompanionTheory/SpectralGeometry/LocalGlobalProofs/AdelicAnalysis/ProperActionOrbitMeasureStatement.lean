module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ProperActionOrbitMeasure
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

theorem _root_.GlobalTheory.T.proper_action_orbit_measure : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (V : Type) [TopologicalSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (act : G → V → V), (Continuous fun p : G × V => act p.1 p.2) → (∀ x, act 1 x = x) → (∀ g h x, act (g * h) x = act g (act h x)) → ∀ Z : Set V, IsClosed Z → (∀ g, ∀ x ∈ Z, act g x ∈ Z) → (∀ x ∈ Z, ∀ y ∈ Z, ∃ g, act g x = y) → ∀ (μ ν : Measure V), IsLocallyFiniteMeasure μ → IsLocallyFiniteMeasure ν → μ Zᶜ = 0 → ν Zᶜ = 0 → (∀ g, μ.map (act g) = μ) → (∀ g, ν.map (act g) = ν) → ν ≠ 0 → ∃ c : ℝ≥0, μ = c • ν := by
  first | exact @GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | exact GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique | (intros; apply GlobalTheory.CompanionTheory.SW.AbsUniq.invariant_measure_unique <;> assumption)
