module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDens
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UpperDensityBoundsAlmostHomogeneousMeasure
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

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

theorem _root_.GlobalTheory.T.upperDensity_bounds_almost_homogeneous_measure : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (l ν : Measure V) [l.IsAddHaarMeasure] [IsFiniteMeasure ν] (c : ℝ≥0∞), c ≠ ⊤ → Tendsto (fun r : ℝ => ν (Metric.ball 0 r) / l (Metric.ball 0 r)) (𝓝[>] 0) (𝓝 c) → ∀ ε η : ℝ, 0 < ε → ε < 1 → (∀ x : V, ‖x‖ < η → ∀ᶠ r in 𝓝[>] (0:ℝ), ν (Metric.ball x ((1 - ε) * r)) ≤ ν (Metric.ball 0 r) ∧ ν (Metric.ball 0 r) ≤ ν (Metric.ball x ((1 + ε) * r))) → ∀ x : V, ‖x‖ < η → ENNReal.ofReal ((1 + ε)⁻¹ ^ Module.finrank ℝ V) * c ≤ GlobalTheory.HaarDensChart.upperDens l ν x ∧ GlobalTheory.HaarDensChart.upperDens l ν x ≤ ENNReal.ofReal (((1 + ε) / (1 - ε)) ^ Module.finrank ℝ V) * c := by
  first | exact @GlobalTheory.upperDens_bounds_of_almost_homogeneous | exact GlobalTheory.upperDens_bounds_of_almost_homogeneous | (intros; apply GlobalTheory.upperDens_bounds_of_almost_homogeneous <;> assumption)
