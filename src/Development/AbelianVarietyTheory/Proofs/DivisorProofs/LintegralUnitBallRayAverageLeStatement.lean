module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralUnitBallRayAverageLe
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

open MeasureTheory Filter Topology Set Module
open scoped ENNReal


theorem _root_.GlobalTheory.T.lintegral_unit_ball_ray_average_le : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (Ψ : E → ℝ≥0∞) (m : ℕ), Measurable Ψ → finrank ℝ E = m + 1 → ∫⁻ v in Metric.closedBall (0:E) 1, ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (t ^ m * ‖v‖ ^ (m + 1)) * Ψ (t • v) ∂volume ∂μ ≤ ENNReal.ofReal (1 / ((m : ℝ) + 1)) * ∫⁻ y, Ψ y ∂μ := by
  first | exact @GlobalTheory.rayAvg_bound | exact GlobalTheory.rayAvg_bound | (intros; apply GlobalTheory.rayAvg_bound <;> assumption)
