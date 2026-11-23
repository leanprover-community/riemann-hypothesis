module

public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoProdSmallBallAsymptotics
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
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

theorem _root_.GlobalTheory.T.tendsto_prod_smallBall_asymptotics : ∀ (X Y : Type) [MeasurableSpace X] [MeasurableSpace Y] (ν₁ : Measure X) (ν₂ : Measure Y) [IsFiniteMeasure ν₁] [IsFiniteMeasure ν₂] (ρ₁ : X → ℝ) (ρ₂ : Y → ℝ) (d₁ d₂ : ℕ) (C₁ C₂ : ℝ), Measurable ρ₁ → Measurable ρ₂ → (∀ x, 0 ≤ ρ₁ x) → (∀ y, 0 ≤ ρ₂ y) → 0 < C₁ → 0 < C₂ → Filter.Tendsto (fun r : ℝ => ν₁ {x | Real.sqrt (ρ₁ x) ≤ r} / ENNReal.ofReal (r ^ (d₁))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁))) 1))) → Filter.Tendsto (fun r : ℝ => ν₂ {x | Real.sqrt (ρ₂ x) ≤ r} / ENNReal.ofReal (r ^ (d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₂))) 1))) → Filter.Tendsto (fun r : ℝ => (ν₁.prod ν₂) {x | Real.sqrt (ρ₁ x.1 + ρ₂ x.2) ≤ r} / ENNReal.ofReal (r ^ (d₁ + d₂))) (nhdsWithin 0 (Set.Ioi 0)) (nhds (ENNReal.ofReal (C₁ * C₂) * volume (Metric.ball (0 : EuclideanSpace ℝ (Fin (d₁ + d₂))) 1))) := by
  first | exact @GlobalTheory.SmallBallProd.tendsto_prod_smallBall | exact GlobalTheory.SmallBallProd.tendsto_prod_smallBall | (intros; apply GlobalTheory.SmallBallProd.tendsto_prod_smallBall <;> assumption)
