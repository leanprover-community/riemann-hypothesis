module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RandomSetSumExpectation
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
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsDoubleComplexVanish

@[expose] public section

set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal


theorem _root_.GlobalTheory.T.random_set_sum_expectation : ∀ {Ω Y : Type} [MeasurableSpace Ω] [MeasurableSpace Y] (P : Measure Ω) (ν : Measure Y)
  (L : Ω → Set Y) (φ : Y → ℝ≥0∞) (c : ℝ≥0∞), Measurable φ →
  (∀ s : ℝ≥0∞, Measurable fun ω => (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞)) →
  (∀ s : ℝ≥0∞, ∫⁻ ω, (((L ω ∩ {y | s < φ y}).encard : ℕ∞) : ℝ≥0∞) ∂P = c * ν {y | s < φ y}) →
    Measurable (fun ω => ∑' y : L ω, φ y) ∧ ∫⁻ ω, ∑' y : L ω, φ y ∂P = c * ∫⁻ y, φ y ∂ν := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.LayerCake.measurable_lintegral_tsum_of_level_counts <;> assumption)
