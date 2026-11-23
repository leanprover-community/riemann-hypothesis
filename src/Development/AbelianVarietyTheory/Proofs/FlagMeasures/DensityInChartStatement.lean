module

public import Formalism.PeriodIntegrals.QuotInv
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DensityInChart
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

@[expose] public section

open MeasureTheory Matrix Filter Topology Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

theorem _root_.GlobalTheory.T.tendsto_measure_image_ball_div_volume : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)) (c : ℝ≥0∞), PI.IsMatGroup S → PI.IsHaarOnM S μ → HasDens S μ c → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (Φ : E → Matrix (Fin m) (Fin m) ℂ) (L : E ≃L[ℝ] lieE S), Φ 0 = 1 → (∀ᶠ x in 𝓝 (0 : E), Φ x ∈ S) → (∀ i j, ∃ D : E →L[ℝ] ℂ, HasStrictFDerivAt (fun x => Φ x i j) D 0 ∧ ∀ v, D v = unrealify ((L v : lieE S) : EuclideanSpace ℝ _) i j) → Tendsto (fun ρ : ℝ => μ ((fun x => Matrix.of.symm (Φ x)) '' Metric.ball 0 ρ) / volume (L '' Metric.ball (0 : E) ρ)) (𝓝[>] 0) (𝓝 c) := by
  first | exact @GlobalTheory.ChartDensity.density_in_chart | exact GlobalTheory.ChartDensity.density_in_chart | (intros; apply GlobalTheory.ChartDensity.density_in_chart <;> assumption)
