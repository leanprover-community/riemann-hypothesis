module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeakConvergenceOffZeroSet
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
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.weak_convergence_off_zero_set : ∀ {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (μT : ℝ → Measure X) (N : X → ℝ), IsFiniteMeasure μ → (∀ᶠ t in 𝓝[>] (0 : ℝ), IsFiniteMeasure (μT t)) → Continuous N → (∀ y, 0 ≤ N y ∧ N y ≤ 1) → μ {y | N y = 0} = 0 → (∀ᶠ t in 𝓝[>] (0 : ℝ), μT t {y | N y = 0} = 0) → (∀ (g : X → ℝ) (B : ℝ), Continuous g → (∀ y, |g y| ≤ B) → Tendsto (fun t => ∫ y, g y ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, g y ∂μ))) → (∀ η : ℝ, 0 < η → ∃ ε₀ t₁ : ℝ, 0 < ε₀ ∧ 0 < t₁ ∧ ∀ ε t : ℝ, 0 < ε → ε ≤ ε₀ → 0 < t → t ≤ t₁ → Integrable (fun y => Real.log (1 + ε / N y ^ 2)) (μT t) ∧ ∫ y, Real.log (1 + ε / N y ^ 2) ∂μT t ≤ η) → Integrable (fun y => -Real.log (N y)) μ ∧ (∀ᶠ t in 𝓝[>] (0 : ℝ), Integrable (fun y => -Real.log (N y)) (μT t)) ∧ Tendsto (fun t => ∫ y, -Real.log (N y) ∂μT t) (𝓝[>] 0) (𝓝 (∫ y, -Real.log (N y) ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | exact GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.tendsto_integral_neg_log_of_green_small <;> assumption)
