module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.OpenPartialHomeomorph.Defs
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.C2TendstoPullbackThroughChart
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
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
import ReciprocityTheory.AnalyticForms.LeviForms.IsRegFamilyInhabitStatement
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff

theorem _root_.GlobalTheory.T.C2_tendsto_pullback_through_chart : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (c : OpenPartialHomeomorph X (Fin e → ℂ)) (g : ℝ → (Fin e → ℂ) → ℝ) (p : (Fin e → ℂ) → ℝ) (K' : Set (Fin e → ℂ)), K' ⊆ c.target → (TendstoUniformlyOn g p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (g t)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ (g t))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ (g t) z - fderiv ℝ p z‖ ≤ M * t) → (TendstoUniformlyOn (fun t => (g t ∘ c) ∘ c.symm) p (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ ((g t ∘ c) ∘ c.symm)) (fderiv ℝ p) (𝓝[>] 0) K' ∧ TendstoUniformlyOn (fun t => fderiv ℝ (fderiv ℝ ((g t ∘ c) ∘ c.symm))) (fderiv ℝ (fderiv ℝ p)) (𝓝[>] 0) K' ∧ ∃ M : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K', ‖fderiv ℝ ((g t ∘ c) ∘ c.symm) z - fderiv ℝ p z‖ ≤ M * t) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | exact GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback | (intros; apply GlobalTheory.CompanionTheory.Metric.ChartPullBack.C2_tendsto_chart_pullback <;> assumption)
