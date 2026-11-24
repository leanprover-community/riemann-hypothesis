module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Order.CompletePartialOrder
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DominatedConvergenceExhaustion
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

theorem _root_.GlobalTheory.T.dominated_convergence_exhaustion : ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (l : Filter ℝ) [l.NeBot] [l.IsCountablyGenerated] (E : ℕ → Set α) (L : α → ℝ) (ρ Γ : ℝ → α → ℝ) (ρ0 Γ0 : α → ℝ) (a : ℝ) (b : ℕ → ℝ), (∀ n, MeasurableSet (E n)) → Monotone E → (∀ n, μ (E n) < ⊤) → (∀ᵐ y ∂μ, ∃ n, y ∈ E n) → (∀ᵐ y ∂μ, 0 ≤ L y) → 0 ≤ a → Tendsto b atTop (𝓝 0) → (∀ n, TendstoUniformlyOn ρ ρ0 l (E n)) → (∀ n, TendstoUniformlyOn Γ Γ0 l (E n)) → (∀ n, ∃ M : ℝ, ∀ y ∈ E n, |ρ0 y| ≤ M ∧ |Γ0 y| ≤ M) → (∀ᶠ t in l, AEStronglyMeasurable (ρ t) μ ∧ AEStronglyMeasurable (Γ t) μ ∧ (∀ᵐ y ∂μ, 0 ≤ ρ t y) ∧ (∀ᵐ y ∂μ, y ∉ E 0 → |Γ t y| ≤ a * L y) ∧ ∀ n, IntegrableOn (fun y => L y * ρ t y) (E n)ᶜ μ ∧ ∫ y in (E n)ᶜ, L y * ρ t y ∂μ ≤ b n) → Integrable (fun y => Γ0 y * ρ0 y) μ ∧ (∀ᶠ t in l, Integrable (fun y => Γ t y * ρ t y) μ) ∧ Tendsto (fun t => ∫ y, Γ t y * ρ t y ∂μ) l (𝓝 (∫ y, Γ0 y * ρ0 y ∂μ)) := by
  first | exact @GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | exact GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion | (intros; apply GlobalTheory.CompanionTheory.Conv.tendsto_integral_of_exhaustion <;> assumption)
