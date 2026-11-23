module

public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelComparisonLimit
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
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ConjugateHermitianLineIsometries

@[expose] public section

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)

theorem _root_.GlobalTheory.T.root_model_comparison_limit : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M₁ M₂ : GlobalTheory.CompanionTheory.Ar.Top.RootModel Ψ N) (σ : Type) [Fintype σ] [DecidableEq σ] (ℓ₁ : ℝ → σ → HermLine M₁.ι) (ℓ₂ : ℝ → σ → HermLine M₂.ι) (n : Ψ × Fin N → σ → ℤ) (s : Ψ × Fin N → Ψ × Fin N) (e₁ e₂ : ℕ), e₁ ≠ 0 → e₁ * M₁.δ = e₂ * M₂.δ → (∀ᶠ t in 𝓝[>] (0 : ℝ), (∀ a, IsSmoothHerm (ℓ₁ t a) ∧ IsSmoothHerm (ℓ₂ t a)) ∧ (∀ r, (M₁.x t (s r)).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).a ∧ ∀ z ∈ mcPts M₁.P, (M₁.x t (s r)).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₁ t) (n r)).h z) ∧ ∀ r, (M₂.x t r).a = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).a ∧ ∀ z ∈ mcPts M₂.P, (M₂.x t r).h z = (GlobalTheory.CompanionTheory.Ar.Top.combLine (ℓ₂ t) (n r)).h z) → (∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → σ, Tendsto (fun t => (e₁ : ℝ) * II _ _ M₁.P _ (fun j => ℓ₁ t (w j)) - (e₂ : ℝ) * II _ _ M₂.P _ (fun j => ℓ₂ t (w j))) (𝓝[>] 0) (𝓝 0)) → ∀ w : Fin (GlobalTheory.CompanionTheory.Ar.Top.dimFl Ψ N + 1) → Ψ × Fin N, Tendsto (fun t => II _ _ M₁.P _ (fun j => M₁.x t (s (w j))) / M₁.δ - II _ _ M₂.P _ (fun j => M₂.x t (w j)) / M₂.δ) (𝓝[>] 0) (𝓝 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | exact GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.Root.cmp_root <;> assumption)
