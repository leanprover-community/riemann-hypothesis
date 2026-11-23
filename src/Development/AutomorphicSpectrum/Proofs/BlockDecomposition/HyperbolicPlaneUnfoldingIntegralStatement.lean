module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicPlaneUnfoldingIntegral
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.hyperbolic_plane_unfolding_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ n : ℕ, 1 ≤ n → 2 * n < M → ∀ (μ : Measure (HA (AF F) σ (hypOne J))) 𝓕, IsHaarH F E σ (M + 2) (hypOne J) μ → IsFDH F E σ (M + 2) (hypOne J) μ 𝓕 → ∀ (μ₁ : Measure (HA (AF F) σ J)) 𝓕₁, IsHaarH F E σ M J μ₁ → IsFDH F E σ M J μ₁ 𝓕₁ → ∀ dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E), IsCovolOne dA → ∀ (Φ : (Fin (n + 1) → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞) (Ψ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞), Measurable Φ → Measurable Ψ → (∀ h : HA (AF F) σ (hypOne J), Ψ (actW (AF F) σ (hypOne J) h (e0 _ M)) = ∫⁻ Y, ∫⁻ a, Φ (actW (AF F) σ (hypOne J) h (consA a Y)) ∂dA ∂(thetaMeas σ J μ₁ 𝓕₁ (framesE σ J (0 : Matrix (Fin n) (Fin n) E)))) → ∫⁻ X, Φ X ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin (n + 1)) (Fin (n + 1)) E))) = ∫⁻ y, Ψ y ∂(thetaMeas σ (hypOne J) μ 𝓕 (framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.unfold_frames <;> assumption)
