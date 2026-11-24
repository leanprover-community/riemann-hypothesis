module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneSiegelWeilThetaAverage
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

theorem _root_.GlobalTheory.T.rank_one_siegel_weil_theta_average : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)), IsHaarH F E σ 1 J μ → IsFDH F E σ 1 J μ 𝓕 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ x : (AF F ⊗[F] E)ˣ, mean σ J μ 𝓕 φ A x = (μ 𝓕)⁻¹ * ∫⁻ h in 𝓕, Th φ A (x * ue (AF F) σ J h⁻¹) ∂μ ∧ Measurable fun h : HA (AF F) σ J => Th φ A (x * ue (AF F) σ J h⁻¹) := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint <;> assumption)
