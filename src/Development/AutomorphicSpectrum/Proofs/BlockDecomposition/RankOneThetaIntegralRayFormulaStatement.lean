module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayFormula
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

theorem _root_.GlobalTheory.T.rank_one_theta_integral_ray_formula : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∀ ε₁ : ℝ, ∃ C : ℝ≥0, ∀ k ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ ε₁ → ENNReal.ofReal (ε ^ (2 * Module.finrank ℚ F)) * Th φ A (k * ofF (r ε)) ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound <;> assumption)
