module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OfE
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaTestFunctionRayAsymptotic
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

theorem _root_.GlobalTheory.T.theta_test_function_ray_asymptotic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A → ∀ K : Set (AF F ⊗[F] E)ˣ, IsCompact K → ∃ (N : ℕ) (ρ : ℝ), 0 < N ∧ ∀ k ∈ K, ∀ (X : Fin 1 → Fin 1 → E) (ε : ℝ), 0 < ε → Psi φ A (fun a i => ((k * ofF (r ε) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) * inclR (AF F) (X a i)) ≠ 0 → (∀ (p : Fin 1 × Fin 1 × Fin d) (v : HeightOneSpectrum (𝓞 F)), algebraMap F (Fv F v) ((N : F) * b.repr (X p.1 p.2.1) p.2.2) ∈ v.adicCompletionIntegers F) ∧ ∀ (p : Fin 1 × Fin 1 × Fin d) (w : InfinitePlace F), ‖(θ ε * algebraMap F (Ainf F) ((N : F) * b.repr (X p.1 p.2.1) p.2.2)) w‖ ≤ ρ := by
  first | exact @GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | exact GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box | (intros; apply GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Box.unit_box <;> assumption)
