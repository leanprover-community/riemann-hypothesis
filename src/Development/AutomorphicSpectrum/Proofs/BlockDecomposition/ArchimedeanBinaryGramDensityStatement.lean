module

public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanBinaryGramDensity
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
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

@[expose] public section

open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal

theorem _root_.GlobalTheory.T.archimedean_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)), IsStdInf li →
  ∀ (mi : HermR (Ainf F) σ 1 → Measure (Fin 1 → Fin 2 → Ainf F ⊗[F] E)),
  IsGramFib (Ainf F) σ J 1 (coordW (Ainf F) b li 1 2) (coordHerm (Ainf F) σ b li 1) mi →
  ∀ φ : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → ℝ, Continuous φ → HasCompactSupport φ → (∀ X, 0 ≤ φ X) →
  tsupport φ ⊆ {X | IsUnit (gramR (Ainf F) σ J X).det} →
  Continuous (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  HasCompactSupport (fun s : Ainf F => ∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∧
  (∀ s : Ainf F, ∫⁻ X, ENNReal.ofReal (φ X) ∂(mi (hermScal (Ainf F) σ s)) = ENNReal.ofReal (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s)))) ∧
  ENNReal.ofReal (∫ s, (∫ X, φ X ∂(mi (hermScal (Ainf F) σ s))) ∂li) = ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW (Ainf F) b li 1 2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | exact GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test | (intros; apply GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral_test <;> assumption)
