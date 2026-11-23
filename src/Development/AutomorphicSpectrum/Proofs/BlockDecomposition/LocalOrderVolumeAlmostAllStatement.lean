module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrMMemFramesEIff
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalOrderVolumeAlmostAll
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
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsCovolOne

@[expose] public section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep

theorem _root_.GlobalTheory.T.local_order_volume_almost_all : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (N : ℕ) (J : Matrix (Fin N) (Fin N) E), IsHermND σ J → 3 ≤ N → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ O : Subring (Fv F v ⊗[F] E), (∀ y, y ∈ O ↔ ∀ k, (Algebra.TensorProduct.basis (Fv F v) b).repr y k ∈ v.adicCompletionIntegers F) → ∀ lam : Measure (Fv F v), IsStdV v lam → ∀ m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin N → Fv F v ⊗[F] E), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 N) (coordHerm (Fv F v) σ b lam 1) m → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (c : O), ¬ IsUnit c → IsUnit (c : Fv F v ⊗[F] E) → ∀ B : Set (Fin 1 → Fin N → Fv F v ⊗[F] E), MeasurableSet B → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) ((fun (X : Fin 1 → Fin N → Fv F v ⊗[F] E) a i => (c : Fv F v ⊗[F] E) * X a i) '' B) ≤ ENNReal.ofReal (1 / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) B := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.ScaleNonUnit.fibre_zero_image_le <;> assumption)
