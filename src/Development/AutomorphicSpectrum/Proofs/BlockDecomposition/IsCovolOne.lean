module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Free

def e0 (K : Type) [Zero K] [One K] (M : ℕ) : Fin 1 → Fin (M + 2) → K :=
  fun _ => Fin.cons 1 fun _ => 0

def consA {K : Type} [Zero K] [One K] {M n : ℕ} (a : Fin 1 → Fin n → K) (Y : Fin n → Fin M → K) :
    Fin (n + 1) → Fin (M + 2) → K :=
  Fin.cons (Fin.cons 1 fun _ => 0) fun j => Fin.cons (a 0 j) (Fin.cons 0 (Y j))

section PiLocalization₂

variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]

def stageInt (σ : E →ₐ[F] E) {M n d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (lam : Measure R) (m' : Measure (Fin n → Fin M → R ⊗[F] E))
    (φ : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞) (g : HA R σ (hypOne J)) : ℝ≥0∞ :=
  ∫⁻ Y, ∫⁻ a, φ (actW R σ (hypOne J) g (consA a Y)) ∂(coordW R b lam 1 n) ∂m'

end PiLocalization₂

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def latStab (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) (g : HA (Fv F v) σ J) : Prop :=
  ∀ x : Fin 1 → Fin M → Fv F v ⊗[F] E, actW (Fv F v) σ J g x ∈ latV b v ↔ x ∈ latV b v

def primV (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (v : HeightOneSpectrum (𝓞 F)) : Set (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) :=
  {y | ∃ g : HA (Fv F v) σ (hypOne J), latStab σ (hypOne J) b v g ∧
    actW (Fv F v) σ (hypOne J) g (e0 _ M) = y}

def purePr (σ : E →ₐ[F] E) {M d : ℕ} (J : Matrix (Fin M) (Fin M) E) (b : Module.Basis (Fin d) F E)
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Ψinf : (Fin 1 → Fin (M + 2) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 2) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E) : ℝ≥0∞ :=
  {y : Fin 1 → Fin (M + 2) → AF F ⊗[F] E | ∀ v, v ∉ S → projV v (projFin y) ∈ primV σ J b v}.indicator
    (fun Y => Ψinf (projInf Y) * ∏ v ∈ S, Ψ v (projV v (projFin Y))) y

def ratA (n : ℕ) : AddSubgroup (Fin 1 → Fin n → AF F ⊗[F] E) where
  carrier := Set.range (ratTup (AF F) : (Fin 1 → Fin n → E) → Fin 1 → Fin n → AF F ⊗[F] E)
  zero_mem' := ⟨0, by funext a i; simp [ratTup]⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by funext a i; simp [ratTup]⟩
  neg_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by funext a i; simp [ratTup]⟩

def IsCovolOne {n : ℕ} (dA : Measure (Fin 1 → Fin n → AF F ⊗[F] E)) : Prop :=
  dA.IsAddHaarMeasure ∧ ∃ D : Set (Fin 1 → Fin n → AF F ⊗[F] E),
    IsAddFundamentalDomain (ratA (F := F) (E := E) n) D dA ∧ dA D = 1

end Adelic

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep
