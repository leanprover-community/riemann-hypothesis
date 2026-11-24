module

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

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace PositivityTheory.PfSWUS.SchInf

open GlobalTheory.CompanionTheory.SW

def FamCont : Prop :=
  ∀ (N : ℕ) (X : Type) [TopologicalSpace X] (μ' : Measure (Fin N → ℝ)), μ'.IsAddHaarMeasure →
  ∀ (n : X → Measure (Fin N → ℝ)) (c : X) (O : Set X), IsOpen O → c ∈ O →
  (∀ f : (Fin N → ℝ) → ℝ≥0∞, Measurable f → ∫⁻ y, f y ∂μ' ≠ ⊤ →
      ∀ U : Set X, IsOpen U → U.Nonempty → ∃ s ∈ U, ∫⁻ y, f y ∂(n s) ≠ ⊤) →
  (∀ s₀ ∈ O, ∃ (L Linv : X → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) (Λ : X → ℝ≥0),
      ContinuousAt L c ∧ ContinuousAt Linv c ∧ ContinuousAt Λ c ∧
      (∀ s ∈ O, ∀ y, Linv s (L s y) = y) ∧ ∀ s ∈ O, n s = Λ s • (n s₀).map (L s)) →
  ∀ g : (Fin N → ℝ) → ℂ, Continuous g → (∀ k : ℕ, ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C * (1 + ‖y‖) ^ (-(k : ℝ))) →
    (∀ᶠ s in 𝓝 c, Integrable g (n s)) ∧ ContinuousAt (fun s => ∫ y, g y ∂(n s)) c

def SecInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n : ℕ) (c : HermR (Ainf F) σ n), IsUnit (c : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det →
  ∃ O : Set (HermR (Ainf F) σ n), IsOpen O ∧ c ∈ O ∧ ∀ S₀ ∈ O,
    ∃ h hinv : HermR (Ainf F) σ n → Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E),
      ContinuousOn h O ∧ ContinuousOn hinv O ∧
      ∀ S ∈ O, h S * hinv S = 1 ∧ hinv S * h S = 1 ∧
        (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) =
          cT (sigR (Ainf F) σ) (h S) * (S₀ : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) * h S

def CoordInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n M : ℕ), ∃ (N : ℕ) (eV : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)), Continuous eV ∧ Continuous eV.symm ∧
    ∃ L : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → (Fin N → ℝ) →L[ℝ] (Fin N → ℝ), Continuous L ∧
      ∀ g X, eV (rmul (Ainf F) X g) = L g (eV X)

def ScaleInf : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (n M : ℕ) (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure →
  ∃ A C : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E) → ℝ≥0,
    ContinuousOn A {g | IsUnit g.det} ∧ ContinuousOn C {g | IsUnit g.det} ∧
    ∀ g : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E), IsUnit g.det →
      A g ≠ 0 ∧ C g ≠ 0 ∧ μ.map (fun X => rmul (Ainf F) X g) = A g • μ ∧
      ∀ τ : HermR (Ainf F) σ n → HermR (Ainf F) σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)) = cT (sigR (Ainf F) σ) g * S * g) → ν.map τ = C g • ν

def FinOpen : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n))
    (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m →
  ∀ f : (Fin n → Fin M → Ainf F ⊗[F] E) → ℝ≥0∞, Measurable f → ∫⁻ X, f X ∂μ ≠ ⊤ →
  ∀ U : Set (HermR (Ainf F) σ n), IsOpen U → U.Nonempty → ∃ S ∈ U, ∫⁻ X, f X ∂(m S) ≠ ⊤

def DensInt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n : ℕ)
    (μ : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (ν : Measure (HermR (Ainf F) σ n))
    (m : HermR (Ainf F) σ n → Measure (Fin n → Fin M → Ainf F ⊗[F] E)),
    μ.IsAddHaarMeasure → ν.IsAddHaarMeasure → IsGramFib (Ainf F) σ J n μ ν m →
  ∀ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ, Continuous φ → Integrable φ μ →
    (∀ S : HermR (Ainf F) σ n, IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det → Integrable φ (m S)) →
    ContinuousOn (fun S => ∫ X, ‖φ X‖ ∂(m S)) {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} →
  ∀ K : Set (HermR (Ainf F) σ n), IsCompact K → K ⊆ {S | IsUnit (S : Matrix (Fin n) (Fin n) (Ainf F ⊗[F] E)).det} →
    ∫ X in gramR (Ainf F) σ J ⁻¹' (Subtype.val '' K), φ X ∂μ = ∫ S in K, (∫ X, φ X ∂(m S)) ∂ν

end PositivityTheory.PfSWUS.SchInf

end
