module

public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Hat1
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

namespace GlobalTheory.UCls

open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

def IsUA (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUnit g.det ∧ ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y

def IsKM (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  IsUA c G k ∧ (∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ x - x = M • y) ∧ ∀ x ∈ hat F L, ∃ y ∈ hat F L, k *ᵥ y = x

def ratM (F : Type) [Field F] [NumberField F] [Algebra F E] (γ : Matrix (Fin n) (Fin n) E) :
    Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x

def UEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ)
    (g g' : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ γ : Matrix (Fin n) (Fin n) E, IsUA c G (ratM F γ) ∧ ∃ k, IsKM c G L M k ∧ g' = ratM F γ * g * k

def IsTA (c : E ≃ₐ[F] E) (t : RA F E) : Prop := t * sg (FiniteAdeleRing (𝓞 F) F) c t = 1

def TEquiv (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) (t t' : RA F E) : Prop :=
  ∃ u : E, u * c u = 1 ∧ ∃ k, IsKM c G L M k ∧ t' = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ u) * t * k.det

def torusNo (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (L : Set (Fin n → E)) (M : ℕ) : ℕ∞ :=
  ENat.card (Quot fun a b : {t // IsTA c t} => TEquiv c G L M a.1 b.1)


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
theorem _root_.GlobalTheory.UCls.isKM_one (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E)
    (L : Set (Fin n → E)) (M : ℕ) :
    _root_.GlobalTheory.UCls.IsKM c G L M 1 := by
  refine ⟨⟨by simp, fun x y => by simp only [one_mulVec]⟩, fun x _ => ⟨0, ?_, ?_⟩,
    fun x hx => ⟨x, hx, one_mulVec x⟩⟩
  · exact (_root_.GlobalTheory.AdLat.hat F L).zero_mem
  · simp

end GlobalTheory.UCls
