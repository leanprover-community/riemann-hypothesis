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

namespace GlobalTheory.UnRep

open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def hermE (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) : E :=
  ∑ a, ∑ b, x a * G a b * c (y b)

def IsUnE (c : E ≃ₐ[F] E) {n : ℕ} (G γ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∀ x y, hermE c G (γ *ᵥ x) (γ *ᵥ y) = hermE c G x y

def IsHermForm (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) : Prop :=
  (∀ x, c (c x) = x) ∧ c ≠ 1 ∧ (∀ a b, c (G a b) = G b a) ∧ G.det ≠ 0

def refl (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (u : E) : Matrix (Fin n) (Fin n) E :=
  1 + ((u - 1) / hermE c G x x) • Matrix.vecMulVec x (G *ᵥ fun b => c (x b))

def Moved (c : E ≃ₐ[F] E) (P : Ideal (𝓞 E)) : Prop :=
  ∃ a ∈ P, ∃ b : 𝓞 E, (b : E) = c (a : E) ∧ b ∉ P

def SplitOr (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∨ (N : 𝓞 E) ∈ P

def SplitOff (c : E ≃ₐ[F] E) (N : ℕ) (s : 𝓞 E) : Prop :=
  s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → Moved c P ∧ (N : 𝓞 E) ∉ P

def CongAt {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ v ∈ L, ∃ w ∈ L, t • (δ *ᵥ v - v) = D • w

variable [NumberField F]

def IsUnA (c : E ≃ₐ[F] E) {n : ℕ} (G : Matrix (Fin n) (Fin n) E) (g : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∀ x y, hermA c G (g *ᵥ x) (g *ᵥ y) = hermA c G x y


variable (F) in
def fm {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) : Matrix (Fin n) (Fin n) (RA F E) :=
  γ.map fun x => (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ x


variable (F) in
def CongAtA {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (k : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ t : ℕ, t.Coprime N ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)),
    t • (k *ᵥ z - z) = D • w

def SplitPl (c : E ≃ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : Prop :=
  ∃ P : Ideal (𝓞 E), P.IsPrime ∧ P.comap (algebraMap (𝓞 F) (𝓞 E)) = v.asIdeal ∧ Moved c P

def SuppSplit (c : E ≃ₐ[F] E) {n : ℕ} (N : ℕ) (h : Matrix (Fin n) (Fin n) (RA F E)) : Prop :=
  ∃ e : FiniteAdeleRing (𝓞 F) F, e * e = e ∧ {v | e v ≠ 0}.Finite ∧
    (∀ v, e v ≠ 0 → SplitPl c v ∧ (N : 𝓞 F) ∉ v.asIdeal) ∧ (e ⊗ₜ[F] (1 : E)) • (h - 1) = h - 1

end GlobalTheory.UnRep
