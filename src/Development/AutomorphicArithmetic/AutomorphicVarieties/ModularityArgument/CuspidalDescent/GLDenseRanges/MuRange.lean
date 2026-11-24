module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.CmpPrime
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

open Polynomial TensorProduct UpperTheory.V.Alg UpperTheory.V.J

namespace UpperTheory.V.Z.Desc.V0

section

variable {O Λ B K : Type} [CommRing O] [CommRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B] [Algebra O K]
  (lam : Λ →ₐ[O] B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] (hs : ∀ (a : Λ) (m : M), a • m = lam a • m)

def muE (e : Module.End Λ M) (x : B →ₐ[O] K) : ℕ :=
  letI : Algebra Λ K := (x.comp lam).toRingHom.toAlgebra
  Module.finrank K ↥((⨅ a : B, Module.End.maxGenEigenspace ((actL lam M hs a).baseChange K) (x a)) ⊓
    Module.End.eigenspace (e.baseChange K) 1)


variable (B) {M} in
def Idem (e : Module.End Λ M) : Prop := e * e = e ∧ ∀ (b : B) (m : M), e (b • m) = b • e m

end

def UnrAlgW : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsNoetherianRing Λ] [IsIntegrallyClosed Λ] [CharZero Λ] [CommRing B]
    [Field K] [CharZero K] [IsAlgClosed K] [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type)
    [AddCommGroup M] [Module B M] [Module Λ M] (h : Dat lam J M) (x : B →ₐ[O] K), J ≤ RingHom.ker x →
    ∀ (𝒢 : Set (B →ₐ[O] K)) (b₀ : B), x b₀ ≠ 0 → (∀ a : B, (∀ y ∈ 𝒢, y a = 0) → a * b₀ ∈ J) →
    (∀ y ∈ 𝒢, J ≤ RingHom.ker y ∧ mu lam M h.hs x ≤ mu lam M h.hs y) →
    ∀ δ ∈ PtDer x K, (∀ a ∈ J, δ a = 0) → (∀ c, δ (lam c) = 0) → δ = 0

def MuRange : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ] [CommRing B] [Field K] [Algebra O Λ] [Algebra O B]
    [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B) (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] (h : Dat lam J M)
    (e : Module.End Λ M), Idem B e →
    ∃ (J' : Ideal B) (M' : Type) (_ : AddCommGroup M') (_ : Module B M') (_ : Module Λ M') (h' : Dat lam J' M'), J ≤ J' ∧
      ∀ y : B →ₐ[O] K, mu lam M' h'.hs y = muE lam M h.hs e y ∧ (1 ≤ muE lam M h.hs e y → J' ≤ RingHom.ker y)

def UnrAlgE : Prop :=
  ∀ (O Λ B K : Type) [CommRing O] [CommRing Λ] [IsDomain Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsIntegrallyClosed Λ] [CharZero Λ]
    [CommRing B] [Field K] [CharZero K] [IsAlgClosed K] [Algebra O Λ] [Algebra O B] [Algebra O K] (lam : Λ →ₐ[O] B) (J : Ideal B)
    (M : Type) [AddCommGroup M] [Module B M] [Module Λ M] (h : Dat lam J M) (e : Module.End Λ M), Idem B e → ∀ x : B →ₐ[O] K,
    ∀ (𝒢 : Set (B →ₐ[O] K)) (b₀ : B), x b₀ ≠ 0 → (∀ a : B, (∀ y ∈ 𝒢, y a = 0) → a ∈ J) → 1 ≤ muE lam M h.hs e x →
    (∀ y ∈ 𝒢, y b₀ ≠ 0 → muE lam M h.hs e x ≤ muE lam M h.hs e y) →
    ∀ δ ∈ PtDer x K, (∀ a ∈ J, δ a = 0) → (∀ c, δ (lam c) = 0) → δ = 0

end UpperTheory.V.Z.Desc.V0
