module

public import Mathlib

@[expose] public section

noncomputable section

namespace Formalism.WachCohomologyFacts

structure Base (O A : Type) [CommRing O] [CommRing A] [Algebra O A] where
  ℓ : ℕ
  hℓ : ℓ.Prime
  X : A
  u : A
  c : A
  φ : A →ₐ[O] A
  γ : A →ₐ[O] A
  hu : IsUnit u
  hc : IsUnit c
  comm : ∀ a, φ (γ a) = γ (φ a)
  γ_bij : Function.Bijective γ
  hφX : φ X = u * X * (X + (ℓ : A)) ^ (ℓ - 1)
  hγX : γ X - X = c * X * (X + (ℓ : A))
  γ_modX : ∀ a, γ a - a ∈ Ideal.span {X}

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

def Base.q (B : Base O A) : A := B.X + (B.ℓ : A)

def Base.p (B : Base O A) (s : ℕ) : A := (⇑B.φ)^[s] B.q

variable {AA : Type} [CommRing AA] [Algebra O AA] [Algebra A AA] [IsScalarTower O A AA]

namespace WachDatum

variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]
variable (W : WachDatum E n V)

end WachDatum

section Hom

variable {B : Base O A} {E : Amb B AA} {n : ℕ}
variable {V₁ : Type} [AddCommGroup V₁] [Module AA V₁] [Module A V₁] [IsScalarTower A AA V₁]
  [Module O V₁] [IsScalarTower O AA V₁]
variable {V₂ : Type} [AddCommGroup V₂] [Module AA V₂] [Module A V₂] [IsScalarTower A AA V₂]
  [Module O V₂] [IsScalarTower O AA V₂]

namespace Hom

variable {W₁ : WachDatum E n V₁} {W₂ : WachDatum E n V₂} (h : Hom W₁ W₂)

end Hom

end Hom

def ContractBij : Prop :=
  ∀ (R P : Type) [CommRing R] [AddCommGroup P] [Module R P] (I : Ideal R) [IsAdicComplete I P]
    (f : P →+ P),
    (∀ k : ℕ, ∀ x ∈ (I ^ k • ⊤ : Submodule R P), f x ∈ (I ^ (k + 1) • ⊤ : Submodule R P)) →
    Function.Bijective (fun x => f x - x)

def LenBound : Prop :=
  ∀ (O M : Type) [CommRing O] [AddCommGroup M] [Module O M] (ℓ g e : ℕ)
    (Z Bc I : Submodule O M) (s : Finset M),
    s.card ≤ g → Submodule.span O (s : Set M) ⊔ Bc = Z → Bc ≤ I →
    (∀ p ∈ Z, (ℓ ^ e : ℕ) • p ∈ I) →
    Module.length O (↥Z ⧸ I.comap Z.subtype) ≤
      (g : ℕ∞) * (e : ℕ∞) * Module.length O (O ⧸ Ideal.span {(ℓ : O)})

end Formalism.WachCohomologyFacts
