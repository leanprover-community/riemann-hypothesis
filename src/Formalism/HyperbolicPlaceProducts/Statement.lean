module

public import Mathlib

@[expose] public section

open Module

noncomputable section

namespace Formalism.SLP

def TorsionIndexEq : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ),
    Nat.card A = Nat.card (nsmulAddMonoidHom g : A →+ A).range *
      Nat.card (nsmulAddMonoidHom g : A →+ A).ker

def TorsionIndex : Prop :=
  ∀ (A : Type) [AddCommGroup A] [Finite A] (g : ℕ) (K : AddSubgroup A),
    (∀ x ∈ K, g • x = 0) →
    Nat.card (nsmulAddMonoidHom g : A →+ A).range * Nat.card K ≤ Nat.card A

section Place

variable {𝕜 : Type*} [RCLike 𝕜]
  {W W' : Type*} [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
  [NormedAddCommGroup W'] [InnerProductSpace 𝕜 W']

end Place

def SesqDet : Prop :=
  ∀ (V₁ V₂ : Type) [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ), (∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) →
    ∀ (m : ℕ) (u : Fin m → V₁) (w : Fin m → V₂),
      ‖(Matrix.of fun i j => B (u i) (w j)).det‖ ^ 2 ≤
        c ^ (2 * m) * ‖(Matrix.gram ℂ u).det‖ * ‖(Matrix.gram ℂ w).det‖

def SubmoduleCountDed : Prop :=
  ∀ (R M : Type) [CommRing R] [IsDedekindDomain R] [AddCommGroup M]
    [Module R M] [Finite M] (e : ℕ) (v : Fin e → M), Submodule.span R (Set.range v) = ⊤ →
    Nat.card (Submodule R M) ≤ Nat.card M ^ e

def SubmoduleIndexCountO : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M]
    [Module (NumberField.RingOfIntegers E) M] [Module.Finite (NumberField.RingOfIntegers E) M]
    [Module.Projective (NumberField.RingOfIntegers E) M] (j : ℕ), 1 ≤ j →
    {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.Finite ∧
      {N : Submodule (NumberField.RingOfIntegers E) M | N.toAddSubgroup.index = j}.ncard ≤
        finrank ℚ E ^ (Nat.primeFactorsList j).length *
          j ^ finrank (NumberField.RingOfIntegers E) M

def OmegaPow : Prop :=
  ∀ n j : ℕ, 1 ≤ n → 1 ≤ j →
    (n : ℝ) ^ (Nat.primeFactorsList j).length ≤ (j : ℝ) ^ Real.logb 2 n

end Formalism.SLP
