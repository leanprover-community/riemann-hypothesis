import Mathlib
import Formalism.HermitianLattices.StatementTheta
import Formalism.HermitianLattices.GenusCovolBound

section
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

def ThetaLEuclid : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (NumberField.RingOfIntegers K) V] [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
    (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V) (γ : V) (τ : ℂ),
      thetaL h L γ τ = thetaE (zmap ι L) (ι γ) τ

def ThetaLSLaw : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ (N : ℕ) (ι : V →+ EuclideanSpace ℝ (Fin N)),
      (∀ x y : V, inner ℝ (ι x) (ι y) = ((Algebra.trace ℚ K (h x y) : ℚ) : ℝ)) →
    ∀ (L : Submodule (NumberField.RingOfIntegers K) V),
      ∀ [DiscreteTopology (zmap ι L)] [IsZLattice ℝ (zmap ι L)],
    ∀ (γ : V) (τ : ℂ), 0 < τ.im →
      thetaL h L γ (-τ⁻¹) =
        (-Complex.I * τ) ^ ((N : ℂ) / 2) / (ZLattice.covolume (zmap ι L) : ℂ) *
          ∑' μ : tdualSub h L,
            Complex.exp (2 * Real.pi * Complex.I * ((Algebra.trace ℚ K (h γ μ) : ℚ) : ℂ)) *
            Complex.exp (Real.pi * Complex.I * τ * ((Algebra.trace ℚ K (h μ μ) : ℚ) : ℂ))

end Formalism.HermitianLatticesTheory
end
end

section
open Module Formalism.K

noncomputable section

namespace Formalism.HermitianLatticesTheory

section Defs

variable {K V : Type*} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (NumberField.RingOfIntegers K) V]

abbrev discr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) : Type _ :=
  (tdualSub h L) ⧸ (L.comap (tdualSub h L).subtype)

def drep (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (δ : discr h L) : V :=
  ((Submodule.mkQ_surjective (L.comap (tdualSub h L).subtype) δ).choose : tdualSub h L)

def qDiscr (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V)
    (δ : discr h L) : ℂ :=
  Complex.exp (Real.pi * Complex.I *
    ((Algebra.trace ℚ K (h (drep h L δ) (drep h L δ)) : ℚ) : ℂ))

variable [IsScalarTower (NumberField.RingOfIntegers K) K V]

def thetaVec (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (NumberField.RingOfIntegers K) V) (τ : ℂ)
    (δ : discr h L) : ℂ :=
  thetaL h L (drep h L δ) τ

end Defs

def ThetaWeil : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    L ≤ tdualSub h L → (∀ x ∈ L, ∃ n : ℤ, Algebra.trace ℚ K (h x x) = 2 * n) →
    ∀ [Fintype (discr h L)],
      IsUQuad (qDiscr h L) ∧ Nondeg (qDiscr h L) ∧
      (∀ τ : ℂ, thetaVec h L (τ + 1) = weilT (qDiscr h L) (thetaVec h L τ)) ∧
      ∀ τ : ℂ, 0 < τ.im →
        thetaVec h L (-τ⁻¹) = fun δ =>
          (-Complex.I * τ) ^ (((Module.finrank ℚ K * Module.finrank K V : ℕ) : ℂ) / 2) *
            weilS (qDiscr h L) (thetaVec h L τ) δ

def DiscrFinite : Prop :=
  ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (NumberField.RingOfIntegers K) V]
    [IsScalarTower (NumberField.RingOfIntegers K) K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K), h.IsSymm →
    (∀ x : V, x ≠ 0 → 0 < Algebra.trace ℚ K (h x x)) →
    ∀ L : Submodule (NumberField.RingOfIntegers K) V, Submodule.IsLattice K L →
    L ≤ tdualSub h L → Finite (discr h L)

end Formalism.HermitianLatticesTheory
end
end
