module

public import Mathlib

@[expose] public section

open scoped TensorProduct
open NumberField

namespace GlobalTheory

namespace HermForm

section Ring

variable {R M N P : Type*} [CommRing R] [StarRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

instance : FunLike (HermForm R M) M (M →ₗ⋆[R] R) where
  coe h := h.toSesq
  coe_injective f g H := by
    cases f; cases g; congr; exact DFunLike.coe_injective H

instance : LinearMapClass (HermForm R M) R M (M →ₗ⋆[R] R) where
  map_add h := h.toSesq.map_add
  map_smulₛₗ h := h.toSesq.map_smul

variable (h : HermForm R M)

@[simp] theorem star_apply (x y : M) : star (h x y) = h y x := h.star_apply' x y

variable {h}

namespace IsometryEquiv

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

instance : EquivLike (h₁.IsometryEquiv h₂) M N where
  coe f := f.toLinearEquiv
  inv f := f.toLinearEquiv.symm
  left_inv f := f.toLinearEquiv.left_inv
  right_inv f := f.toLinearEquiv.right_inv
  coe_injective' f g := by cases f; cases g; simp +contextual

instance : LinearEquivClass (h₁.IsometryEquiv h₂) R M N where
  map_add f := map_add f.toLinearEquiv
  map_smulₛₗ f := map_smulₛₗ f.toLinearEquiv

@[simp] theorem map_app (f : h₁.IsometryEquiv h₂) (x y : M) : h₂ (f x) (f y) = h₁ x y :=
  f.map_app' x y

@[simp] theorem apply_symm_apply (f : h₁.IsometryEquiv h₂) (x : N) : f (f.symm x) = x :=
  f.toLinearEquiv.apply_symm_apply x

end IsometryEquiv

namespace Isometric

variable {h₁ : HermForm R M} {h₂ : HermForm R N} {h₃ : HermForm R P}

end Isometric

namespace unitaryGroup

end unitaryGroup

end Ring

section Field

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}

end Field

section Complex

variable {V : Type*} [AddCommGroup V] [Module ℂ V] (h : HermForm ℂ V)

variable {h}

end Complex

end HermForm

universe u v

attribute [instance] HermModule.addCommGroup HermModule.module

attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite

attribute [simp] IsStarFixed.star_algebraMap

section IsStarFixed

variable (F E : Type*) [CommSemiring F] [CommSemiring E] [StarRing E] [Algebra F E]

variable [IsStarFixed F E]

variable {F E}

end IsStarFixed

namespace StarTensor

section NoStar

variable (F E A : Type*) [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]

variable {F E A}

variable {B C : Type*} [CommRing B] [CommRing C] [Algebra F B] [Algebra F C]

end NoStar

section Star

variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]

variable {B : Type*} [CommRing B] [Algebra F B]

end Star

end StarTensor

section RingOfIntegers

variable (K : Type*) [Field K] (V : Type*) [AddCommGroup V] [Module K V]

end RingOfIntegers

section CM

variable (E : Type*) [Field E] [NumberField E] [IsCMField E]

variable {E}

@[simp] theorem complexEmbedding_star (τ : E →+* ℂ) (x : E) : τ (star x) = star (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

noncomputable instance : StarRing (𝓞 E) where
  star := IsCMField.ringOfIntegersComplexConj E
  star_involutive x := RingOfIntegers.ext (star_star (x : E))
  star_mul x y := by rw [map_mul, mul_comm]
  star_add x y := map_add _ x y

namespace CMTensor

variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]

end CMTensor

end CM

end GlobalTheory
