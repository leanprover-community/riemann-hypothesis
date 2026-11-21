import Mathlib

section
namespace GlobalTheory.CommonAlgClosedExtension

open scoped TensorProduct

theorem exists_common_algClosed_extension (K₀ K K' : Type) [Field K₀] [Field K] [Field K']
    (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      RingHom.comp j i = RingHom.comp j' i' := by
  letI : Algebra K₀ K := i.toAlgebra
  letI : Algebra K₀ K' := i'.toAlgebra
  haveI : Nontrivial (K ⊗[K₀] K') := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[K₀] K')
  letI : Field ((K ⊗[K₀] K') ⧸ m) := Ideal.Quotient.field m
  let φ : (K ⊗[K₀] K') →+* AlgebraicClosure ((K ⊗[K₀] K') ⧸ m) :=
    (algebraMap ((K ⊗[K₀] K') ⧸ m) _).comp (Ideal.Quotient.mk m)
  refine ⟨AlgebraicClosure ((K ⊗[K₀] K') ⧸ m), inferInstance, inferInstance,
    φ.comp (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).toRingHom,
    φ.comp (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).toRingHom, ?_⟩
  ext x
  have h1 := (Algebra.TensorProduct.includeLeft (R := K₀) (S := K₀) (A := K) (B := K')).commutes x
  have h2 := (Algebra.TensorProduct.includeRight (R := K₀) (A := K) (B := K')).commutes x
  exact congrArg φ (h1.trans h2.symm)

end GlobalTheory.CommonAlgClosedExtension
end

section
open scoped TensorProduct

namespace GlobalTheory

theorem exists_algClosed_join_of_two_field_extensions
    (K₀ K K' : Type) [Field K₀] [Field K] [Field K'] (i : K₀ →+* K) (i' : K₀ →+* K') :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (j : K →+* Ω) (j' : K' →+* Ω),
      j.comp i = j'.comp i' := by
  first
  | exact @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension
  | (apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CommonAlgClosedExtension.exists_common_algClosed_extension ..)

end GlobalTheory
end
