import Mathlib
import GroundTheory.AutomorphicForms.HermitianValues

noncomputable section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct NumberField IsDedekindDomain GroundTheory.Global

section Diagonalize

variable {F A : Type*} [Field F] [Field A] [Algebra F A] [Algebra.IsQuadraticExtension F A]
  [Algebra.IsSeparable F A]


end Diagonalize

section LocCongr

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def LocCongr (K : Type*) [Field K] [Algebra K E] [Algebra.IsQuadraticExtension K E] (R : Type*)
    [CommRing R] [Algebra K R] (H H' : Matrix ι ι E) : Prop :=
  IsCongr (conjBase K E R) (H.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))
    (H'.map (Algebra.TensorProduct.includeRight : E →ₐ[K] R ⊗[K] E))

variable {R : Type*} [CommRing R] [Algebra K R]

theorem LocCongr.trans {H H' H'' : Matrix ι ι E} (h : LocCongr K R H H') (h' : LocCongr K R H' H'') :
    LocCongr K R H H'' :=
  IsCongr.trans h h'

theorem LocCongr.symm {H H' : Matrix ι ι E} (h : LocCongr K R H H') : LocCongr K R H' H :=
  IsCongr.symm h

omit [Algebra.IsQuadraticExtension K E] in

theorem IsCongr.submatrix {B : Type*} [CommRing B] {s : B →+* B} {κ : Type*} [Fintype κ]
    [DecidableEq κ] (e : κ ≃ ι) {H H' : Matrix ι ι B} (h : IsCongr s H H') :
    IsCongr s (H.submatrix e e) (H'.submatrix e e) := by
  obtain ⟨P, hP, rfl⟩ := h
  refine ⟨P.submatrix e e, by rwa [det_submatrix_equiv_self], ?_⟩
  rw [← submatrix_map, transpose_submatrix, submatrix_mul_equiv, submatrix_mul_equiv]

theorem LocCongr.submatrix {κ : Type*} [Fintype κ] [DecidableEq κ] (e : κ ≃ ι)
    {H H' : Matrix ι ι E} (h : LocCongr K R H H') :
    LocCongr K R (H.submatrix e e) (H'.submatrix e e) := by
  unfold LocCongr at *
  rw [← submatrix_map, ← submatrix_map]
  exact IsCongr.submatrix e h

variable {V V' : Type*} [AddCommGroup V] [Module E V] [AddCommGroup V'] [Module E V']

variable (R) in

def HermitianForm.IsometricAt (h : HermitianForm K E V) (h' : HermitianForm K E V') : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) E V) (b' : Basis (Fin n) E V'),
    LocCongr K R (gram h'.toSesq b') (gram h.toSesq b)

end LocCongr

section Coordinates

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {d : K} {ψ : E ≃ₐ[K] QuadraticAlgebra K d 0} (hψ : ∀ x, ψ (conj K E x) = star (ψ x))
include hψ

abbrev diagE (E : Type*) [Field E] [Algebra K E] (a : ι → K) : Matrix ι ι E :=
  diagonal fun i => algebraMap K E (a i)

end Coordinates

section Main

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V] [AddCommGroup V']
  [Module E V'] [FiniteDimensional E V']

variable [NumberField K]

end Main

section Disc

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {d : K} {ψ : E ≃ₐ[K] QuadraticAlgebra K d 0}

variable [NumberField K]
variable {V V' : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V] [AddCommGroup V']
  [Module E V'] [FiniteDimensional E V']

end Disc

end GroundTheory.Automorphic
