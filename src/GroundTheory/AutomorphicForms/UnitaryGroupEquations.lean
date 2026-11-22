module

public import Mathlib
public import GroundTheory.AutomorphicForms.UnitaryGroupScheme

@[expose] public section

namespace GroundTheory.Automorphic

open Module Matrix TensorProduct

variable {F E : Type*} [Field F] [CommRing E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {κ : Type*} [Fintype κ] (b : Basis κ F E)

section Coordinates

variable (R : Type*) [CommRing R] [Algebra F R] {S : Type*} [CommRing S] [Algebra F S]

noncomputable def matrixCoords : Matrix ι ι (R ⊗[F] E) ≃ (ι × ι × κ → R) where
  toFun g p := (Algebra.TensorProduct.basis R b).repr (g p.1 p.2.1) p.2.2
  invFun x i j := (Algebra.TensorProduct.basis R b).repr.symm
    (Finsupp.equivFunOnFinite.symm fun k => x (i, j, k))
  left_inv g := by
    ext i j
    simp
  right_inv x := by
    funext ⟨i, j, k⟩
    simp

variable {R}

end Coordinates

end GroundTheory.Automorphic
