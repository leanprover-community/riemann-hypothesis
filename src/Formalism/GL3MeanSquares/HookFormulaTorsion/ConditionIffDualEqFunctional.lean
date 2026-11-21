import Mathlib
import Formalism.GL3MeanSquares.FourierTransformKernelSurjective

namespace Formalism.HermitianLattices.LocalLatticeBases

open Finset Matrix




section Count

variable {F : Type} [Field F]

private noncomputable def dotProductDual (m : ℕ) : (Fin m → F) →ₗ[F] Module.Dual F (Fin m → F) :=
  LinearMap.mk₂ F (fun a b => a ⬝ᵥ b) (fun a b c => add_dotProduct a b c)
    (fun c a b => smul_dotProduct c a b) (fun a b c => dotProduct_add a b c)
    (fun c a b => dotProduct_smul c a b)



private noncomputable def functionalWithScalar {n : ℕ} (fL : (Fin n → F) →ₗ[F] F) (c : F) :
    ((Fin n → F) × F) →ₗ[F] F :=
  fL.coprod (c • LinearMap.id)




variable [Fintype F]




end Count

section FJ

variable {F : Type} [Field F] [Fintype F]


end FJ


section Onto

open Formalism.LogVandermondeBounds.product_first_zeroth_parts

section FFOnto

variable {k : Type*} [Field k] [Fintype k] [DecidableEq k] {r : ℕ}







private def unitSmulEquiv (c : kˣ) : (Fin r → k) ≃ (Fin r → k) where
  toFun f := (c : k) • f
  invFun f := ((c⁻¹ : kˣ) : k) • f
  left_inv f := by simp [smul_smul]
  right_inv f := by simp [smul_smul]




end FFOnto


end Onto

end Formalism.HermitianLattices.LocalLatticeBases
