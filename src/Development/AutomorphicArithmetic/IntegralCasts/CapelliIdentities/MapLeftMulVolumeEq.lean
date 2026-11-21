import Mathlib

private def UpperTheory.matrixSpaceLinearEquiv (n : ℕ) : (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun x := fun i j => x j i
  invFun x := fun i j => x j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def UpperTheory.matrixLeftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  (UpperTheory.matrixSpaceLinearEquiv n).toLinearMap ∘ₗ
    (LinearMap.pi fun j : Fin n => (Matrix.toLin' (Matrix.of a)).comp (LinearMap.proj j)) ∘ₗ
    (UpperTheory.matrixSpaceLinearEquiv n).symm.toLinearMap


