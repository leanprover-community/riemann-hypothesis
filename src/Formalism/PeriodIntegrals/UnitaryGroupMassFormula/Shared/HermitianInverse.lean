import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

namespace Formalism.MassFormulaShared
open Matrix

/-- The inverse adjoint is a left inverse of a Hermitian matrix. -/
theorem inverseAdjoint_mul {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]
    (σ : K →+* K) (T : Matrix ι ι K) (hT : (T.map σ)ᵀ = T) (hu : IsUnit T.det) :
    (T⁻¹.map σ)ᵀ * T = 1 := by
  calc
    (T⁻¹.map σ)ᵀ * T = (T⁻¹.map σ)ᵀ * (T.map σ)ᵀ := by rw [hT]
    _ = ((T.map σ) * (T⁻¹.map σ))ᵀ := (Matrix.transpose_mul _ _).symm
    _ = ((T * T⁻¹).map σ)ᵀ := by rw [Matrix.map_mul]
    _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.transpose_one]

end Formalism.MassFormulaShared
