module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

namespace Bl.DetMonotoneStarMulSelf

open Matrix in
open scoped ComplexOrder in
private theorem one_le_re_det_one_add {n : ℕ} (D : Matrix (Fin n) (Fin n) ℂ) (hD : D.PosSemidef) :
    1 ≤ (1 + D).det.re := by
  have hH : (1 + D).IsHermitian := isHermitian_one.add hD.isHermitian
  have key : ∀ i, 1 ≤ hH.eigenvalues i := fun i => by
    rw [hH.eigenvalues_eq i]
    have h1 : RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ ⇑(hH.eigenvectorBasis i)) = (1 : ℝ) := by
      rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hH.eigenvectorBasis.orthonormal.1 i]
      simp
    have h3 : 0 ≤ RCLike.re (star ⇑(hH.eigenvectorBasis i) ⬝ᵥ D *ᵥ ⇑(hH.eigenvectorBasis i)) :=
      (Complex.nonneg_iff.mp (hD.dotProduct_mulVec_nonneg (⇑(hH.eigenvectorBasis i)))).1
    rw [add_mulVec, one_mulVec, dotProduct_add, map_add (f := _), h1]
    linarith
  rw [hH.det_eq_prod_eigenvalues]
  have hp : (∏ i, ((hH.eigenvalues i : ℝ) : ℂ)).re = ∏ i, hH.eigenvalues i := by
    rw [← Complex.ofReal_prod, Complex.ofReal_re]
  refine le_of_le_of_eq ?_ hp.symm
  simpa using Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun i _ => key i)

open Matrix in
open scoped ComplexOrder MatrixOrder in
theorem goal1 : ∀ (n : ℕ), ReciprocityTheory.L2DbarEstimates.DetMonoStatement n := by
  intro n A B hB hAB
  have hA : A.PosSemidef := by simpa using hB.add hAB
  by_cases hdet : B.det = 0
  · rw [hdet, Complex.zero_re]
    exact (Complex.nonneg_iff.mp hA.det_nonneg).1
  · obtain ⟨X, hBX⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
    rw [star_eq_conjTranspose] at hBX
    have hXd : X.det ≠ 0 := fun h => hdet (by rw [hBX, det_mul, h, mul_zero])
    have hYX : X⁻¹ * X = 1 := nonsing_inv_mul X (isUnit_iff_ne_zero.mpr hXd)
    set D := (X⁻¹)ᴴ * (A - B) * X⁻¹ with hDdef
    have hD : D.PosSemidef := hAB.conjTranspose_mul_mul_same X⁻¹
    have h2 : Xᴴ * D * X = A - B := by
      calc Xᴴ * D * X = (X⁻¹ * X)ᴴ * (A - B) * (X⁻¹ * X) := by
            rw [hDdef, conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = A - B := by rw [hYX, conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    have hEq : A = Xᴴ * (1 + D) * X := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h2, ← hBX]; abel
    have hdA : A.det = (1 + D).det * B.det := by
      rw [hEq, det_mul, det_mul, hBX, det_mul]; ring
    have hu := one_le_re_det_one_add D hD
    have hu0 : (1 + D).det.im = 0 :=
      ((Complex.nonneg_iff.mp (PosSemidef.one.add hD).det_nonneg).2).symm
    have hw := (Complex.nonneg_iff.mp hB.det_nonneg).1
    rw [hdA, Complex.mul_re, hu0, zero_mul, sub_zero]
    nlinarith

end Bl.DetMonotoneStarMulSelf
