import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.SpectralGap.CayleyIndepA

open Matrix

namespace GlobalTheory.CayleyUnitaryQuotient

variable {n : ℕ}

lemma star_mul_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Pᴴ * P = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hP

lemma mul_star_self {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P * Pᴴ = 1 := by
  simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hP

lemma inv_eq_star {P : Matrix (Fin n) (Fin n) ℂ} (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    P⁻¹ = Pᴴ :=
  Matrix.inv_eq_left_inv (star_mul_self hP)



lemma conj_eq {P Q : Matrix (Fin n) (Fin n) ℂ}
    (hP : P ∈ Matrix.unitaryGroup (Fin n) ℂ) (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) :
    Q⁻¹ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = P⁻¹ * g * P := by
  rw [inv_eq_star hP, inv_eq_star hQ]
  calc Qᴴ * (Q * Pᴴ * g * (P * Qᴴ)) * Q = (Qᴴ * Q) * (Pᴴ * g * P) * (Qᴴ * Q) := by
        simp only [Matrix.mul_assoc]
    _ = Pᴴ * g * P := by rw [star_mul_self hQ, Matrix.one_mul, Matrix.mul_one]


end GlobalTheory.CayleyUnitaryQuotient
