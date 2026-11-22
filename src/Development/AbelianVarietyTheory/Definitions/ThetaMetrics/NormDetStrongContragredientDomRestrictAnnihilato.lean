module

public import Mathlib

@[expose] public section

open Module Matrix
open scoped InnerProductSpace ComplexOrder

noncomputable section

namespace GlobalTheory

variable {𝕜 : Type*} [RCLike 𝕜]
variable {V W X : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup W] [InnerProductSpace 𝕜 W] [NormedAddCommGroup X] [InnerProductSpace 𝕜 X]
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable (𝕜) in
def gramVol (v : ι → V) : ℝ := √(RCLike.re (gram 𝕜 v).det)

theorem gramVol_nonneg (v : ι → V) : 0 ≤ gramVol 𝕜 v := Real.sqrt_nonneg _

theorem gramVol_sq (v : ι → V) : ((gramVol 𝕜 v : ℝ) : 𝕜) ^ 2 = (gram 𝕜 v).det := by
  have h := (posSemidef_gram 𝕜 v).det_nonneg
  rw [RCLike.nonneg_iff] at h
  rw [← RCLike.ofReal_pow, gramVol, Real.sq_sqrt h.1]
  apply RCLike.ext <;> simp [h.2]

theorem gramVol_eq_of_sq {v : ι → V} {r : ℝ} (hr : 0 ≤ r) (h : (r : 𝕜) ^ 2 = (gram 𝕜 v).det) :
    gramVol 𝕜 v = r := by
  rw [← gramVol_sq] at h
  have : r ^ 2 = gramVol 𝕜 v ^ 2 := by exact_mod_cast h
  exact ((sq_eq_sq₀ hr (gramVol_nonneg v)).mp this).symm

theorem gramVol_of_orthonormal {v : ι → V} (hv : Orthonormal 𝕜 v) : gramVol 𝕜 v = 1 :=
  gramVol_eq_of_sq zero_le_one (by simp [gram_eq_one_iff_orthonormal.mpr hv])

@[simp] theorem gramVol_unique [Unique ι] (v : ι → V) : gramVol 𝕜 v = ‖v default‖ := by
  rw [gramVol_of_pairwise_orthogonal (Subsingleton.pairwise), Fintype.prod_unique]

omit [DecidableEq ι] [Fintype κ] [DecidableEq κ] in
theorem gram_sum_smul (v : ι → V) (Y : Matrix ι κ 𝕜) :
    gram 𝕜 (fun j => ∑ i, Y i j • v i) = Yᴴ * gram 𝕜 v * Y := by
  ext a b
  simp only [gram_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right, Matrix.mul_apply,
    conjTranspose_apply, Finset.sum_mul, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem gramVol_sum_smul (v : ι → V) (Y : Matrix ι ι 𝕜) :
    gramVol 𝕜 (fun j => ∑ i, Y i j • v i) = ‖Y.det‖ * gramVol 𝕜 v := by
  refine gramVol_eq_of_sq (mul_nonneg (norm_nonneg _) (gramVol_nonneg v)) ?_
  rw [gram_sum_smul, det_mul, det_mul, det_conjTranspose, ← gramVol_sq, RCLike.star_def]
  push_cast
  rw [mul_pow, ← RCLike.conj_mul]
  ring

theorem gramVol_eq_norm_det (b : OrthonormalBasis ι 𝕜 V) (v : ι → V) :
    gramVol 𝕜 v = ‖(b.toBasis.toMatrix v).det‖ := by
  have h := gramVol_sum_smul (b : ι → V) (b.toBasis.toMatrix v)
  rw [gramVol_of_orthonormal b.orthonormal, mul_one] at h
  rw [← h]
  congr 1
  ext j
  simpa [Basis.toMatrix_apply] using (b.sum_repr (v j)).symm

section NormDet

variable [FiniteDimensional 𝕜 V]

variable [FiniteDimensional 𝕜 W]

end NormDet

section Dual

open InnerProductSpace

variable [FiniteDimensional 𝕜 V] [FiniteDimensional 𝕜 W] [FiniteDimensional 𝕜 X]

end Dual

end GlobalTheory
