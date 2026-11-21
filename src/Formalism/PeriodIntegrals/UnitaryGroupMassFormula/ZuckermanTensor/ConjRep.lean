import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ZuckermanTensor.DualChoice

open Matrix Finset
open scoped InnerProductSpace
noncomputable section
namespace PI.ZuckTensorWork
open PI.UpqRep PI.ZuckTensor

section Mat
variable {n : ℕ}

theorem revM_eq_submatrix (g : Matrix (Fin n) (Fin n) ℂ) :
    revM g = g.submatrix (Fin.revPerm : Fin n ≃ Fin n) (Fin.revPerm : Fin n ≃ Fin n) := by
  ext i j; simp [revM, Fin.revPerm_apply]

theorem revM_revM (g : Matrix (Fin n) (Fin n) ℂ) : revM (revM g) = g := by
  ext i j; simp [revM]


theorem revM_mul (a b : Matrix (Fin n) (Fin n) ℂ) : revM (a * b) = revM a * revM b := by
  rw [revM_eq_submatrix, revM_eq_submatrix, revM_eq_submatrix, Matrix.submatrix_mul_equiv]

theorem revM_one : revM (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  rw [revM_eq_submatrix, Matrix.submatrix_one_equiv]


theorem revM_conjTranspose (g : Matrix (Fin n) (Fin n) ℂ) : (revM g)ᴴ = revM gᴴ := by
  unfold revM; rw [Matrix.conjTranspose_submatrix]

theorem revM_diagonal (d : Fin n → ℂ) : revM (diagonal d) = diagonal (d ∘ Fin.rev) := by
  rw [revM_eq_submatrix, Matrix.submatrix_diagonal_equiv]
  congr 1

theorem revM_Jm (ε : Fin n → Bool) : revM (Jm ε) = Jm (revE ε) := by
  unfold Jm; rw [revM_diagonal]; rfl









end Mat

section Conj
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem Cj.mk_smul (c : ℂ) (x : H) : Cj.mk (c • x) = (starRingEnd ℂ) c • Cj.mk x := by
  show c • x = (starRingEnd ℂ) ((starRingEnd ℂ) c) • x
  rw [Complex.conj_conj]

theorem Cj.continuous_mk : Continuous (Cj.mk : H → Cj H) := continuous_id



variable {n : ℕ}














end Conj

section Wt
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {n : ℕ} {ε : Fin n → Bool}







end Wt





end PI.ZuckTensorWork
end
