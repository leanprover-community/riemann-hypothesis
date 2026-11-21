import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LFocksLemmas

section
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

lemma LFocks_subAdj {σ : Type*} [Fintype σ] [DecidableEq σ] (U : Matrix σ σ ℂ)
    (f g : MvPolynomial σ ℂ) :
    fockF (sub U f) g = fockF f (sub U.conjTranspose g) := by
  induction f using MvPolynomial.induction_on generalizing g
  · rename_i a
    rw [LFocks_sub_C, LFocks_C_left, LFocks_C_left,
      LFocks_constantCoeff_sub]
  · rename_i p q hp hq
    rw [map_add, Formalism.REAL.fischerInner_add_left, Formalism.REAL.fischerInner_add_left, hp, hq]
  · rename_i p i hp
    rw [map_mul, LFocks_sub_X, mul_comm p (X i), Formalism.REAL.fischerInner_X_mul_left i p,
      LFocks_pderiv_sub, Formalism.REAL.fischerInner_sum_right, Finset.mul_sum, Formalism.REAL.fischerInner_sum_left]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [LFocks_C_mul_right, ← hp, Matrix.conjTranspose_apply, star_star,
      mul_comm (sub U p), mul_assoc, LFocks_C_mul_left,
      Formalism.REAL.fischerInner_X_mul_left]

theorem fischerInnerSubstitutionAdjoint : FockSubAdj :=
  fun _ _ _ U f g => LFocks_subAdj U f g

end Formalism.GradedWeylDivisibility
end
end

section
open MvPolynomial Formalism.REAL

noncomputable section

namespace Formalism.GradedWeylDivisibility

def LFocks_rowMat {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    Matrix (Fin r × Fin n) (Fin r × Fin n) ℂ :=
  fun v w => if v.2 = w.2 then g v.1 w.1 else 0

lemma LFocks_rowAct_eq_sub {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    rowAct ℂ (n := n) g = sub (LFocks_rowMat g) := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [rowAct, sub, aeval_X, LFocks_rowMat]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_eq_single v.2]
  · simp
  · intro s _ hs; simp [Ne.symm hs]
  · simp

lemma LFocks_rowMat_conjTranspose {r n : ℕ} (g : Matrix (Fin r) (Fin r) ℂ) :
    (LFocks_rowMat (n := n) g).conjTranspose = LFocks_rowMat g.conjTranspose := by
  ext v w
  simp only [Matrix.conjTranspose_apply, LFocks_rowMat]
  by_cases h : v.2 = w.2
  · rw [if_pos h.symm, if_pos h]
  · rw [if_neg (Ne.symm h), if_neg h, star_zero]

theorem fischerInnerRowActionAdjoint : FockRowAdj := by
  intro r n g f h
  rw [LFocks_rowAct_eq_sub, LFocks_rowAct_eq_sub, LFocks_subAdj, LFocks_rowMat_conjTranspose]

end Formalism.GradedWeylDivisibility
end
end
