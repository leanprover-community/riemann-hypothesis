import Formalism.HyperbolicPlaceProducts.DetIndexProductHyperbolicInequality

namespace Formalism.SLP.GlobalBoundRefinements.P
open Formalism.SLP.GlobalBoundRefinements

theorem matrix_entries_integral (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.conjTranspose * J * M = J) :
    ‖M 0 0‖ ^ 2 - ‖M 1 0‖ ^ 2 = 1 ∧ ‖M 0 1‖ ^ 2 - ‖M 1 1‖ ^ 2 = -1 ∧
      ‖M 0 0‖ * ‖M 0 1‖ = ‖M 1 0‖ * ‖M 1 1‖ := by
  have e00 := congrFun (congrFun hM 0) 0
  have e11 := congrFun (congrFun hM 1) 1
  have e01 := congrFun (congrFun hM 0) 1
  simp [J, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply] at e00 e11 e01
  rw [Complex.conj_mul', Complex.conj_mul'] at e00 e11
  refine ⟨?_, ?_, ?_⟩
  · exact_mod_cast e00
  · exact_mod_cast e11
  · have h : (starRingEnd ℂ) (M 0 0) * M 0 1 = (starRingEnd ℂ) (M 1 0) * M 1 1 := by
      linear_combination e01
    have := congrArg norm h
    simpa [norm_mul] using this



end Formalism.SLP.GlobalBoundRefinements.P
