import Formalism.HermitianCurvature.StatementLE
namespace Formalism.FourierDecayAlt.P.LEx2
open Formalism.FourierDecayAlt.LE
open MeasureTheory Filter Topology Finset










theorem onBoxes_mem (S : Sys) : ∀ w : List ℝ, S.OnBoxes w → ∀ y ∈ w, ∃ a, a < w.length ∧ y ∈ S.box a := by
  intro w
  induction w with
  | nil => intro _ y hy; simp at hy
  | cons Y w ih =>
    intro h y hy
    rcases List.mem_cons.mp hy with rfl | hy'
    · exact ⟨w.length, by simp, h.1⟩
    · obtain ⟨a, ha, hm⟩ := ih h.2 y hy'
      exact ⟨a, by simp; omega, hm⟩


open MvPolynomial in
theorem degreeOf_prod_linear_le (N n : ℕ) (lam : Fin n → ℝ) (c : ℝ) (a : Fin N) :
    (C c * ∏ b : Fin N, ∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ).degreeOf a ≤ n := by
  classical
  refine (degreeOf_mul_le _ _ _).trans ?_
  rw [degreeOf_C, zero_add]
  refine (degreeOf_prod_le _ _ _).trans ?_
  have h1 : ∀ b : Fin N, degreeOf a (∏ s : Fin n, (X b + C (lam s)) : MvPolynomial (Fin N) ℝ) ≤ if a = b then n else 0 := by
    intro b
    refine (degreeOf_prod_le _ _ _).trans ?_
    have h2 : ∀ s : Fin n, degreeOf a (X b + C (lam s) : MvPolynomial (Fin N) ℝ) ≤ if a = b then 1 else 0 := by
      intro s
      refine (degreeOf_add_le _ _ _).trans ?_
      rw [degreeOf_C, degreeOf_X]
      simp
    refine (Finset.sum_le_sum fun s _ => h2 s).trans ?_
    split_ifs <;> simp
  refine (Finset.sum_le_sum fun b _ => h1 b).trans ?_
  simp






end Formalism.FourierDecayAlt.P.LEx2
