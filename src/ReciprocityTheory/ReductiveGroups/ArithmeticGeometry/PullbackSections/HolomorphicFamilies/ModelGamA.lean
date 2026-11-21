import Mathlib

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.MG

open Matrix

variable {r : ℕ}

def Eij (i j : Fin r) (s : ℂ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => if a = i ∧ b = j then s else 0

theorem mul_Eij (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (H * Eij i j s) a b = if b = j then H a i * s else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases hb : b = j
  · subst hb
    simp [mul_ite]
  · simp [hb]

theorem Eij_mul (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (s : ℂ) (a b : Fin r) :
    (Eij i j s * H) a b = if a = i then s * H j b else 0 := by
  simp only [Eij, Matrix.mul_apply, Matrix.of_apply]
  by_cases ha : a = i
  · subst ha
    simp [ite_mul]
  · simp [ha]

theorem Eij_sq (i j : Fin r) (hij : i ≠ j) (s : ℂ) : Eij i j s * Eij i j s = 0 := by
  ext a b
  rw [Eij_mul]
  simp [Eij, Ne.symm hij]

theorem unip_mul (i j : Fin r) (hij : i ≠ j) (s : ℂ) : (1 - Eij i j s) * (1 + Eij i j s) = 1 := by
  rw [sub_mul, one_mul, mul_add, mul_one, Eij_sq i j hij, add_zero, add_sub_cancel_right]

theorem det_unip (i j : Fin r) (hji : j < i) (s : ℂ) : (1 + Eij i j s).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun a _ => ?_
    simp only [Matrix.add_apply, Matrix.one_apply_eq, Eij, Matrix.of_apply]
    rw [if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_irrefl _ hji
  · intro a b hab
    have hab' : a < b := OrderDual.toDual_lt_toDual.mp hab
    simp only [Matrix.add_apply, Eij, Matrix.of_apply]
    rw [Matrix.one_apply_ne (ne_of_lt hab'), if_neg, add_zero]
    rintro ⟨rfl, rfl⟩
    exact lt_asymm hji hab'


theorem conj_entry (H : Matrix (Fin r) (Fin r) ℂ) (i j : Fin r) (hij : i ≠ j) (s : ℂ) :
    ((1 - Eij i j s) * H * (1 + Eij i j s)) i j = H i j + s * (H i i - H j j) - s ^ 2 * H j i := by
  have h : (1 - Eij i j s) * H * (1 + Eij i j s) =
      H + H * Eij i j s - Eij i j s * H - Eij i j s * (H * Eij i j s) := by
    noncomm_ring
  rw [h]
  simp only [Matrix.add_apply, Matrix.sub_apply, mul_Eij, Eij_mul, if_true, ite_true, eq_self_iff_true]
  ring



end ReciprocityTheory.ChartRestriction.G.PullbackSections.MG
