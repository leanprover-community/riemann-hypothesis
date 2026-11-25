module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace Bl.general_b_fact_left

theorem goal1 {k : Type} [Field k] [Fintype k] (t m e : k) (hd : t ^ 2 - 4 * m ≠ 0) :
    ∃ x y : k, x ^ 2 + t * x * y + m * y ^ 2 = e := by
  by_cases hc : ringChar k = 2
  · have h2 : (2 : k) = 0 := by simpa [hc] using ringChar.Nat.cast_ringChar (R := k)
    have h4 : (4 : k) = 0 := by rw [show (4 : k) = 2 * 2 by norm_num, h2, zero_mul]
    rw [h4, zero_mul, sub_zero] at hd
    have ht : t ≠ 0 := fun h => hd (by rw [h]; ring)
    by_cases hm : m = 0
    · exact ⟨1, (e - 1) / t, by rw [hm]; field_simp; ring⟩
    · obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two hc (e / m)
      exact ⟨0, r, by rw [show r ^ 2 = e / m by rw [hr]; ring]; field_simp; ring⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hc
    have h4 : (4 : k) ≠ 0 := by rw [show (4 : k) = 2 * 2 by norm_num]; exact mul_ne_zero h2 h2
    set D : k := m - t ^ 2 / 4 with hD
    have hD0 : D ≠ 0 := fun h0 => hd <| by
      rw [show t ^ 2 - 4 * m = -4 * D by rw [hD]; field_simp; ring, h0, mul_zero]
    have hf : Polynomial.degree (Polynomial.X ^ 2 - Polynomial.C e : Polynomial k) = 2 := by
      rw [Polynomial.degree_sub_C, Polynomial.degree_X_pow] <;> norm_num
    have hg : Polynomial.degree (Polynomial.C D * Polynomial.X ^ 2 : Polynomial k) = 2 := by
      rw [Polynomial.degree_C_mul_X_pow 2 hD0]; rfl
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic hf hg (FiniteField.odd_card_of_char_ne_two hc)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul] at hab
    refine ⟨a - t * b / 2, b, ?_⟩
    have key : a ^ 2 + D * b ^ 2 = e := by linear_combination hab
    rw [← key, hD]; field_simp; ring

end Bl.general_b_fact_left
