import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan

noncomputable section

open NumberField IsDedekindDomain MeasureTheory

namespace GlobalTheory.JSW.SpanModel

open GlobalTheory.CuspRep GlobalTheory.JSW

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem colU_zero (r : ℕ) : colU (E := E) (a := a) r 0 = 1 := by
  ext i j
  simp [colU]

theorem colU_add (r : ℕ) (x y : Fin a → Cinf E) : colU r (x + y) = colU r x * colU r y := by
  apply Units.ext
  change (1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then (x + y) i else 0)) =
    ((1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0)) *
      (1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then y i else 0)))
  have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
      Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then y i else 0) = 0 := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : (k : ℕ) = r
    · simp [hk]
    · simp [hk]
  rw [mul_add, add_mul, add_mul, one_mul, mul_one, one_mul, h, add_zero, add_assoc]
  congr 1
  refine Matrix.ext fun i j => ?_
  simp only [Matrix.add_apply, Matrix.of_apply, Pi.add_apply]
  split_ifs <;> simp




def leftInv (E : Type) [Field E] [NumberField E] (a : ℕ) : Submodule ℂ (GA E a → ℂ) where
  carrier := {F | ∀ γ g, F (ratGL E a γ * g) = F g}
  add_mem' hF hG γ g := by simp [hF γ g, hG γ g]
  zero_mem' _ _ := rfl
  smul_mem' c F hF γ g := by simp [hF γ g]




end GlobalTheory.JSW.SpanModel
