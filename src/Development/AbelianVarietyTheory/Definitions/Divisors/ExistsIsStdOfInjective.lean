import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt

set_option autoImplicit false

noncomputable section

open DividedPowers TensorProduct

namespace GlobalTheory.PDA.Model

variable {B : Type} [CommRing B] {J : Ideal B}

theorem repr_mul_succ (Q : PDPoly B) (p : Q.P) (n : ℕ) : Q.e.repr (p * Q.e (n + 1)) 0 = 0 := by
  have : (Q.e.coord 0) ∘ₗ LinearMap.mulRight B (Q.e (n + 1)) = 0 := by
    refine Q.e.ext fun m ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, Q.e_mul, ← nsmul_eq_mul, map_nsmul,
      LinearMap.zero_apply, Module.Basis.coord_apply, Module.Basis.repr_self]
    rw [Finsupp.single_eq_of_ne (by omega), smul_zero]
  exact LinearMap.congr_fun this p

theorem mem_ext_iff (Q : PDPoly B) (p : Q.P) : p ∈ Q.ext J ↔ Q.e.repr p 0 ∈ J := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    have h1 : ∀ q, Q.e.repr (q * a) 0 ∈ J := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 ∈ J) ?_ ?_ ?_ ?_ ha
      · rintro _ ⟨j, hj, rfl⟩ q
        rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul]
        exact J.mul_mem_right _ hj
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add]; exact add_mem (hx q) (hy q)
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h2 : ∀ q, Q.e.repr (q * b) 0 = 0 := by
      refine Submodule.span_induction (p := fun a _ ↦ ∀ q, Q.e.repr (q * a) 0 = 0) ?_ ?_ ?_ ?_ hb
      · rintro _ ⟨j, rfl⟩ q; exact repr_mul_succ Q q j
      · simp
      · intro x y _ _ hx hy q; rw [mul_add, map_add, Finsupp.add_apply, hx, hy, add_zero]
      · intro r x _ hx q; rw [smul_eq_mul, ← mul_assoc]; exact hx _
    have h1' := h1 1
    have h2' := h2 1
    rw [one_mul] at h1' h2'
    rw [map_add, Finsupp.add_apply, h2', add_zero]; exact h1'
  · intro h
    rw [← Q.e.linearCombination_repr p, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Ideal.sum_mem _ fun n _ ↦ ?_
    rw [Algebra.smul_def]
    rcases n with _ | n
    · exact Ideal.mul_mem_right _ _ (Q.algebraMap_mem_ext h)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Q.e_succ_mem_aug n))






def gam (n : ℕ) (x : ZMod 4) : ZMod 4 :=
  if x = 0 ∨ x = 2 then (if n = 0 then 1 else if n = 1 ∨ n = 4 then x else 0) else 0


theorem gam_mul (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) (x y : ZMod 4) : gam m x * gam n y = 0 := by
  unfold gam
  simp only [hm, hn, if_false]
  by_cases h1 : m = 1 ∨ m = 4 <;> by_cases h2 : n = 1 ∨ n = 4 <;> simp only [h1, h2] <;> revert x y <;> decide


end GlobalTheory.PDA.Model
