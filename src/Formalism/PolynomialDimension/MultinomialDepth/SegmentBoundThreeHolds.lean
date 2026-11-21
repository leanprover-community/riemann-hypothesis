import Formalism.PolynomialDimension.DigitSumValuationBound

noncomputable section

open scoped BigOperators
open Finset

namespace Formalism.CountingSumsFrames







lemma sum_update_swap {s : ℕ} (As : Fin s → Finset ℕ) (i : Fin s) (g : (Fin s → ℕ) → ℝ) :
    ∑ aa ∈ Fintype.piFinset As, ∑ x ∈ As i, g (Function.update aa i x) =
      ((As i).card : ℝ) * ∑ aa ∈ Fintype.piFinset As, g aa := by
  have key : ∑ p ∈ Fintype.piFinset As ×ˢ As i, g (Function.update p.1 i p.2) =
      ∑ p ∈ Fintype.piFinset As ×ˢ As i, g p.1 := by
    apply Finset.sum_nbij' (fun p => (Function.update p.1 i p.2, p.1 i))
      (fun p => (Function.update p.1 i p.2, p.1 i))
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ h
      simp only [Finset.mem_product, Fintype.mem_piFinset] at h ⊢
      refine ⟨fun j => ?_, h.1 i⟩
      rcases eq_or_ne j i with rfl | hj
      · simp [h.2]
      · simp [Function.update_of_ne hj, h.1 j]
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      simp
    · rintro ⟨aa, x⟩ _
      rfl
  rw [← Finset.sum_product', key, Finset.sum_product]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [Finset.mul_sum]









theorem det_leading_diagonal : DetLeadDiag := by
  intro K _ n J A d hdeg hcoeff
  have hprod : ∀ σ : Equiv.Perm (Fin n), (∏ i, A (σ i) i).coeff (n * J) = ∏ i, (A (σ i) i).coeff J := by
    intro σ
    have h1 := Polynomial.coeff_prod_of_natDegree_le (s := Finset.univ) (fun i => A (σ i) i) J
      (fun i _ => hdeg (σ i) i)
    rw [Finset.card_univ, Fintype.card_fin] at h1
    exact h1
  rw [Matrix.det_apply']
  constructor
  · apply Polynomial.natDegree_sum_le_of_forall_le
    intro σ _
    refine (Polynomial.natDegree_mul_le).trans ?_
    rw [Polynomial.natDegree_intCast, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc ∑ i, (A (σ i) i).natDegree ≤ ∑ _i : Fin n, J := Finset.sum_le_sum fun i _ => hdeg (σ i) i
      _ = n * J := by simp
  · rw [Polynomial.finset_sum_coeff, Finset.sum_eq_single 1]
    · rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul, Equiv.Perm.one_apply]
      exact Finset.prod_congr rfl fun i _ => by rw [hcoeff]; simp
    · intro σ _ hσ
      rw [← Polynomial.C_eq_intCast, Polynomial.coeff_C_mul, hprod]
      obtain ⟨i, hi⟩ := not_forall.mp (mt Equiv.ext hσ)
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hcoeff, if_neg (by simpa using hi)]), mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h



end Formalism.CountingSumsFrames
