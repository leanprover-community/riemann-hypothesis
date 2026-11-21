import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivationDetEqDoubleSumAdjugateEntry
import BuildAid.ForwardExisting

section
section
namespace GlobalTheory.PiolaAlg

open Finset Matrix

variable {K R : Type} [CommRing K] [CommRing R] [Algebra K R]

theorem derivation_prod {ι : Type} [DecidableEq ι] (D : Derivation K R R) (f : ι → R) (s : Finset ι) :
    D (∏ i ∈ s, f i) = ∑ k ∈ s, ∏ i ∈ s, Function.update f k (D (f k)) i := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, Derivation.leibniz, ih, sum_insert ha, prod_insert ha, Function.update_self,
      prod_congr rfl (fun i hi => Function.update_of_ne (ne_of_mem_of_not_mem hi ha) _ _)]
    simp only [smul_eq_mul, mul_sum]
    rw [add_comm, mul_comm (∏ i ∈ s, f i)]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [prod_insert ha, Function.update_of_ne (ne_of_mem_of_not_mem hk ha).symm]

theorem derivation_det {ι : Type} [Fintype ι] [DecidableEq ι] (D : Derivation K R R)
    (A : Matrix ι ι R) :
    D A.det = ∑ k, (A.updateRow k fun l => D (A k l)).det := by
  simp only [det_apply, map_sum]
  rw [sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
  · simp only [h, one_smul, Units.neg_smul, map_neg, sum_neg_distrib, neg_inj]
    rw [derivation_prod]
    conv_rhs => rw [← Equiv.sum_comp σ]
    refine sum_congr rfl fun k _ => prod_congr rfl fun i _ => ?_
    by_cases hik : i = k
    · subst hik; simp [updateRow_apply]
    · rw [Function.update_of_ne hik, updateRow_apply, if_neg (σ.injective.ne hik)]

theorem piola {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R)
    (M : Matrix ι ι R) (hM : ∀ h i j, δ h (M i j) = δ i (M h j)) (j : ι) :
    ∑ i, δ i (M.adjugate j i) = 0 := by
  set f : ι × ι → R := fun p =>
    ((M.updateRow p.1 (Pi.single j 1)).updateRow p.2
      fun l => δ p.1 ((M.updateRow p.1 (Pi.single j 1)) p.2 l)).det with hf
  have hS : ∑ i, δ i (M.adjugate j i) = ∑ p ∈ univ ×ˢ univ, f p := by
    rw [sum_product]
    refine sum_congr rfl fun i _ => ?_
    rw [adjugate_apply, derivation_det]
  have hdiag : ∀ i, f (i, i) = 0 := by
    intro i
    refine det_eq_zero_of_row_eq_zero i fun l => ?_
    simp only [updateRow_self]
    by_cases hl : l = j
    · subst hl; simp
    · simp [Pi.single_apply, hl]
  have hpair : ∀ i k, i ≠ k → f (i, k) + f (k, i) = 0 := by
    intro i k hik
    set D : ι → R := fun l => δ i (M k l) with hD
    have h1 : f (i, k) = ((M.updateRow i (Pi.single j 1)).updateRow k D).det := by
      simp only [hf]
      congr 2
      funext l
      rw [updateRow_ne (Ne.symm hik)]
    have h2 : f (k, i) = (((M.updateRow i (Pi.single j 1)).updateRow k D).submatrix
        (Equiv.swap i k) id).det := by
      simp only [hf]
      congr 1
      ext a b
      simp only [submatrix_apply, id, updateRow_apply, updateRow_ne hik, hD]
      by_cases hai : a = i
      · subst hai; simp [Equiv.swap_apply_left, hik, Ne.symm hik, hM]
      · by_cases hak : a = k
        · subst hak; simp [Equiv.swap_apply_right, hik, Ne.symm hik]
        · rw [Equiv.swap_apply_of_ne_of_ne hai hak]; simp [hai, hak]
    rw [h1, h2, det_permute, Equiv.Perm.sign_swap hik]
    simp
  rw [hS]
  refine sum_involution (fun p _ => p.swap) ?_ ?_ ?_ ?_
  · rintro ⟨i, k⟩ _
    by_cases hik : i = k
    · subst hik; simp [hdiag]
    · exact hpair i k hik
  · rintro ⟨i, k⟩ _ hne heq
    simp only [Prod.swap_prod_mk, Prod.mk.injEq] at heq
    rw [heq.1] at hne
    exact hne (hdiag i)
  · intro p _; simp
  · intro p _; simp

theorem piola_identity : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι]
    [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R),
    (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 :=
  fun δ M hM j => piola δ M hM j

end GlobalTheory.PiolaAlg
end

open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.piola_identity_adjugate_divergence_free : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (M : Matrix ι ι R), (∀ h i j, δ h (M i j) = δ i (M h j)) → ∀ j, ∑ i, δ i (M.adjugate j i) = 0 := by
  atlas_forward_decl GlobalTheory.PiolaAlg.piola_identity
end

section
open MvPolynomial

namespace GlobalTheory

theorem weighted_det_divergence_mem_ideal : ∀ {K R : Type} [CommRing K] [CommRing R] [Algebra K R] {ι : Type} [Fintype ι] [DecidableEq ι] (δ : ι → Derivation K R R) (δ0 : Derivation K R R) (I : Ideal R) (M : Matrix ι ι R) (a b : ι → R) (w t ρ : R), (∀ i j, δ0 (M i j) = δ i (a j)) → (∀ h i j, δ h (M i j) = δ i (M h j)) → δ0 w = 0 → (∀ i, δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j ∈ I) → ρ = ∑ j, b j * a j → δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * ∑ j, M.adjugate j i * a j) + t * δ i ρ * (w * ∑ j, M.adjugate j i * a j)) ∈ I := by
  intro K R _ _ _ ι _ _ δ δ0 I M a b w t ρ h0 hM hw hI hρ
  set c : ι → R := fun i => ∑ j, M.adjugate j i * a j with hc
  have hdet : δ0 M.det = ∑ i, δ i (c i) := by
    rw [GlobalTheory.T.derivation_det_eq_double_sum_adjugate_entry δ0 M]
    have hp := GlobalTheory.T.piola_identity_adjugate_divergence_free δ M hM
    have h1 : ∀ i, δ i (c i) = ∑ j, M.adjugate j i * δ0 (M i j) + ∑ j, a j * δ i (M.adjugate j i) := by
      intro i
      simp only [hc, map_sum, Derivation.leibniz, smul_eq_mul, h0, Finset.sum_add_distrib]
    have h2 : ∑ i, ∑ j, a j * δ i (M.adjugate j i) = 0 := by
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [← Finset.mul_sum, hp j, mul_zero]
    simp only [h1, Finset.sum_add_distrib, h2, add_zero]
  have hadj : ∀ k, ∑ i, c i * M i k = M.det * a k := by
    intro k
    have h3 : ∀ j, ∑ i, M.adjugate j i * M i k = if j = k then M.det else 0 := by
      intro j
      have := congrFun (congrFun (Matrix.adjugate_mul M) j) k
      rw [Matrix.mul_apply] at this
      rw [this, Matrix.smul_apply, Matrix.one_apply]
      split_ifs <;> simp
    calc ∑ i, c i * M i k = ∑ j, a j * ∑ i, M.adjugate j i * M i k := by
          simp only [hc, Finset.sum_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = M.det * a k := by
          simp only [h3, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  have hrho : ∑ i, c i * (w * ∑ j, M i j * b j) = ρ * (w * M.det) := by
    calc ∑ i, c i * (w * ∑ j, M i j * b j) = ∑ j, w * b j * ∑ i, c i * M i j := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
      _ = ρ * (w * M.det) := by
          rw [hρ, Finset.sum_mul]
          refine Finset.sum_congr rfl fun j _ => by rw [hadj]; ring
  have key : δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i))
      = - ∑ i, c i * (δ i w + t * δ i ρ * w - w * ∑ j, M i j * b j) := by
    rw [Derivation.leibniz, hw, smul_zero, add_zero, smul_eq_mul, hdet, ← hrho, Finset.mul_sum,
      ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  change δ0 (w * M.det) + ρ * (w * M.det) - ∑ i, (δ i (w * c i) + t * δ i ρ * (w * c i)) ∈ I
  rw [key]
  exact I.neg_mem (I.sum_mem fun i _ => I.mul_mem_left _ (hI i))

end GlobalTheory
end

section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory

theorem psco_t_core : GlobalTheory.PsCo.Cw2a.CoreCondition := by
  intro A _ _ I _ _ D dm J Z u η E μ r h1 h2 h3 h4 h5
  exact GlobalTheory.weighted_det_divergence_mem_ideal (K := ℂ) D dm J Z u η E μ r h1 h2 h3 h4 h5

end GlobalTheory
end
