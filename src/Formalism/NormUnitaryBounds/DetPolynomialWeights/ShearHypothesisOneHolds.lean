import Formalism.NormUnitaryBounds.Statement

section
open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma blockSum {N n : ℕ} {ν : Fin N → ℕ} (d : Fin N × Fin n →₀ ℕ)
    (hd : Finsupp.weight (blockWt N n) d = ν) (j : Fin N) : ∑ k, d (j, k) = ν j := by
  have h := congrFun hd j
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Finset.sum_apply, Pi.smul_apply, blockWt, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fintype.sum_prod_type] at h
  simpa [Finset.sum_ite_eq, Finset.sum_comm] using h

lemma aeval_scale {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    (F : MvPolynomial (Fin N × Fin n) R)
    (hF : IsWeightedHomogeneous (blockWt N n) F ν) (lam : Fin N → S) (y : Fin N × Fin n → S) :
    aeval (fun p => lam p.1 * y p) F = (∏ j, lam j ^ ν j) * aeval y F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWt N n) d = ν := hF (mem_support_iff.mp hd)
  have hprod : (d.prod fun p k => lam p.1 ^ k) = ∏ j, lam j ^ ν j := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    show ∏ k, lam j ^ d (j, k) = _
    rw [Finset.prod_pow_eq_pow_sum, blockSum d hw j]
  have : (d.prod fun p k => (lam p.1 * y p) ^ k) =
      (d.prod fun p k => lam p.1 ^ k) * d.prod fun p k => y p ^ k := by
    rw [← Finsupp.prod_mul]
    simp [mul_pow]
  rw [this, hprod]
  ring

lemma shear_eval {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} (i j : Fin N)
    (y : Fin N × Fin n → S) (s : S) (G : MvPolynomial (Fin N × Fin n) R) :
    Polynomial.eval₂ (aeval y).toRingHom s (shear R i j G) =
      aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    simp [shear, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p q hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    simp only [shear, aeval_X]
    split_ifs <;> simp <;> ring

lemma shear_eq {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν)
    (i j : Fin N) (hij : i < j) : shear R i j F = Polynomial.C F := by
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 i) j) hij
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
  exact h

lemma shear_inv {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν) (i j : Fin N) (hij : i < j)
    (y : Fin N × Fin n → S) (s : S) :
    aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) F = aeval y F := by
  rw [← shear_eval, shear_eq hF i j hij, Polynomial.eval₂_C]
  rfl

lemma shear_multi {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (y : Fin (N + 1) × Fin n → S) (s : Fin (N + 1) → S) (T : Finset (Fin (N + 1)))
    (hT : (0 : Fin (N + 1)) ∉ T) :
    aeval (fun p => y p + if p.1 ∈ T then s p.1 * y (0, p.2) else 0) F = aeval y F := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have ha0 : a ≠ 0 := fun h => hT (h ▸ Finset.mem_insert_self _ _)
    have h0T : (0 : Fin (N + 1)) ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have key : (fun p : Fin (N + 1) × Fin n =>
        y p + if p.1 ∈ insert a T then s p.1 * y (0, p.2) else 0) =
        fun p => (fun q : Fin (N + 1) × Fin n => y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) p
          + if p.1 = a then s a * (fun q : Fin (N + 1) × Fin n =>
              y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) (0, p.2) else 0 := by
      funext p
      by_cases hpa : p.1 = a
      · have : p.1 ∉ T := hpa ▸ haT
        simp [hpa, h0T, haT]
      · simp [hpa, Finset.mem_insert]
    rw [key, shear_inv hF 0 a (Fin.pos_iff_ne_zero.mpr ha0), ih h0T]

lemma natDegree_aeval_le {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    (F : MvPolynomial (Fin (N + 1) × Fin n) R) (hF : IsWeightedHomogeneous (blockWt (N + 1) n) F ν)
    (y : Fin (N + 1) × Fin n → Polynomial B)
    (hy : ∀ p, (y p).natDegree ≤ if p.1 = 0 then 1 else 0) : (aeval y F).natDegree ≤ ν 0 := by
  rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  have hw : Finsupp.weight (blockWt (N + 1) n) d = ν := hF (mem_support_iff.mp hd)
  rw [aeval_monomial, Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (by simp)]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ p, (y p ^ d p).natDegree ≤ ∑ p : Fin (N + 1) × Fin n, d p * (if p.1 = 0 then 1 else 0) :=
        Finset.sum_le_sum fun p _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hy p))
    _ = ν 0 := by
        rw [← blockSum d hw 0, Fintype.sum_prod_type]
        simp

end Formalism.NormUnitaryCountingLemmas.H1OnPoints
end
end

section
open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma core {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (x : Fin (N + 1) → Fin n → B) (u : Fin n → B) (c : Fin (N + 1) → B)
    (hc : IsLeftRegular (c 0)) :
    (aeval (fun p : Fin (N + 1) × Fin n =>
      Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2)) F).natDegree
        ≤ ν 0 := by
  have hW : IsWeightedHomogeneous (blockWt (N + 1) n) F ν :=
    (mem_weightedHomogeneousSubmodule _ _ _ _).mp (Submodule.mem_inf.mp hF).1
  set φ : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    Polynomial.C (x p.1 p.2) + Polynomial.X * Polynomial.C (c p.1 * u p.2) with hφ
  let y : Fin (N + 1) × Fin n → Polynomial B := fun p =>
    if p.1 = 0 then Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2)
    else Polynomial.C (c 0 * x p.1 p.2 - c p.1 * x 0 p.2)
  let lam : Fin (N + 1) → Polynomial B := fun j => if j = 0 then 1 else Polynomial.C (c 0)
  let ℓ : B := ∏ j, (if j = 0 then 1 else c 0) ^ ν j
  have hsc := aeval_scale F hW lam φ
  have hfun : (fun p : Fin (N + 1) × Fin n => lam p.1 * φ p) = fun p =>
      y p + if p.1 ∈ Finset.univ.erase 0 then Polynomial.C (c p.1) * y (0, p.2) else 0 := by
    funext p
    obtain ⟨j, k⟩ := p
    by_cases hj : j = 0
    · subst hj
      simp [lam, y, φ]
    · simp only [lam, y, φ, hj, if_false, Finset.mem_erase, ne_eq, not_false_eq_true,
        Finset.mem_univ, and_true, if_true, map_sub, map_mul]
      ring
  have hsh := shear_multi hF y (fun j => Polynomial.C (c j)) (Finset.univ.erase 0) (by simp)
  rw [hfun, hsh] at hsc
  have hdeg := natDegree_aeval_le F hW y (by
    intro p
    by_cases h : p.1 = 0
    · simp only [y, h, if_true]
      have : Polynomial.C (x 0 p.2) + Polynomial.X * Polynomial.C (c 0 * u p.2) =
          Polynomial.C (c 0 * u p.2) * Polynomial.X + Polynomial.C (x 0 p.2) := by ring
      rw [this]
      exact Polynomial.natDegree_linear_le
    · simp only [y, h, if_false]
      exact (Polynomial.natDegree_C _).le)
  have hprodC : (∏ j, lam j ^ ν j) = Polynomial.C ℓ := by
    simp only [lam, ℓ, map_prod, map_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hℓ : IsLeftRegular ℓ := by
    refine Finset.prod_induction _ (fun b : B => IsLeftRegular b) (fun a b ha hb => ha.mul hb)
      (isRegular_one : IsRegular (1 : B)).left fun j _ => IsLeftRegular.pow _ ?_
    split_ifs
    · exact (isRegular_one : IsRegular (1 : B)).left
    · exact hc
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero] at hdeg ⊢
  intro e he
  have h0 := hdeg e he
  rw [hsc, hprodC, Polynomial.coeff_C_mul] at h0
  exact hℓ (h0.trans (mul_zero ℓ).symm)

end Formalism.NormUnitaryCountingLemmas.H1OnPoints

namespace Formalism.NormUnitaryCountingLemmas

open Formalism.NormUnitaryCountingLemmas.H1OnPoints in
theorem shear_hypothesis_one_holds : H1 := by
  intro R _ N n ν F hF A _ _ x u c
  let g : Polynomial A →ₐ[R] A := (Polynomial.aeval (0 : A)).restrictScalars R
  have hreg : IsLeftRegular (Polynomial.C (c 0) + Polynomial.X : Polynomial A) := by
    rw [add_comm]
    exact (Polynomial.monic_X_add_C _).isRegular.left
  have hc := core (B := Polynomial A) hF (fun j k => Polynomial.C (x j k))
    (fun k => Polynomial.C (u k)) (fun j => Polynomial.C (c j) + if j = 0 then Polynomial.X else 0)
    (by simpa using hreg)
  refine le_trans (le_of_eq ?_) ((Polynomial.natDegree_map_le (f := (g : Polynomial A →+* A))).trans hc)
  congr 1
  rw [← Polynomial.coe_mapAlgHom, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  congr 1
  congr 1
  funext p
  by_cases h : p.1 = 0 <;> simp [g, h]

end Formalism.NormUnitaryCountingLemmas
end
end
