import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsFlag
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.AltCoeff
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.IsFlagIntegralOne

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

namespace FlagEq

variable {f N : ℕ}

def permSign (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : ℤ :=
  ∏ τ, ((Equiv.Perm.sign (w τ) : ℤˣ) : ℤ)

def stairExp (f N : ℕ) (w : Fin f → Equiv.Perm (Fin N)) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - ((w v.1).symm v.2 : ℕ)

def rho (f N : ℕ) : Fin f × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun v => N - 1 - (v.2 : ℕ)

def stairConst (f N : ℕ) : ℝ := (∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ)) ^ f

theorem stairExp_one : stairExp f N 1 = rho f N := by
  ext v; simp [stairExp, rho, Equiv.Perm.one_def]

theorem permSign_one : permSign f N 1 = 1 := by simp [permSign]

theorem permSign_inv (w : Fin f → Equiv.Perm (Fin N)) : permSign f N w⁻¹ = permSign f N w := by
  simp [permSign, Equiv.Perm.sign_inv]

theorem permSign_mul (u w : Fin f → Equiv.Perm (Fin N)) :
    permSign f N (u * w) = permSign f N u * permSign f N w := by
  simp [permSign, Equiv.Perm.sign_mul, prod_mul_distrib]

theorem permSign_mul_self (u : Fin f → Equiv.Perm (Fin N)) :
    permSign f N u * permSign f N u = 1 := by
  rw [permSign, ← prod_mul_distrib]
  exact prod_eq_one fun τ _ => by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]

theorem stairConst_pos : 0 < stairConst f N :=
  pow_pos (prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos _) _

theorem coeff_rename_prodCongrRight {R : Type*} [CommSemiring R] (w : Fin f → Equiv.Perm (Fin N))
    (P : MvPolynomial (Fin f × Fin N) R) (d : Fin f × Fin N →₀ ℕ) :
    coeff d (rename (Equiv.prodCongrRight w) P) =
      coeff (Finsupp.equivFunOnFinite.symm fun v => d (Equiv.prodCongrRight w v)) P := by
  rw [← coeff_rename_mapDomain (Equiv.prodCongrRight w) (Equiv.injective _) P]
  congr 1
  ext v
  obtain ⟨u, rfl⟩ := (Equiv.prodCongrRight w).surjective v
  rw [Finsupp.mapDomain_apply (Equiv.injective _)]
  simp

theorem coeff_rho_antisym {R : Type*} [CommRing R] (P : MvPolynomial (Fin f × Fin N) R) :
    coeff (rho f N) (∑ w : Fin f → Equiv.Perm (Fin N),
        ((permSign f N w : ℤ) : R) • rename (Equiv.prodCongrRight w) P) =
      ∑ w, ((permSign f N w : ℤ) : R) * coeff (stairExp f N w) P := by
  rw [coeff_sum]
  refine Fintype.sum_equiv (Equiv.inv _) _ _ (fun w => ?_)
  rw [coeff_smul, smul_eq_mul, coeff_rename_prodCongrRight, Equiv.inv_apply, permSign_inv]
  congr 2

theorem blockVandermonde_eq_sum (f N : ℕ) :
    blockVandermonde f N = ∑ w : Fin f → Equiv.Perm (Fin N),
      ((permSign f N w : ℤ) : ℚ) • monomial (stairExp f N w) (1 : ℚ) := by
  simp only [blockVandermonde, Comb.vandermondeOf_eq_det, Matrix.det_apply', Matrix.of_apply]
  rw [prod_univ_sum, Fintype.piFinset_univ]
  refine sum_congr rfl fun w _ => ?_
  rw [prod_mul_distrib, smul_eq_C_mul, monomial_eq, C_1, one_mul,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_prod_type]
  congr 1
  · simp [permSign]
  · refine prod_congr rfl fun τ _ => ?_
    symm
    rw [← Equiv.prod_comp (w τ)]
    simp [stairExp]

theorem coeff_blockVandermonde (α : Fin f × Fin N →₀ ℕ) :
    coeff α (blockVandermonde f N) =
      ∑ w, ((permSign f N w : ℤ) : ℚ) * if stairExp f N w = α then 1 else 0 := by
  rw [blockVandermonde_eq_sum, coeff_sum]
  simp only [coeff_smul, coeff_monomial, smul_eq_mul]

theorem eq_one_of_stairExp_eq (w : Fin f → Equiv.Perm (Fin N)) (h : stairExp f N w = rho f N) :
    w = 1 := by
  funext τ
  ext i
  have h1 := DFunLike.congr_fun h (τ, w τ i)
  simp [stairExp, rho] at h1
  have := (w τ i).isLt
  have := i.isLt
  simp only [Pi.one_apply, Equiv.Perm.coe_one, id_eq]
  omega

theorem prod_factorial_stairExp (w : Fin f → Equiv.Perm (Fin N)) :
    (stairExp f N w).prod (fun _ e => (e.factorial : ℝ)) = stairConst f N := by
  rw [Finsupp.prod_fintype _ _ (fun _ => by simp), Fintype.prod_prod_type]
  have h : ∀ τ, ∏ i : Fin N, ((stairExp f N w (τ, i)).factorial : ℝ) =
      ∏ i : Fin N, ((N - 1 - (i : ℕ)).factorial : ℝ) := by
    intro τ
    simp only [stairExp, Finsupp.coe_equivFunOnFinite_symm]
    exact Equiv.prod_comp (w τ).symm (fun i : Fin N => ((N - 1 - (i : ℕ)).factorial : ℝ))
  rw [prod_congr rfl (fun τ _ => h τ), prod_const, card_univ, Fintype.card_fin, stairConst]

theorem rho_degree (f N : ℕ) : (rho f N).degree = f * (N * (N - 1) / 2) := by
  rw [Finsupp.degree_eq_sum, Fintype.sum_prod_type]
  simp only [rho, Finsupp.coe_equivFunOnFinite_symm, sum_const, card_univ, Fintype.card_fin,
    smul_eq_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => N - 1 - i) N]
  have h := sum_range_reflect (fun i => i) N
  rw [h, sum_range_id]

end FlagEq

end

end GroundTheory.Heights₂.Heights.RestTerms
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset

noncomputable section

def flagIntegralReal (f N : ℕ) : MvPolynomial (Fin f × Fin N) ℝ →ₗ[ℝ] ℝ where
  toFun G := ∑ α ∈ (blockVandermonde f N).support,
    coeff α G * ((coeff α (blockVandermonde f N) : ℚ) : ℝ) * α.prod (fun _ e => (e.factorial : ℝ))
  map_add' G H := by simp only [coeff_add, add_mul, sum_add_distrib]
  map_smul' c G := by simp only [coeff_smul, smul_eq_mul, RingHom.id_apply, mul_sum, mul_assoc]

theorem flagIntegralReal_map (f N : ℕ) (Φ : RootRing f N) :
    flagIntegralReal f N (map (algebraMap ℚ ℝ) Φ) = (flagIntegral f N Φ : ℝ) := by
  simp [flagIntegralReal, flagIntegral, coeff_map, Finsupp.prod]

namespace FlagEq

theorem flagIntegralReal_eq {f N : ℕ} (G : MvPolynomial (Fin f × Fin N) ℝ) :
    flagIntegralReal f N G =
      stairConst f N * ∑ w, ((permSign f N w : ℤ) : ℝ) * coeff (stairExp f N w) G := by
  classical
  have hsub : (blockVandermonde f N).support ⊆
      (blockVandermonde f N).support ∪ univ.image (stairExp f N) := subset_union_left
  show ∑ α ∈ _, _ = _
  rw [sum_subset hsub (fun α _ hα => by rw [notMem_support_iff.mp hα]; simp)]
  have hc : ∀ α : Fin f × Fin N →₀ ℕ, ((coeff α (blockVandermonde f N) : ℚ) : ℝ) =
      ∑ w, ((permSign f N w : ℤ) : ℝ) * if stairExp f N w = α then 1 else 0 := by
    intro α
    rw [coeff_blockVandermonde, Rat.cast_sum]
    refine sum_congr rfl fun w _ => ?_
    split_ifs <;> simp
  simp only [hc, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun w _ => ?_
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
  rw [sum_ite_eq, if_pos (mem_union_right _ (mem_image_of_mem _ (mem_univ w))),
    prod_factorial_stairExp]
  ring

theorem ddConst_apply (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      coeff (rho f (j + k)) (∑ w : Fin f → Equiv.Perm (Fin (j + k)),
        ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G) := by
  simp [IndefiniteRowSideFullHecke.RestTerms.ddConst, IndefiniteRowSideFullHecke.RestTerms.blockAntisym, permSign, rho,
    IndefiniteRowSideFullHecke.RestTerms.rhoMon, coeff_sum, coeff_smul, smul_eq_mul]

theorem ddConst_eq (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G =
      ∑ w, ((permSign f (j + k) w : ℤ) : ℝ) * coeff (stairExp f (j + k) w) G := by
  rw [ddConst_apply, coeff_rho_antisym]

theorem rename_psumAt (f j k m : ℕ) (τ : Fin f) (w : Fin f → Equiv.Perm (Fin (j + k))) :
    rename (Equiv.prodCongrRight w) (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ := by
  simp only [IndefiniteRowSideFullHecke.RestTerms.psumAt, map_sum, map_pow, rename_X, Equiv.prodCongrRight_apply]
  exact Equiv.sum_comp (w τ) (fun i => (X (τ, i) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) ^ m)

def antisym (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) : IndefiniteRowSideFullHecke.RestTerms.Roots f j k :=
  ∑ w : Fin f → Equiv.Perm (Fin (j + k)),
    ((permSign f (j + k) w : ℤ) : ℝ) • rename (Equiv.prodCongrRight w) G

theorem antisym_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    antisym f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) =
      IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * antisym f j k G := by
  simp only [antisym, map_mul, rename_psumAt, mul_sum, mul_smul_comm]

theorem rename_antisym (f j k : ℕ) (u : Fin f → Equiv.Perm (Fin (j + k)))
    (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    rename (Equiv.prodCongrRight u) (antisym f j k G) =
      ((permSign f (j + k) u : ℤ) : ℝ) • antisym f j k G := by
  have hcomp : ∀ w : Fin f → Equiv.Perm (Fin (j + k)),
      rename (Equiv.prodCongrRight u) (rename (Equiv.prodCongrRight w) G) =
        rename (Equiv.prodCongrRight (u * w)) G := by
    intro w
    rw [rename_rename]
    congr 1
  have hs : ((permSign f (j + k) u : ℤ) : ℝ) * ((permSign f (j + k) u : ℤ) : ℝ) = 1 := by
    exact_mod_cast permSign_mul_self u
  simp only [antisym, map_sum, map_smul, hcomp, smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.mulLeft u) _ _ (fun w => ?_)
  simp only [Equiv.coe_mulLeft, permSign_mul]
  push_cast
  rw [← mul_assoc, hs, one_mul]

theorem coeff_eq_zero_of_swap {f N : ℕ} (A : MvPolynomial (Fin f × Fin N) ℝ)
    (hA : ∀ u : Fin f → Equiv.Perm (Fin N),
      rename (Equiv.prodCongrRight u) A = ((permSign f N u : ℤ) : ℝ) • A)
    (β : Fin f × Fin N →₀ ℕ) (τ : Fin f) (i i' : Fin N) (hii : i ≠ i')
    (hβ : β (τ, i) = β (τ, i')) : coeff β A = 0 := by
  classical
  let u : Fin f → Equiv.Perm (Fin N) := Pi.mulSingle τ (Equiv.swap i i')
  have hu1 : u τ = Equiv.swap i i' := Pi.mulSingle_eq_same _ _
  have hu2 : ∀ τ', τ' ≠ τ → u τ' = 1 := fun τ' h => Pi.mulSingle_eq_of_ne h _
  have hs : permSign f N u = -1 := by
    rw [permSign, Fintype.prod_eq_single τ]
    · rw [hu1, Equiv.Perm.sign_swap hii]; rfl
    · intro τ' h; rw [hu2 τ' h]; simp
  have hfix : (Finsupp.equivFunOnFinite.symm fun v => β (Equiv.prodCongrRight u v)) = β := by
    ext ⟨τ', l⟩
    simp only [Finsupp.coe_equivFunOnFinite_symm, Equiv.prodCongrRight_apply]
    by_cases h : τ' = τ
    · subst h
      rw [hu1]
      rcases eq_or_ne l i with rfl | h1
      · rw [Equiv.swap_apply_left, hβ]
      · rcases eq_or_ne l i' with rfl | h2
        · rw [Equiv.swap_apply_right, hβ]
        · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
    · rw [hu2 τ' h]; rfl
  have h := congrArg (coeff β) (hA u)
  rw [coeff_rename_prodCongrRight, hfix, hs, coeff_smul, smul_eq_mul] at h
  push_cast at h
  linarith

theorem ddConst_psumAt_mul (f j k m : ℕ) (τ : Fin f) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k)
    (hm : 1 ≤ m) : IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (IndefiniteRowSideFullHecke.RestTerms.psumAt f j k m τ * G) = 0 := by
  classical
  rw [ddConst_apply, ← antisym, antisym_psumAt_mul, IndefiniteRowSideFullHecke.RestTerms.psumAt, sum_mul, coeff_sum]
  refine sum_eq_zero fun i _ => ?_
  rw [X_pow_eq_monomial, coeff_monomial_mul']
  split_ifs with h
  · rw [Finsupp.single_le_iff] at h
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm] at h
    have hi : (i : ℕ) + m < j + k := by have := i.isLt; omega
    have hii : i ≠ ⟨(i : ℕ) + m, hi⟩ := by
      intro h'; have := congrArg Fin.val h'; simp at this; omega
    rw [coeff_eq_zero_of_swap _ (fun u => rename_antisym f j k u G) _ τ i ⟨(i : ℕ) + m, hi⟩ hii, mul_zero]
    rw [Finsupp.tsub_apply, Finsupp.tsub_apply, Finsupp.single_eq_same,
      Finsupp.single_eq_of_ne (by intro h'; simp at h'; exact hii h'.symm)]
    simp only [rho, Finsupp.coe_equivFunOnFinite_symm]
    omega
  · rfl

theorem ddConst_monomial_rho (f j k : ℕ) :
    IndefiniteRowSideFullHecke.RestTerms.ddConst f j k (monomial (rho f (j + k)) (1 : ℝ)) = 1 := by
  rw [ddConst_eq, Fintype.sum_eq_single 1]
  · simp [stairExp_one, permSign_one]
  · intro w hw
    rw [coeff_monomial, if_neg (fun h => hw (eq_one_of_stairExp_eq w h.symm)), mul_zero]

end FlagEq

open FlagEq in

theorem flagIntegralReal_eq_mul_ddConst (f j k : ℕ) (G : IndefiniteRowSideFullHecke.RestTerms.Roots f j k) :
    flagIntegralReal f (j + k) G = stairConst f (j + k) * IndefiniteRowSideFullHecke.RestTerms.ddConst f j k G := by
  rw [flagIntegralReal_eq, ddConst_eq]

end

end GroundTheory.Heights₂.Heights.RestTerms
end
