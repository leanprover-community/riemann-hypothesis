import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsFlagIntMuOne
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.PermFinTwoUniv

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open Matrix Finset

def invFactMat (j m : ℕ) : Matrix (Fin m) (Fin m) ℚ :=
  Matrix.of fun r k => if (k : ℕ) ≤ j + r then (((j + r - k : ℕ).factorial : ℚ))⁻¹ else 0

theorem det_vandermonde_shift (j m : ℕ) :
    (vandermonde fun r : Fin m => ((j + r : ℕ) : ℚ)).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) := by
  have h : (fun r : Fin m => ((j + r : ℕ) : ℚ)) = fun r : Fin m => ((r : ℕ) : ℚ) + j := by
    ext r; push_cast; ring
  rw [h, det_vandermonde_add]
  cases m with
  | zero => simp
  | succ n =>
    rw [det_vandermonde_id_eq_superFactorial, ← Nat.prod_range_factorial_succ,
      Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ)) (n + 1), prod_range_succ']
    push_cast
    simp

theorem det_invFactMat (j m : ℕ) :
    (invFactMat j m).det = ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have hB : (Matrix.of fun r k : Fin m => ((j + r : ℕ).factorial : ℚ) * invFactMat j m r k) =
      Matrix.of fun r k : Fin m => (descPochhammer ℚ k).eval (((j + r : ℕ) : ℚ)) := by
    ext r k
    simp only [invFactMat, Matrix.of_apply, descPochhammer_eval_eq_descFactorial]
    split_ifs with h
    · rw [← Nat.factorial_mul_descFactorial h]
      push_cast
      have : ((j + r - k : ℕ).factorial : ℚ) ≠ 0 := by positivity
      field_simp
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)]
      simp
  have hV := Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
    (fun r : Fin m => ((j + r : ℕ) : ℚ)) (fun k => descPochhammer ℚ (k : ℕ))
    (fun k => descPochhammer_natDegree ℚ k) (fun k => monic_descPochhammer ℚ k)
  rw [← hB, det_mul_column, det_vandermonde_shift] at hV
  have hP : (∏ i : Fin m, ((j + i : ℕ).factorial : ℚ)) ≠ 0 :=
    prod_ne_zero_iff.mpr fun i _ => by positivity
  rw [prod_div_distrib, eq_div_iff hP, hV, mul_comm]

theorem prod_factorial_div_comm (j m : ℕ) :
    ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) =
      ∏ i : Fin j, ((i : ℕ).factorial : ℚ) / ((m + i : ℕ).factorial : ℚ) := by
  rw [Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((j + i : ℕ).factorial : ℚ)) m,
    Fin.prod_univ_eq_prod_range (fun i => ((i.factorial : ℕ) : ℚ) / ((m + i : ℕ).factorial : ℚ)) j,
    prod_div_distrib, prod_div_distrib,
    div_eq_div_iff (prod_ne_zero_iff.mpr fun i _ => by positivity)
      (prod_ne_zero_iff.mpr fun i _ => by positivity)]
  have h1 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) m j
  have h2 := prod_range_add (fun i => ((i.factorial : ℕ) : ℚ)) j m
  rw [Nat.add_comm m j] at h1
  rw [← h1.symm.trans h2]

def flagMat (j m : ℕ) : Matrix (Fin (j + m)) (Fin (j + m)) ℚ :=
  Matrix.of fun i k =>
    if (i : ℕ) < j then (if (k : ℕ) = m + i then 1 else 0)
    else (if (k : ℕ) ≤ i then (((i - k : ℕ).factorial : ℚ))⁻¹ else 0)

def blockSwap (j m : ℕ) : Equiv.Perm (Fin (j + m)) := finAddFlip.trans (finCongr (Nat.add_comm m j))

theorem blockSwap_castAdd (j m : ℕ) (i : Fin j) : ((blockSwap j m (Fin.castAdd m i) : Fin (j + m)) : ℕ) = m + i := by
  simp [blockSwap]
  omega

theorem blockSwap_natAdd (j m : ℕ) (r : Fin m) : ((blockSwap j m (Fin.natAdd j r) : Fin (j + m)) : ℕ) = r := by
  simp [blockSwap]

theorem finRotate_pow_val (n k : ℕ) (x : Fin n) : (((finRotate n) ^ k) x : ℕ) = ((x : ℕ) + k) % n := by
  cases n with
  | zero => exact x.elim0
  | succ n =>
    induction k with
    | zero => simp [Nat.mod_eq_of_lt x.isLt]
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, finRotate_apply, Fin.val_add, ih, Fin.val_one',
        ← Nat.add_mod, Nat.add_assoc]

theorem blockSwap_eq_pow (j m : ℕ) : blockSwap j m = (finRotate (j + m)) ^ m := by
  ext x
  rw [finRotate_pow_val]
  induction x using Fin.addCases with
  | left i =>
    rw [blockSwap_castAdd, Fin.val_castAdd, Nat.mod_eq_of_lt (by omega), Nat.add_comm]
  | right r =>
    rw [blockSwap_natAdd, Fin.val_natAdd, show j + (r : ℕ) + m = r + (j + m) by ring, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

theorem sign_blockSwap (j m : ℕ) : Equiv.Perm.sign (blockSwap j m) = (-1) ^ (j * m) := by
  rw [blockSwap_eq_pow, map_pow, sign_finRotate, ← pow_mul]
  have h : (j + m - 1) * m = j * m + (m * (m - 1)) := by
    cases m with
    | zero => simp
    | succ n => rw [show j + (n + 1) - 1 = j + n by omega, Nat.add_sub_cancel]; ring
  rw [h, pow_add, (Nat.even_mul_pred_self m).neg_one_pow, mul_one]

theorem det_flagMat (j m : ℕ) :
    (flagMat j m).det = (-1) ^ (j * m) * ∏ i : Fin m, ((i : ℕ).factorial : ℚ) / ((j + i : ℕ).factorial : ℚ) := by
  have h1 := det_permute' (blockSwap j m) (flagMat j m)
  have h2 : ((flagMat j m).submatrix id (blockSwap j m)).det = (invFactMat j m).det := by
    rw [← det_submatrix_equiv_self finSumFinEquiv]
    have : ((flagMat j m).submatrix id (blockSwap j m)).submatrix finSumFinEquiv finSumFinEquiv =
        fromBlocks 1 0 (Matrix.of fun r k => flagMat j m (Fin.natAdd j r) (blockSwap j m (Fin.castAdd m k)))
          (invFactMat j m) := by
      ext (i | r) (k | r')
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, fromBlocks_apply₁₁, flagMat, of_apply,
          Fin.val_castAdd, blockSwap_castAdd, Matrix.one_apply, Fin.ext_iff]
        rw [if_pos i.isLt]
        by_cases h : (i : ℕ) = k
        · rw [if_pos (by omega), if_pos h]
        · rw [if_neg (by omega), if_neg h]
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
          fromBlocks_apply₁₂, flagMat, of_apply, Fin.val_castAdd, blockSwap_natAdd, Matrix.zero_apply]
        rw [if_pos i.isLt, if_neg (by omega)]
      · simp
      · simp only [submatrix_apply, id, finSumFinEquiv_apply_right, fromBlocks_apply₂₂, flagMat, of_apply,
          Fin.val_natAdd, blockSwap_natAdd, invFactMat]
        rw [if_neg (by omega)]
    rw [this, det_fromBlocks_zero₁₂, det_one, one_mul]
  rw [h2, sign_blockSwap, det_invFactMat] at h1
  push_cast at h1
  have hs : ((-1 : ℚ) ^ (j * m)) * (-1) ^ (j * m) = 1 := by rw [← mul_pow]; simp
  linear_combination (-((-1 : ℚ) ^ (j * m))) * h1 - (flagMat j m).det * hs

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

namespace FlagIntMuOne

open MvPolynomial Finset

noncomputable def rhoPerm (N : ℕ) (σ : Equiv.Perm (Fin N)) : Unit × Fin N →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun p => N - 1 - (σ p.2 : ℕ)

theorem flagInt_unit_eq (N : ℕ) (P : RootPoly Unit N) :
    flagInt Unit N P =
      ∑ σ : Equiv.Perm (Fin N), ((Equiv.Perm.sign σ : ℤ) : ℚ) * coeff (rhoPerm N σ) P := by
  unfold flagInt antisym
  rw [coeff_sum, ← (Equiv.funUnique Unit (Equiv.Perm (Fin N))).symm.sum_comp]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [coeff_smul, smul_eq_mul]
  congr 1
  · simp [weylSign]
  · have hinj : Function.Injective (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) := by
      rintro ⟨⟨⟩, a⟩ ⟨⟨⟩, b⟩ h
      simpa [weylAct] using h
    have hρ : rhoMono Unit N =
        Finsupp.mapDomain (weylAct Unit N ((Equiv.funUnique Unit _).symm σ)) (rhoPerm N σ) := by
      ext ⟨⟨⟩, k⟩
      obtain ⟨i, rfl⟩ := σ.surjective k
      have : ((), σ i) = weylAct Unit N ((Equiv.funUnique Unit _).symm σ) ((), i) := rfl
      rw [this, Finsupp.mapDomain_apply hinj]
      simp [rhoMono, rhoPerm, weylAct]
    rw [hρ, coeff_rename_mapDomain _ hinj]

theorem muPoly_eq_sum (N j : ℕ) :
    muPoly Unit N j = ∑ p, (if (p.2 : ℕ) < j then (0 : ℚ) else 1) • X p := by
  unfold muPoly
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> simp_all

theorem coeff_muPow_rhoBlock (j m : ℕ) (σ : Equiv.Perm (Fin (j + m))) :
    coeff (rhoPerm (j + m) σ)
        (muPoly Unit (j + m) j ^ (j * m) * monomial (rhoBlock Unit (j + m) j) 1) =
      ((j * m).factorial : ℚ) * ∏ i, flagMat j m i (σ i) := by
  set d := rhoPerm (j + m) σ with hd
  set s := rhoBlock Unit (j + m) j with hs
  have hdv : ∀ i : Fin (j + m), d ((), i) = j + m - 1 - (σ i : ℕ) := fun i => rfl
  have hsv : ∀ i : Fin (j + m), s ((), i) = if (i : ℕ) < j then j - 1 - (i : ℕ) else j + m - 1 - (i : ℕ) :=
    fun i => rfl

  have hpt : ∀ i : Fin (j + m), flagMat j m i (σ i) =
      if s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
      then (((d ((), i) - s ((), i)).factorial : ℚ))⁻¹ else 0 := by
    intro i
    have hi := i.isLt
    have hσ := (σ i).isLt
    simp only [flagMat, Matrix.of_apply, hdv, hsv]
    by_cases hij : (i : ℕ) < j
    · simp only [hij, if_true, forall_const]
      by_cases h : (σ i : ℕ) = m + i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j - 1 - i) = 0 by omega]
        simp
      · rw [if_neg h, if_neg (by omega)]
    · simp only [hij, if_false, false_implies, and_true]
      by_cases h : (σ i : ℕ) ≤ i
      · rw [if_pos h, if_pos (by omega), show j + m - 1 - (σ i : ℕ) - (j + m - 1 - i) = i - σ i by omega]
      · rw [if_neg h, if_neg (by omega)]
  rw [coeff_mul_monomial', muPoly_eq_sum, coeff_linearCombination_X_pow_of_fintype]
  by_cases hall : ∀ i : Fin (j + m), s ((), i) ≤ d ((), i) ∧ ((i : ℕ) < j → d ((), i) - s ((), i) = 0)
  · have hle : s ≤ d := by
      intro p
      obtain ⟨⟨⟩, i⟩ := p
      exact (hall i).1
    have hev : ∀ i : Fin (j + m), ((d - s) ((), i) : ℤ) = (i : ℤ) - (σ i : ℤ) + (if (i : ℕ) < j then (m : ℤ) else 0) := by
      intro i
      have hi := i.isLt
      have hσ := (σ i).isLt
      have := hall i
      rw [Finsupp.tsub_apply, hdv, hsv] at *
      split_ifs at * with hij <;> omega
    have hsumN : ∑ i : Fin (j + m), (d - s) ((), i) = j * m := by
      have hz : ((∑ i : Fin (j + m), (d - s) ((), i) : ℕ) : ℤ) = ((j * m : ℕ) : ℤ) := by
        have hσsum : ∑ i : Fin (j + m), ((σ i : ℕ) : ℤ) = ∑ i : Fin (j + m), ((i : ℕ) : ℤ) :=
          Equiv.sum_comp σ (fun i => ((i : ℕ) : ℤ))
        rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => hev i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
          hσsum, sub_self, zero_add, Fin.sum_univ_add]
        simp
      exact_mod_cast hz
    have hsum : (d - s).sum (fun _ k => k) = j * m := by
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fintype.sum_prod_type]
      simpa using hsumN
    have hprod : ((d - s).prod fun r k => (if (r.2 : ℕ) < j then (0 : ℚ) else 1) ^ k) = 1 := by
      rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
      refine Finset.prod_eq_one fun p _ => ?_
      obtain ⟨⟨⟩, i⟩ := p
      by_cases hij : (i : ℕ) < j
      · simp only [Finsupp.tsub_apply]
        rw [(hall i).2 hij, pow_zero]
      · simp [hij]
    have hmult : (((d - s).multinomial : ℕ) : ℚ) =
        ((j * m).factorial : ℚ) / ∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ) := by
      have h := Nat.multinomial_spec (Finset.univ : Finset (Unit × Fin (j + m))) (DFunLike.coe (d - s))
      rw [← Finsupp.multinomial_eq_of_support_subset (Finset.subset_univ _)] at h
      rw [Fintype.sum_prod_type, Fintype.prod_prod_type] at h
      simp only [Finset.univ_unique, Finset.sum_singleton, Finset.prod_singleton, PUnit.default_eq_unit] at h
      rw [hsumN] at h
      have hP : (∏ i : Fin (j + m), (((d - s) ((), i)).factorial : ℚ)) ≠ 0 :=
        prod_ne_zero_iff.mpr fun i _ => by positivity
      rw [eq_div_iff hP, mul_comm]
      exact_mod_cast h
    rw [if_pos hle, if_pos hsum, hprod, mul_one, mul_one, hmult, div_eq_mul_inv, ← prod_inv_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [hpt, if_pos (hall i), Finsupp.tsub_apply]
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hpt, if_neg (by tauto)]), mul_zero]
    split_ifs with hle hsum
    · rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), mul_one]
      refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ ((), i)) ?_)
      obtain ⟨hij, hne⟩ := hi (hle ((), i))
      simp [hij, Finsupp.tsub_apply, hne]
    · simp
    · simp

end FlagIntMuOne

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial FlagIntMuOne

theorem FlagIntMuOne.proof : FlagIntMuOne.Statement := by
  intro N j hjN
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjN
  rw [Nat.add_sub_cancel_left, flagInt_unit_eq]
  simp_rw [coeff_muPow_rhoBlock]
  have hdet : (flagMat j m).det =
      ∑ σ : Equiv.Perm (Fin (j + m)), ((Equiv.Perm.sign σ : ℤ) : ℚ) * ∏ i, flagMat j m i (σ i) := by
    rw [← Matrix.det_transpose, Matrix.det_apply']
    rfl
  calc ∑ σ : Equiv.Perm (Fin (j + m)),
        ((Equiv.Perm.sign σ : ℤ) : ℚ) * (((j * m).factorial : ℚ) * ∏ i, flagMat j m i (σ i))
      = ((j * m).factorial : ℚ) * (flagMat j m).det := by
        rw [hdet, Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        ring
    _ = (-1) ^ (j * m) * grassDeg j m := by
        rw [det_flagMat, prod_factorial_div_comm, grassDeg]
        ring

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
