import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfLoZero
import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.NuOfWtPQCast

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem midOf_zero (r : ℕ) : midOf (0 : Fin (r + 1 + 1)) = none := by
  unfold midOf
  rw [dif_neg]
  simp

theorem subY_X_zero (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) : subY A r (X (a, 0)) = X (a, 0) := by
  simp only [subY, aeval_X, midOf_zero]

theorem subY_X_mid (A : Type) [CommRing A] (r : ℕ) (a : Fin (r + 1 + 1)) (j : Fin r) :
    subY A r (X (a, midI r j)) = ∑ i : Fin r, C (X (i, j)) * X (a, midI r i) := by
  simp only [subY, aeval_X, midOf_midI]

def dOneY (A : Type) [CommRing A] (r : ℕ) :
    Matrix (Fin (r + 1)) (Fin (r + 1)) (MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A)) :=
  fun s t => Fin.cases (Fin.cases 1 (fun _ => 0) t) (fun s' => Fin.cases 0 (fun t' => C (X (s', t'))) t) s

theorem det_dOneY (A : Type) [CommRing A] (r : ℕ) : (dOneY A r).det = C (detY A r) := by
  rw [Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have h0 : ∀ i : Fin r, dOneY A r i.succ 0 = 0 := fun i => rfl
  have h1 : dOneY A r 0 0 = 1 := rfl
  simp only [h0, h1, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero, one_mul]
  unfold detY
  have h := RingHom.map_det (C : MvPolynomial (Fin r × Fin r) A →+*
    MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) (MvPolynomial (Fin r × Fin r) A))
    (Matrix.of fun i j : Fin r => (X (i, j) : MvPolynomial (Fin r × Fin r) A))
  refine Eq.trans ?_ h.symm
  congr 1

theorem subY_covY (K : Type) [Field K] (r : ℕ) (i : Fin (r + 1 + 1)) :
    subY K r (covY K (r + 1) i) = C (detY K r) * map C (covY K (r + 1) i) := by
  unfold covY
  rw [map_mul, map_mul, map_pow, map_pow, map_neg, map_neg, map_one, map_one]
  have hA := AlgHom.map_det (subY K r)
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hB := RingHom.map_det (map (C : K →+* MvPolynomial (Fin r × Fin r) K))
    (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K))
  have hM : (subY K r).mapMatrix
      (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      (map (C : K →+* MvPolynomial (Fin r × Fin r) K)).mapMatrix
        (Matrix.of fun a b : Fin (r + 1) => (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) *
        dOneY K r := by
    apply Matrix.ext
    intro a b
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    induction b using Fin.cases with
    | zero =>
      have h0 : ∀ s : Fin r, dOneY K r s.succ 0 = 0 := fun s => rfl
      have h1 : dOneY K r 0 0 = 1 := rfl
      simp only [h0, h1, mul_zero, Finset.sum_const_zero, add_zero, mul_one]
      show subY K r (X (i.succAbove a, (0 : Fin (r + 1)).castSucc)) = map C (X (i.succAbove a, (0 : Fin (r + 1)).castSucc))
      rw [Fin.castSucc_zero, subY_X_zero, map_X]
    | succ j =>
      have h0 : dOneY K r 0 j.succ = 0 := rfl
      have h1 : ∀ s : Fin r, dOneY K r s.succ j.succ = C (X (s, j)) := fun s => rfl
      simp only [h0, h1, mul_zero, zero_add]
      show subY K r (X (i.succAbove a, j.succ.castSucc)) =
        ∑ s : Fin r, map C (X (i.succAbove a, s.succ.castSucc)) * C (X (s, j))
      have e : ∀ s : Fin r, s.succ.castSucc = midI r s := fun s => (Fin.succ_castSucc s).symm
      simp only [e, map_X]
      rw [subY_X_mid]
      exact Finset.sum_congr rfl fun s _ => mul_comm _ _
  have hdet : subY K r (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) =
      C (detY K r) * map C (Matrix.det fun a b : Fin (r + 1) =>
      (X (i.succAbove a, b.castSucc) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1)) K)) := by
    refine hA.trans ?_
    rw [hM, Matrix.det_mul, det_dOneY, mul_comm]
    congr 1
    exact hB.symm
  rw [hdet]
  ring

theorem subY_dPsi_monomial (K : Type) [Field K] (r : ℕ) (v : XY (r + 1 + 1) →₀ ℕ) (c : K) :
    subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) =
      C (detY K r ^ yDeg v) * map C (deltaB K (r + 1) (PsiXY K (r + 1) (monomial v c))) := by
  have hx : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (r + 1 + 1), deltaB K (r + 1) (PsiXY K (r + 1) (X (Sum.inr i))) = covY K (r + 1) i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (r + 1 + 1) × Fin (r + 1 + 1) → Fin (r + 1 + 1) × Fin (r + 1 + 1)) = id := rfl
    rw [this, rename_id_apply]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, subY_X_zero, subY_covY, mul_pow, Finset.prod_mul_distrib, map_X]
  have hC : subY K r (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) = map C (deltaB K (r + 1) (PsiXY K (r + 1) (C c))) := by
    simp only [← algebraMap_eq, AlgHom.commutes]
    simp [algebraMap_eq]
  rw [hC]
  have hp : ∏ i : Fin (r + 1 + 1), (C (detY K r) : MvPolynomial (Fin (r + 1 + 1) × Fin (r + 1 + 1))
      (MvPolynomial (Fin r × Fin r) K)) ^ v (Sum.inr i) = C (detY K r) ^ yDeg v := by
    rw [Finset.prod_pow_eq_pow_sum]
    rfl
  rw [hp]
  ring

theorem subMuP_of (h2 : ExplicitMapOntoTwoLetters) (h5 : TwoLetterLatticeGaussInverse) (hCO : CartanOnto) : SubMuP := by
  intro p n' R r hr P Q F hF
  rw [← tie3 h2 h5 hCO R (r + 1) (by omega) P Q] at hF
  obtain ⟨f, hf, rfl⟩ := hF
  rw [dPsi_apply, f.as_sum]
  simp only [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun v hv => ?_
  rw [subY_dPsi_monomial, (hf v hv).2]

end Formalism.MainNotions.flipOneThree.Pf

end
end

section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial Formalism.MainNotions.G.LatticeSystems

theorem rowA_of_iwh {K : Type} [CommRing K] {k n : ℕ} {f : MvPolynomial (Fin k × Fin n) K} {μ : Fin k → ℕ}
    (h : IsWeightedHomogeneous (rowW k n) f μ) (a : Fin k) : RowA a f (μ a) := by
  intro u hu
  rw [← ldrow_weight_rowW, h hu]

theorem qt_cnt (m : ℕ) (i a' : Fin (m + 1)) :
    (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ)) a' = if a' = i then 0 else 1 := by
  classical
  rw [Finset.sum_apply]
  simp only [Pi.single_apply]
  split_ifs with h
  · subst h
    exact Finset.sum_eq_zero fun p _ => if_neg (Fin.succAbove_ne a' p).symm
  · obtain ⟨q, rfl⟩ := Fin.exists_succAbove_eq h
    rw [Finset.sum_eq_single q]
    · rw [if_pos rfl]
    · intro p _ hp
      exact if_neg fun e => hp (Fin.succAbove_right_injective e).symm
    · intro hq
      exact absurd (Finset.mem_univ q) hq

theorem qt_covY_iwh (K : Type) [Field K] (m : ℕ) (i : Fin (m + 1)) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (covY K m i) (∑ p : Fin m, Pi.single (i.succAbove p) 1) := by
  have e : covY K m i = ((-1 : ℤ) ^ (i : ℕ)) • initMinor K (n := m + 1) i.succAbove (Nat.le_succ m) := by
    rw [zsmul_eq_mul]
    push_cast
    rfl
  rw [e, ← mem_weightedHomogeneousSubmodule]
  exact zsmul_mem ((mem_weightedHomogeneousSubmodule _ _ _ _).2 (ldbasis_initMinor_rowHom K i.succAbove (Nat.le_succ m))) _

theorem dPsi_monomial (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    deltaB K m (PsiXY K m (monomial v c)) =
      C c * ((∏ i : Fin (m + 1), X (i, (0 : Fin (m + 1))) ^ v (Sum.inl i)) * ∏ i : Fin (m + 1), covY K m i ^ v (Sum.inr i)) := by
  have hx : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inl i))) = X (i, 0) := by
    intro i
    simp [PsiXY, deltaB]
  have hy : ∀ i : Fin (m + 1), deltaB K m (PsiXY K m (X (Sum.inr i))) = covY K m i := by
    intro i
    simp only [PsiXY, deltaB, aeval_X, Sum.elim_inr, rename_rename]
    have : (Prod.snd ∘ Prod.mk false : Fin (m + 1) × Fin (m + 1) → Fin (m + 1) × Fin (m + 1)) = id := rfl
    rw [this, rename_id_apply]
  have hC : deltaB K m (PsiXY K m (C c)) = C c := by
    simp only [← algebraMap_eq, AlgHom.commutes]
  rw [monomial_eq, Finsupp.prod_fintype _ _ (by simp), Fintype.prod_sum_type]
  simp only [map_mul, map_prod, map_pow, hx, hy, hC]

def qtW (m : ℕ) (v : XY (m + 1) →₀ ℕ) : Fin (m + 1) → ℕ :=
  0 + ((∑ i : Fin (m + 1), v (Sum.inl i) • (Pi.single i 1 : Fin (m + 1) → ℕ)) +
    ∑ i : Fin (m + 1), v (Sum.inr i) • ∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ))

theorem dPsi_monomial_iwh (K : Type) [Field K] (m : ℕ) (v : XY (m + 1) →₀ ℕ) (c : K) :
    IsWeightedHomogeneous (rowW (m + 1) (m + 1)) (deltaB K m (PsiXY K m (monomial v c))) (qtW m v) := by
  rw [dPsi_monomial]
  refine (isWeightedHomogeneous_C _ c).mul (IsWeightedHomogeneous.mul ?_ ?_)
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (isWeightedHomogeneous_X K (rowW (m + 1) (m + 1)) (i, 0)).pow _
  · exact IsWeightedHomogeneous.prod _ _ _ fun i _ => (qt_covY_iwh K m i).pow _

theorem qtW_apply (m : ℕ) (v : XY (m + 1) →₀ ℕ) (a' : Fin (m + 1)) :
    qtW m v a' + v (Sum.inr a') = v (Sum.inl a') + yDeg v := by
  classical
  unfold qtW yDeg
  simp only [Pi.add_apply, Pi.zero_apply, zero_add, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have h1 : ∑ i : Fin (m + 1), v (Sum.inl i) * (Pi.single i 1 : Fin (m + 1) → ℕ) a' = v (Sum.inl a') := by
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  have h2 : ∀ i : Fin (m + 1), (∑ p : Fin m, (Pi.single (i.succAbove p) 1 : Fin (m + 1) → ℕ) a') = if a' = i then 0 else 1 := by
    intro i
    rw [← Finset.sum_apply]
    exact qt_cnt m i a'
  have h3 : v (Sum.inr a') = ∑ i : Fin (m + 1), v (Sum.inr i) * (if a' = i then 1 else 0) := by
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp
  rw [h1, add_assoc]
  congr 1
  simp only [h2]
  conv_lhs => rw [h3]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

end Formalism.MainNotions.flipOneThree.Pf

end
end
