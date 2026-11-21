import Formalism.HermitianCurvature.StatementWd

namespace Formalism.FourierDecayAlt.P.Wd2

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd

section Units

variable {A S : Type} [Ring A] [Fintype S] [DecidableEq S]

theorem eU_mul (a : S) (i j k l : Fin 2) :
    (eU a i j : SlopeTestRemainingChoices S A) * eU a k l = if j = k then eU a i l else 0 := by
  ext x z
  rw [Matrix.mul_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, Finset.sum_eq_single (Function.update x a j)]
    · simp (config := { contextual := true }) only [eU, Matrix.of_apply, Function.update_self,
        Function.update_apply, true_and, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul]
      by_cases hx : x a = i ∧ z a = l ∧ ∀ b, b ≠ a → x b = z b
      · simp [hx]
      · rw [if_neg hx]
        split_ifs <;> simp_all
    · intro y _ hy
      simp only [eU, Matrix.of_apply]
      split_ifs with h1 h2 <;> simp only [mul_one, mul_zero, zero_mul]
      exfalso
      apply hy
      funext b
      by_cases hb : b = a
      · subst hb
        rw [Function.update_self, h1.2.1]
      · rw [Function.update_of_ne hb, h1.2.2 b hb]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg hjk, Matrix.zero_apply]
    refine Finset.sum_eq_zero fun y _ => ?_
    simp only [eU, Matrix.of_apply]
    split_ifs with h1 h2
    · exact absurd (h1.2.1.symm.trans h2.1) hjk
    all_goals simp

end Units

section Entries

variable {K B : Type} [CommRing K] [Ring B] [Algebra K B]

theorem kronecker_E1_E2_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E1 M * E2 N) (i, k) (j, l) = M i j * N k l := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]

theorem kronecker_embed_mul_apply (M N : Matrix (Fin 2) (Fin 2) B) (i k j l : Fin 2) :
    (E2 N * E1 M) (i, k) (j, l) = N k l * M i j := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp [E1, E2]

theorem Pf_mul_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (i k : Fin 2) (p : Fin 2 × Fin 2) :
    (Pf B * X) (i, k) p = X (k, i) p := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases i <;> fin_cases k <;> simp [Pf]

theorem mul_Pf_apply (X : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) (p : Fin 2 × Fin 2) (j l : Fin 2) :
    (X * Pf B) p (j, l) = X p (l, j) := by
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  fin_cases j <;> fin_cases l <;> simp [Pf]

theorem rtt_entry (M N : Matrix (Fin 2) (Fin 2) B) (D : K)
    (H : (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B) * E1 M * E2 N =
      E2 N * E1 M * (D • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) B) - Pf B))
    (i j k l : Fin 2) :
    D • (M i j * N k l) - M k j * N i l = D • (N k l * M i j) - N k j * M i l := by
  have h := congrFun (congrFun H (i, k)) (j, l)
  rw [mul_assoc, sub_mul, mul_sub, smul_mul_assoc, one_mul, mul_smul_comm, mul_one] at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, Pf_mul_apply, mul_Pf_apply, kronecker_E1_E2_apply,
    kronecker_embed_mul_apply] at h
  exact h

end Entries

section Slots

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]


theorem eU_mul_ins (a : S) (m i : Fin 2) (N : M2 (SlopeTestRemainingChoices S A)) :
    eU a m i * ins a N = ∑ l, eU a m l * N i l := by
  unfold ins
  rw [Finset.mul_sum, Finset.sum_eq_single i]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_pos rfl]
  · intro k _ hk
    rw [Finset.mul_sum]
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [← mul_assoc, eU_mul, if_neg (Ne.symm hk), zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem ins_mul_eU (a : S) (N : M2 (SlopeTestRemainingChoices S A)) (hN : FreeOf2 a N) (j m : Fin 2) :
    ins a N * eU a j m = ∑ k, eU a k m * N k j := by
  unfold ins
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul, Finset.sum_eq_single j]
  · rw [mul_assoc, ← (hN k j j m).eq, ← mul_assoc, eU_mul, if_pos rfl]
  · intro l _ hl
    rw [mul_assoc, ← (hN k l j m).eq, ← mul_assoc, eU_mul, if_neg hl, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h



end Slots

section Start

variable {K A S : Type} [Field K] [Ring A] [Algebra K A] [Fintype S] [DecidableEq S]

theorem io_smul (c : K) (x : A) : (io (c • x) : SlopeTestRemainingChoices S A) = c • io x := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.smul_apply, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem io_algebraMap (c : K) : (io (algebraMap K A c) : SlopeTestRemainingChoices S A) = algebraMap K (SlopeTestRemainingChoices S A) c := by
  ext x y
  simp only [io, Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply,
    Pi.algebraMap_apply]

theorem liftMatrix_eq_map_scalar (M : M2 A) : (lift0 M : M2 (SlopeTestRemainingChoices S A)) = M.map (Matrix.scalar (Ix S)) := rfl

theorem firstEmbed_liftMatrix (M : M2 A) :
    E1 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E1 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E1, lift0, io, Matrix.of_apply, Matrix.map_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem secondEmbed_liftMatrix (M : M2 A) :
    E2 (lift0 M : M2 (SlopeTestRemainingChoices S A)) = (E2 M).map (Matrix.scalar (Ix S)) := by
  ext p q
  simp only [E2, lift0, io, Matrix.of_apply, Matrix.map_apply]
  split_ifs <;> simp

theorem core_map (c : K) :
    c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A) =
      (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext p q : 1
  simp only [Pf, Matrix.map_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply,
    Matrix.of_apply]
  split_ifs <;> simp [map_sub, map_neg, hsc]

theorem J_map : YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) = (YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem smulJ_map (c : K) :
    algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) =
      (algebraMap K A c • YangianSpanCharacter.T.J A).map (Matrix.scalar (Ix S)) := by
  have hsc : ∀ x : A, Matrix.scalar (Ix S) (c • x) = c • Matrix.scalar (Ix S) x := io_smul c
  ext i j : 1
  fin_cases i <;> fin_cases j <;> simp [YangianSpanCharacter.T.J, Algebra.algebraMap_eq_smul_one, hsc] <;>
    (try (ext x y; simp only [Matrix.neg_apply, Matrix.one_apply, Matrix.diagonal_apply,
      Matrix.smul_apply]; split_ifs <;> simp))

theorem rtt_lift0 (M N : M2 A) (c : K)
    (H : (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A) * E1 M * E2 N =
      E2 N * E1 M * (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) A) - Pf A)) :
    (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) *
        E1 (lift0 M) * E2 (lift0 N) =
      E2 (lift0 N) * E1 (lift0 M) *
        (c • (1 : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) (SlopeTestRemainingChoices S A)) - Pf (SlopeTestRemainingChoices S A)) := by
  rw [core_map, firstEmbed_liftMatrix, secondEmbed_liftMatrix, ← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0 (M M' : M2 A) (c : K) (H : M'ᵀ * YangianSpanCharacter.T.J A * M = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M' : M2 (SlopeTestRemainingChoices S A))ᵀ * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * lift0 M = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem det_lift0' (M M' : M2 A) (c : K) (H : M * YangianSpanCharacter.T.J A * M'ᵀ = algebraMap K A c • YangianSpanCharacter.T.J A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A)) * YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) * (lift0 M')ᵀ = algebraMap K (SlopeTestRemainingChoices S A) c • YangianSpanCharacter.T.J (SlopeTestRemainingChoices S A) := by
  rw [smulJ_map, liftMatrix_eq_map_scalar, liftMatrix_eq_map_scalar, J_map, ← Matrix.transpose_map, ← Matrix.map_mul,
    ← Matrix.map_mul, H]

theorem liftMatrix_conjTranspose [StarRing A] (M : M2 A) :
    (lift0 M : M2 (SlopeTestRemainingChoices S A))ᴴ = lift0 Mᴴ := by
  ext i j x y
  simp [lift0, io, Matrix.conjTranspose_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    Matrix.star_apply]
  split_ifs <;> simp_all [@eq_comm _ y x]

theorem d0_one : (d0 (1 : SlopeTestRemainingChoices S A)) = 1 := by
  unfold d0
  exact Matrix.diagonal_one

end Start

end Formalism.FourierDecayAlt.P.Wd2

namespace Formalism.FourierDecayAlt.P

open Matrix Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.W Formalism.FourierDecayAlt.Wd



theorem initial_module_structure : Formalism.FourierDecayAlt.Wd.StartModule := by
  intro K A S _ _ _ _ _ _ _ _ QQ q hS
  refine ⟨star_one _, fun Y _ hY => ?_, fun Y _ Y' _ => ?_, fun Y _ _ => ?_, hS.q_real⟩
  · rw [Formalism.FourierDecayAlt.P.Wd2.d0_one, one_mul, Formalism.FourierDecayAlt.P.Wd2.liftMatrix_conjTranspose, hS.herm Y hY]
  · exact Formalism.FourierDecayAlt.P.Wd2.rtt_lift0 (QQ Y') (QQ Y) (Y' - Y) (hS.rtt Y Y')
  · exact ⟨Formalism.FourierDecayAlt.P.Wd2.det_lift0 (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).1,
      Formalism.FourierDecayAlt.P.Wd2.det_lift0' (QQ Y) (QQ (Y + 1)) (q Y) (hS.det Y).2⟩

end Formalism.FourierDecayAlt.P
