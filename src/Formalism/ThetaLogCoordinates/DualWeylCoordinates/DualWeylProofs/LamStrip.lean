import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsColHHigh
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.QsMnTranspose

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_sr (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R :=
  ∏ a ∈ A, ∏ k ∈ K, (if k < a then (-1 : R) else 1)

def wedgeSign (R : Type*) [CommRing R] (A K : Finset (Fin n)) : R := if Disjoint A K then ql_sr R A K else 0

def ql_w (R : Type*) [CommRing R] (A K I : Finset (Fin n)) : R := if A ∪ K = I then wedgeSign R A K else 0

variable {R : Type*} [CommRing R]

lemma ql_sr_union_left {A B : Finset (Fin n)} (h : Disjoint A B) (C : Finset (Fin n)) :
    ql_sr R (A ∪ B) C = ql_sr R A C * ql_sr R B C := prod_union h

lemma ql_sr_union_right (A : Finset (Fin n)) {B C : Finset (Fin n)} (h : Disjoint B C) :
    ql_sr R A (B ∪ C) = ql_sr R A B * ql_sr R A C := by
  simp only [ql_sr, prod_union h, prod_mul_distrib]

lemma ql_s_assoc (A B C : Finset (Fin n)) :
    wedgeSign R A B * wedgeSign R (A ∪ B) C = wedgeSign R B C * wedgeSign R A (B ∪ C) := by
  unfold wedgeSign
  by_cases hAB : Disjoint A B <;> by_cases hAC : Disjoint A C <;> by_cases hBC : Disjoint B C <;>
    simp only [disjoint_union_left, disjoint_union_right, hAB, hAC, hBC, if_true, if_false, and_true,
      and_false, and_self, mul_zero, zero_mul]
  rw [ql_sr_union_left hAB, ql_sr_union_right _ hBC]; ring

lemma ql_sr_single (A : Finset (Fin n)) (m : Fin n) : ql_sr R A {m} = ((qs_sg A m : ℤ) : R) := by
  simp only [ql_sr, prod_singleton, qs_sg]
  rw [prod_ite]; simp

lemma ql_sr_isUnit (A K : Finset (Fin n)) : IsUnit (ql_sr R A K) := by
  unfold ql_sr
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun a _ => ?_
  refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun k _ => ?_
  split_ifs
  · exact isUnit_one.neg
  · exact isUnit_one

lemma ql_s_isUnit {A K : Finset (Fin n)} (h : Disjoint A K) : IsUnit (wedgeSign R A K) := by
  rw [wedgeSign, if_pos h]; exact ql_sr_isUnit A K

lemma ql_sr_cast (A K : Finset (Fin n)) : ((ql_sr ℤ A K : ℤ) : R) = ql_sr R A K := by
  simp only [ql_sr, Int.cast_prod]
  refine prod_congr rfl fun a _ => prod_congr rfl fun k _ => ?_
  split_ifs <;> simp

lemma ql_s_cast (A K : Finset (Fin n)) : ((wedgeSign ℤ A K : ℤ) : R) = wedgeSign R A K := by
  unfold wedgeSign; split_ifs
  · exact ql_sr_cast A K
  · simp

lemma ql_w_cast (A K I : Finset (Fin n)) : ((ql_w ℤ A K I : ℤ) : R) = ql_w R A K I := by
  unfold ql_w; split_ifs
  · exact ql_s_cast A K
  · simp

lemma ql_sum_w (A K : Finset (Fin n)) (f : Finset (Fin n) → R) :
    ∑ I, f I * ql_w R A K I = wedgeSign R A K * f (A ∪ K) := by
  simp [ql_w, mul_comm]

lemma ql_w_assoc (A B C I : Finset (Fin n)) :
    ∑ M, ql_w R A B M * ql_w R M C I = ∑ M, ql_w R B C M * ql_w R A M I := by
  have h1 : ∑ M, ql_w R A B M * ql_w R M C I = wedgeSign R A B * ql_w R (A ∪ B) C I := by
    rw [← ql_sum_w A B (fun M => ql_w R M C I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  have h2 : ∑ M, ql_w R B C M * ql_w R A M I = wedgeSign R B C * ql_w R A (B ∪ C) I := by
    rw [← ql_sum_w B C (fun M => ql_w R A M I)]; exact sum_congr rfl fun _ _ => mul_comm _ _
  rw [h1, h2, ql_w, ql_w, union_assoc]
  split_ifs
  · exact ql_s_assoc A B C
  · simp

lemma ql_w_single (M I : Finset (Fin n)) (k : Fin n) :
    ql_w R M {k} I = if M = I.erase k then (if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) else 0) else 0 := by
  by_cases hM : M = I.erase k
  · subst hM
    rw [if_pos rfl]
    by_cases hk : k ∈ I
    · have : I.erase k ∪ {k} = I := by
        rw [union_comm, ← insert_eq, insert_erase hk]
      rw [if_pos hk, ql_w, if_pos this, wedgeSign, if_pos (by simp), ql_sr_single]
    · rw [if_neg hk, ql_w, if_neg]
      intro h; exact hk (h ▸ mem_union_right _ (mem_singleton_self k))
  · rw [if_neg hM, ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hd
      apply hM
      rw [← h, union_comm, ← insert_eq, erase_insert (by simpa using hd)]
    · rfl

lemma sum_four_comm_form {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] (F : α → β → γ → δ → R) :
    ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, F a b c d = ∑ a, ∑ c, ∑ b, ∑ d, F a b c d := sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ a, ∑ b, ∑ d, F a b c d := sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun a _ => sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, F a b c d := sum_congr rfl fun c _ => sum_comm
    _ = ∑ c, ∑ d, ∑ b, ∑ a, F a b c d := sum_congr rfl fun c _ => sum_congr rfl fun d _ => sum_comm

variable (g : Matrix (Fin n) (Fin n) R)

lemma laplace_expansion_column (B I : Finset (Fin n)) (m : Fin n) :
    ∑ M, ∑ k, qs_mn g M B * g k m * ql_w R M {k} I = wedgeSign R B {m} * qs_mn g I (B ∪ {m}) := by
  rw [sum_comm]
  have h1 : ∀ k, ∑ M, qs_mn g M B * g k m * ql_w R M {k} I =
      if k ∈ I then ((qs_sg (I.erase k) k : ℤ) : R) * qs_mn g (I.erase k) B * g k m else 0 := by
    intro k
    simp only [ql_w_single, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
    split_ifs
    · ring
    · rfl
  simp only [h1]
  rw [sum_ite_mem, univ_inter, qs_laplace_col, wedgeSign]
  by_cases hm : m ∈ B
  · rw [if_pos hm, if_neg (by simpa using hm), zero_mul]
  · rw [if_neg hm, if_pos (by simpa using hm), ql_sr_single, union_comm, ← insert_eq]

lemma ql_mn_empty (K : Finset (Fin n)) : qs_mn g K ∅ = if K = ∅ then 1 else 0 := by
  split_ifs with h
  · subst h; rw [qs_mn_eq g ∅ ∅ (h := 0) rfl rfl]; simp
  · exact qs_mn_ne g (by simpa using h)

lemma ql_s_empty (A : Finset (Fin n)) : wedgeSign R A ∅ = 1 := by simp [wedgeSign, ql_sr]

lemma ql_s_max {K : Finset (Fin n)} {m : Fin n} (h : ∀ x ∈ K, x < m) : wedgeSign R K {m} = 1 := by
  rw [wedgeSign, if_pos (by simpa using fun hm => lt_irrefl _ (h m hm)), ql_sr]
  refine prod_eq_one fun a ha => ?_
  rw [prod_singleton, if_neg (not_lt.2 (h a ha).le)]

theorem ql_lap (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = wedgeSign R A K * qs_mn g I (A ∪ K) := by
  induction K using Finset.induction_on_max generalizing I with
  | empty =>
    simp only [ql_mn_empty, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, sum_ite_eq', mem_univ, if_true,
      ql_s_empty, one_mul, union_empty]
    simp [ql_w, ql_s_empty]
  | insert m K0 hmax ih =>
    have e1 : ∀ K', qs_mn g K' (insert m K0) = ∑ M, ∑ k, qs_mn g M K0 * g k m * ql_w R M {k} K' := by
      intro K'; rw [laplace_expansion_column, ql_s_max hmax, one_mul, union_comm, ← insert_eq]
    have h1 : ∀ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I =
        ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I := by
      intro A'
      simp only [e1, mul_sum, sum_mul]
      rw [sum_comm]; refine sum_congr rfl fun M _ => ?_
      rw [sum_comm]; exact sum_congr rfl fun k _ => sum_congr rfl fun K' _ => by ring
    have h2 : ∑ M', ∑ k, (∑ A', ∑ M, qs_mn g A' A * qs_mn g M K0 * ql_w R A' M M') * g k m * ql_w R M' {k} I =
        ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I := by
      simp only [mul_sum, sum_mul]
      rw [sum_four_comm_form]
      exact sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ =>
        sum_congr rfl fun M' _ => by ring
    calc ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' (insert m K0) * ql_w R A' K' I
        = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ K', ql_w R M {k} K' * ql_w R A' K' I :=
          sum_congr rfl fun A' _ => h1 A'
      _ = ∑ A', ∑ M, ∑ k, qs_mn g A' A * qs_mn g M K0 * g k m * ∑ M', ql_w R A' M M' * ql_w R M' {k} I :=
          sum_congr rfl fun A' _ => sum_congr rfl fun M _ => sum_congr rfl fun k _ => by rw [ql_w_assoc]
      _ = ∑ M', ∑ k, (wedgeSign R A K0 * qs_mn g M' (A ∪ K0)) * g k m * ql_w R M' {k} I := by
          rw [← h2]; simp only [ih]
      _ = wedgeSign R A K0 * ∑ M', ∑ k, qs_mn g M' (A ∪ K0) * g k m * ql_w R M' {k} I := by
          simp only [mul_sum, mul_assoc]
      _ = wedgeSign R A (insert m K0) * qs_mn g I (A ∪ insert m K0) := by
          rw [laplace_expansion_column, ← mul_assoc, ql_s_assoc, ql_s_max hmax, one_mul, union_assoc, union_comm K0, ← insert_eq]

theorem ql_lapT (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A A' * qs_mn g K K' * ql_w R A' K' I = ∑ I', ql_w R A K I' * qs_mn g I' I := by
  have h := ql_lap g.transpose A K I
  simp only [qs_mn_transpose] at h
  rw [h, ← ql_sum_w A K (fun I' => qs_mn g I' I)]
  exact sum_congr rfl fun _ _ => mul_comm _ _

theorem ql_lapM (A K I : Finset (Fin n)) :
    ∑ A', ∑ K', qs_mn g A' A * qs_mn g K' K * ql_w R A' K' I = ∑ I', qs_mn g I I' * ql_w R A K I' := by
  rw [ql_lap, ql_sum_w A K (fun I' => qs_mn g I I')]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_U : (N : ℕ) → (Fin N → Finset (Fin n)) → Finset (Fin n)
  | 0, _ => ∅
  | N + 1, D => D 0 ∪ ql_U N (Fin.tail D)

def ql_sW (R : Type*) [CommRing R] : (N : ℕ) → (Fin N → Finset (Fin n)) → R
  | 0, _ => 1
  | N + 1, D => wedgeSign R (D 0) (ql_U N (Fin.tail D)) * ql_sW R N (Fin.tail D)

def wedgeCoeff (R : Type*) [CommRing R] {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) : R :=
  if ql_U N D = L then ql_sW R N D else 0

variable {R : Type*} [CommRing R]

lemma ql_W_succ {N : ℕ} (D : Fin (N + 1) → Finset (Fin n)) (L : Finset (Fin n)) :
    wedgeCoeff R D L = ∑ M, ql_w R (D 0) M L * wedgeCoeff R (Fin.tail D) M := by
  simp only [wedgeCoeff, mul_ite, mul_zero, sum_ite_eq, mem_univ, if_true, ql_U, ql_sW, ql_w, ite_mul, zero_mul]
  congr

lemma ql_sW_cast : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), ((ql_sW ℤ N D : ℤ) : R) = ql_sW R N D
  | 0, _ => by simp [ql_sW]
  | N + 1, D => by simp only [ql_sW, Int.cast_mul, ql_s_cast, ql_sW_cast N]

lemma ql_W_cast {N : ℕ} (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)) :
    ((wedgeCoeff ℤ D L : ℤ) : R) = wedgeCoeff R D L := by
  unfold wedgeCoeff; split_ifs
  · exact ql_sW_cast N D
  · simp

lemma ql_mem_U : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (a : Fin n), a ∈ ql_U N D ↔ ∃ j, a ∈ D j
  | 0, _, a => by simp [ql_U]
  | N + 1, D, a => by
    rw [ql_U, mem_union, ql_mem_U N, Fin.exists_fin_succ]; rfl

lemma ql_sW_isUnit : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)), (∀ i j, i ≠ j → Disjoint (D i) (D j)) →
    IsUnit (ql_sW R N D)
  | 0, _, _ => by simp [ql_sW]
  | N + 1, D, h => by
    rw [ql_sW]
    refine IsUnit.mul (ql_s_isUnit ?_) (ql_sW_isUnit N _ fun i j hij => h _ _ (by simpa using hij))
    rw [Finset.disjoint_left]
    intro a ha hU
    obtain ⟨j, hj⟩ := (ql_mem_U N _ a).1 hU
    exact Finset.disjoint_left.1 (h 0 j.succ (Fin.succ_ne_zero j).symm) ha hj

lemma ql_sum_cons {N : ℕ} (φ : (Fin (N + 1) → Finset (Fin n)) → R) :
    ∑ D, φ D = ∑ a, ∑ D', φ (Fin.cons a D') := by
  rw [← (Fin.consEquiv (fun _ => Finset (Fin n))).sum_comp, Fintype.sum_prod_type]; rfl

lemma ql_prod_sum {N : ℕ} (G : Fin N → Finset (Fin n) → R) :
    ∏ j, ∑ a, G j a = ∑ x : Fin N → Finset (Fin n), ∏ j, G j (x j) := by
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]

variable (g : Matrix (Fin n) (Fin n) R)

theorem ql_W_equiv : ∀ (N : ℕ) (D : Fin N → Finset (Fin n)) (L : Finset (Fin n)),
    ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (D j)) * wedgeCoeff R D' L = ∑ L', qs_mn g L L' * wedgeCoeff R D L'
  | 0, D, L => by
    simp [wedgeCoeff, ql_U, ql_sW, ql_mn_empty, eq_comm]
  | N + 1, D, L => by
    rw [ql_sum_cons]
    calc ∑ a, ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g ((Fin.cons a D' : Fin (N + 1) → _) j) (D j)) *
            wedgeCoeff R (Fin.cons a D' : Fin (N + 1) → _) L
        = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L *
            ∑ D' : Fin N → Finset (Fin n), (∏ j, qs_mn g (D' j) (Fin.tail D j)) * wedgeCoeff R D' M := by
          refine sum_congr rfl fun a _ => ?_
          simp only [ql_W_succ (Fin.cons a _), Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail_cons,
            mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by simp only [Fin.tail]; ring
      _ = ∑ a, ∑ M, qs_mn g a (D 0) * ql_w R a M L * ∑ M', qs_mn g M M' * wedgeCoeff R (Fin.tail D) M' := by
          simp only [ql_W_equiv N]
      _ = ∑ M', wedgeCoeff R (Fin.tail D) M' * ∑ a, ∑ M, qs_mn g a (D 0) * qs_mn g M M' * ql_w R a M L := by
          simp only [mul_sum]
          symm
          rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
          rw [sum_comm]; exact sum_congr rfl fun M _ => sum_congr rfl fun M' _ => by ring
      _ = ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
          simp only [ql_lapM, ql_W_succ D, mul_sum]
          rw [sum_comm]
          exact sum_congr rfl fun M _ => sum_congr rfl fun D' _ => by ring

def ql_P (R : Type*) [CommRing R] {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n))
    (i : Fin N → Finset (Fin n)) : R :=
  ∑ D : Fin N → Finset (Fin n), (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D L

lemma ql_P_cast {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ((ql_P ℤ k L i : ℤ) : R) = ql_P R k L i := by
  simp only [ql_P, Int.cast_sum, Int.cast_mul, Int.cast_prod, ql_w_cast, ql_W_cast]

theorem ql_P_equiv {N : ℕ} (k : Fin N → Finset (Fin n)) (L : Finset (Fin n)) (i : Fin N → Finset (Fin n)) :
    ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i =
      ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
  calc ∑ k' : Fin N → Finset (Fin n), ∑ L', (∏ j, qs_mn g (k j) (k' j)) * qs_mn g L L' * ql_P R k' L' i
      = ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          (∏ j, qs_mn g (k j) (k' j)) * (∏ j, ql_w R (k' j) (D j) (i j)) * ∑ L', qs_mn g L L' * wedgeCoeff R D L' := by
        refine sum_congr rfl fun k' _ => ?_
        simp only [ql_P, mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L * ∑ k' : Fin N → Finset (Fin n), ∑ D : Fin N → Finset (Fin n),
          ∏ j, qs_mn g (k j) (k' j) * qs_mn g (D' j) (D j) * ql_w R (k' j) (D j) (i j) := by
        simp only [← ql_W_equiv, mul_sum, prod_mul_distrib]
        symm
        rw [sum_comm]; refine sum_congr rfl fun k' _ => ?_
        rw [sum_comm]; exact sum_congr rfl fun D _ => sum_congr rfl fun D' _ => by ring
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∏ j, ∑ a, ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j) := by
        refine sum_congr rfl fun D' _ => ?_
        rw [ql_prod_sum (fun j a => ∑ d, qs_mn g (k j) a * qs_mn g (D' j) d * ql_w R a d (i j))]
        refine congrArg _ (sum_congr rfl fun k' _ => ?_)
        exact (ql_prod_sum (fun j d => qs_mn g (k j) (k' j) * qs_mn g (D' j) d * ql_w R (k' j) d (i j))).symm
    _ = ∑ D' : Fin N → Finset (Fin n), wedgeCoeff R D' L *
          ∑ i' : Fin N → Finset (Fin n), ∏ j, ql_w R (k j) (D' j) (i' j) * qs_mn g (i' j) (i j) := by
        simp only [ql_lapT, ql_prod_sum]
    _ = ∑ i' : Fin N → Finset (Fin n), ql_P R k L i' * ∏ j, qs_mn g (i' j) (i j) := by
        simp only [ql_P, mul_sum, sum_mul, prod_mul_distrib]
        rw [sum_comm]
        exact sum_congr rfl fun D _ => sum_congr rfl fun L' _ => by ring

lemma ql_P_unit {N : ℕ} (k i : Fin N → Finset (Fin n)) (hk : ∀ j, k j ⊆ i j)
    (hd : ∀ j j', j ≠ j' → Disjoint (i j \ k j) (i j' \ k j')) :
    IsUnit (ql_P R k (ql_U N fun j => i j \ k j) i) := by
  have h0 : ∀ D : Fin N → Finset (Fin n), D ≠ (fun j => i j \ k j) →
      (∏ j, ql_w R (k j) (D j) (i j)) * wedgeCoeff R D (ql_U N fun j => i j \ k j) = 0 := by
    intro D hD
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hD
    rw [prod_eq_zero (mem_univ j), zero_mul]
    rw [ql_w]
    split_ifs with h
    · rw [wedgeSign, if_neg]
      intro hdis
      apply hj
      rw [← h, union_sdiff_cancel_left hdis]
    · rfl
  rw [ql_P, sum_eq_single _ (fun D _ hD => h0 D hD) (fun h => absurd (mem_univ _) h)]
  refine IsUnit.mul ?_ ?_
  · refine Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun j _ => ?_
    rw [ql_w, if_pos (union_sdiff_of_subset (hk j))]
    exact ql_s_isUnit disjoint_sdiff
  · rw [wedgeCoeff, if_pos rfl]
    exact ql_sW_isUnit N _ hd

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_E (lo : ℤ) (N : ℕ) (F : ℤ → Finset (Fin n)) : Fin N → Finset (Fin n) := fun j => F (lo + 1 + (j : ℕ))

lemma ql_prod_Ioc {M : Type*} [CommMonoid M] (lo : ℤ) (N : ℕ) (φ : ℤ → M) :
    ∏ c ∈ Finset.Ioc lo (lo + N), φ c = ∏ j : Fin N, φ (lo + 1 + (j : ℕ)) := by
  symm
  refine Finset.prod_bij (fun j _ => lo + 1 + ((j : Fin N) : ℕ)) ?_ ?_ ?_ ?_
  · intro j _; have := j.2; simp only [mem_Ioc]; omega
  · intro i _ j _ h; ext; omega
  · intro c hc
    simp only [mem_Ioc] at hc
    exact ⟨⟨(c - lo - 1).toNat, by omega⟩, mem_univ _, by show lo + 1 + ((c - lo - 1).toNat : ℤ) = c; omega⟩
  · intro j _; rfl

def ql_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ℤ → Finset (Fin n) :=
  fun c => if h : lo < c ∧ c ≤ lo + N then f ⟨(c - lo - 1).toNat, by omega⟩ else if c ≤ lo then univ else ∅

lemma ql_E_fill (lo : ℤ) (N : ℕ) (f : Fin N → Finset (Fin n)) : ql_E lo N (ql_fill lo N f) = f := by
  funext j
  have := j.2
  simp only [ql_E, ql_fill]
  rw [dif_pos ⟨by omega, by omega⟩]
  congr 1
  ext
  show (lo + 1 + (j : ℕ) - lo - 1).toNat = j
  omega

lemma ql_sum_L {M : Type*} [AddCommMonoid M] {b : ℕ} (φ : Finset (Fin n) → M) (hφ : ∀ L, L.card ≠ b → φ L = 0) :
    ∑ L : LamIdx n b, φ L.1 = ∑ L, φ L := by
  refine Fintype.sum_of_injective (fun L : LamIdx n b => L.1) Subtype.val_injective _ _ ?_ (fun _ => rfl)
  intro L hL
  exact hφ L fun h => hL ⟨⟨L, h⟩, rfl⟩

variable [NeZero n]

lemma ql_fill_card {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (f : Fin N → Finset (Fin n)) (hf : ∀ j : Fin N, (f j).card = colH mu (lo + 1 + (j : ℕ))) (c : ℤ) :
    (ql_fill lo N f c).card = colH mu c := by
  unfold ql_fill
  split_ifs with h h'
  · rw [hf]; congr 1
    show lo + 1 + ((c - lo - 1).toNat : ℤ) = c
    omega
  · rw [qs_colH_low hmu (h'.trans h1)]; simp
  · rw [qs_colH_high hmu (by omega)]; simp

lemma ql_E_card {mu : Fin n → ℤ} (hmu : Dominant mu) (lo : ℤ) (N : ℕ) (I : TIdx mu) (j : Fin N) :
    (ql_E lo N (qs_ext mu I) j).card = colH mu (lo + 1 + (j : ℕ)) := qs_ext_card hmu I _

lemma sum_indices_eq_sum_columns {M : Type*} [AddCommMonoid M] {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ}
    (h1 : lo ≤ mu (lastIdx n)) (h2 : mu 0 ≤ lo + N) (φ : (Fin N → Finset (Fin n)) → M)
    (hφ : ∀ f, (∃ j : Fin N, (f j).card ≠ colH mu (lo + 1 + (j : ℕ))) → φ f = 0) :
    ∑ I : TIdx mu, φ (ql_E lo N (qs_ext mu I)) = ∑ f, φ f := by
  refine Fintype.sum_of_injective (fun I : TIdx mu => ql_E lo N (qs_ext mu I)) ?_ _ _ ?_ (fun _ => rfl)
  · intro I I' h
    funext c
    apply Subtype.ext
    rw [← qs_ext_mem, ← qs_ext_mem]
    have hc := c.2
    simp only [TCols, mem_Ioc] at hc
    have := congrFun h ⟨(c.1 - lo - 1).toNat, by omega⟩
    have e : lo + 1 + ((c.1 - lo - 1).toNat : ℤ) = c.1 := by omega
    simp only [ql_E, e] at this
    exact this
  · intro f hf
    apply hφ
    by_contra hc
    push Not at hc
    exact hf ⟨qs_res mu (ql_fill lo N f) (ql_fill_card hmu h1 h2 f hc), by
      simp only [qs_ext_res hmu, ql_E_fill]⟩

lemma ql_TMat {mu : Fin n → ℤ} (hmu : Dominant mu) {lo : ℤ} {N : ℕ} (h1 : lo ≤ mu (lastIdx n))
    (h2 : mu 0 ≤ lo + N) (J I : TIdx mu) :
    TMat mu J I = ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) *
      ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext mu J) j) (ql_E lo N (qs_ext mu I) j) := by
  rw [qs_TMat_eq hmu lo (lo + N) h1 h2, qs_TM, ql_prod_Ioc]; rfl

lemma ql_mem_can {mu : Fin n → ℤ} (hmu : Dominant mu) (c : ℤ) (a : Fin n) :
    a ∈ qs_ext mu (canT mu) c ↔ c ≤ mu a := by
  rw [qs_ext_can hmu, ← qb_lt_colH_iff hmu]; simp [qs_ini]

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end

section
noncomputable section

open Finset

namespace Formalism.InvariantFactorPaths.ColumnFamilies

variable {n : ℕ}

def ql_be (b : ℕ) (L : LamIdx n b) : Fin n → ℤ := ∑ x ∈ L.1, Pi.single x (1 : ℤ)

lemma ql_be_apply (b : ℕ) (L : LamIdx n b) (a : Fin n) : ql_be b L a = if a ∈ L.1 then 1 else 0 := by
  simp [ql_be, Finset.sum_apply, Pi.single_apply]

lemma ql_be_inj (b : ℕ) : Function.Injective (ql_be (n := n) b) := by
  intro L L' h
  apply Subtype.ext
  ext a
  have := congrFun h a
  rw [ql_be_apply, ql_be_apply] at this
  by_cases h1 : a ∈ L.1 <;> by_cases h2 : a ∈ L'.1 <;> simp_all

lemma ql_torus (b : ℕ) (k l : LamIdx n b) :
    evGL (torusPt n) (LamMat n b k l) = if k = l then AddMonoidAlgebra.single (ql_be b k) 1 else 0 := by
  rw [LamMat, qb_evGL_minorC]
  change Matrix.det (Matrix.of fun a b => Matrix.diagonal _ _ _) = _
  rw [qb_minor_diagonal, qb_prod_single]
  simp only [Subtype.ext_iff, ql_be]

variable [NeZero n]

def ql_ps (b : ℕ) (mu nu : Fin n → ℤ) : Matrix (TIdx mu × LamIdx n b) (TIdx nu) ℤ :=
  fun y I => ql_P ℤ (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext mu y.1)) y.2.1
    (ql_E (mu (lastIdx n)) (nu 0 - mu (lastIdx n)).toNat (qs_ext nu I))

lemma ql_mem_strVert {mu nu : Fin n → ℤ} {b : ℕ} (h : nu ∈ strVert mu b) :
    (∀ a, mu a ≤ nu a ∧ nu a ≤ mu a + 1) ∧ Dominant nu ∧ ∑ a, (nu a - mu a) = (b : ℤ) := by
  simpa only [strVert, mem_filter, Fintype.mem_piFinset, mem_Icc] using h

theorem ql_core (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (hnu : Dominant nu) {lo : ℤ} {N : ℕ}
    (m1 : lo ≤ mu (lastIdx n)) (m2 : mu 0 ≤ lo + N) (n1 : lo ≤ nu (lastIdx n)) (n2 : nu 0 ≤ lo + N)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 (ql_E lo N (qs_ext nu I)) : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_P ℤ (ql_E lo N (qs_ext mu K)) L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) *
        TMat nu I' I := by
  set d : GLCoord ℤ n := ((detU n ^ lo : (GLCoord ℤ n)ˣ) : GLCoord ℤ n) with hd
  set k := ql_E lo N (qs_ext mu K) with hk
  set i := ql_E lo N (qs_ext nu I) with hi
  calc ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) *
        ((ql_P ℤ (ql_E lo N (qs_ext mu y.1)) y.2.1 i : ℤ) : GLCoord ℤ n)
      = ∑ K' : TIdx mu, ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (ql_E lo N (qs_ext mu K') j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) (ql_E lo N (qs_ext mu K')) L'.1 i) := by
        rw [Fintype.sum_prod_type]
        refine sum_congr rfl fun K' _ => sum_congr rfl fun L' _ => ?_
        rw [ql_TMat hmu m1 m2, LamMat, qs_minorC_eq, ql_P_cast]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i) := by
        refine sum_indices_eq_sum_columns hmu m1 m2 (fun k' => ∑ L' : LamIdx n b, d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L'.1 * ql_P (GLCoord ℤ n) k' L'.1 i)) ?_
        rintro f ⟨j, hj⟩
        refine sum_eq_zero fun L' _ => ?_
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hk, ql_E_card hmu]; exact hj.symm))]; ring
    _ = ∑ k' : Fin N → Finset (Fin n), ∑ L' : Finset (Fin n), d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i) := by
        refine sum_congr rfl fun k' _ => ql_sum_L (b := b) (fun L' => d * ((∏ j, qs_mn (qs_gC n) (k j) (k' j)) *
          qs_mn (qs_gC n) L.1 L' * ql_P (GLCoord ℤ n) k' L' i)) ?_
        intro L' hL'
        show d * (_ * qs_mn (qs_gC n) L.1 L' * _) = 0
        rw [qs_mn_ne _ (by rw [L.2]; exact hL'.symm)]; ring
    _ = ∑ i' : Fin N → Finset (Fin n), d * (ql_P (GLCoord ℤ n) k L.1 i' * ∏ j, qs_mn (qs_gC n) (i' j) (i j)) := by
        rw [← mul_sum, ← ql_P_equiv]; simp only [mul_sum]
    _ = ∑ I' : TIdx nu, d * (ql_P (GLCoord ℤ n) k L.1 (ql_E lo N (qs_ext nu I')) *
          ∏ j, qs_mn (qs_gC n) (ql_E lo N (qs_ext nu I') j) (i j)) := by
        symm
        refine sum_indices_eq_sum_columns hnu n1 n2 (fun i' => d * (ql_P (GLCoord ℤ n) k L.1 i' *
          ∏ j, qs_mn (qs_gC n) (i' j) (i j))) ?_
        rintro f ⟨j, hj⟩
        show d * (_ * ∏ j, qs_mn (qs_gC n) (f j) (i j)) = 0
        rw [prod_eq_zero (mem_univ j) (qs_mn_ne _ (by rw [hi, ql_E_card hnu]; exact hj))]; ring
    _ = ∑ I' : TIdx nu, ((ql_P ℤ k L.1 (ql_E lo N (qs_ext nu I')) : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
        refine sum_congr rfl fun I' _ => ?_
        rw [ql_TMat hnu n1 n2, ql_P_cast]; ring

lemma ql_range {mu nu : Fin n → ℤ} {b : ℕ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    mu (lastIdx n) + ((nu 0 - mu (lastIdx n)).toNat : ℕ) = nu 0 := by
  have h0 : mu (lastIdx n) ≤ mu 0 := hmu (Fin.zero_le _)
  have := ((ql_mem_strVert h).1 0).1
  omega

theorem ql_ps_equiv (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b)
    (K : TIdx mu) (L : LamIdx n b) (I : TIdx nu) :
    ∑ y : TIdx mu × LamIdx n b, (TMat mu K y.1 * LamMat n b L y.2) * ((ql_ps b mu nu y I : ℤ) : GLCoord ℤ n) =
      ∑ I' : TIdx nu, ((ql_ps b mu nu (K, L) I' : ℤ) : GLCoord ℤ n) * TMat nu I' I := by
  obtain ⟨hb, hnu, -⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  exact ql_core b hmu hnu le_rfl (by rw [hN]; exact (hb 0).1) (hb _).1 hN.ge K L I

theorem ql_lead (b : ℕ) {mu nu : Fin n → ℤ} (hmu : Dominant mu) (h : nu ∈ strVert mu b) :
    ∃ k0 : LamIdx n b, ql_be b k0 = nu - mu ∧
      (ql_ps b mu nu (canT mu, k0) (canT nu) = 1 ∨ ql_ps b mu nu (canT mu, k0) (canT nu) = -1) := by
  obtain ⟨hb, hnu, hs⟩ := ql_mem_strVert h
  have hN := ql_range hmu h
  set lo := mu (lastIdx n) with hlo
  set N := (nu 0 - lo).toNat with hNdef
  set k := ql_E lo N (qs_ext mu (canT mu)) with hk
  set i := ql_E lo N (qs_ext nu (canT nu)) with hi
  have hmk : ∀ (j : Fin N) a, a ∈ k j ↔ lo + 1 + (j : ℕ) ≤ mu a := fun j a => ql_mem_can hmu _ a
  have hmi : ∀ (j : Fin N) a, a ∈ i j ↔ lo + 1 + (j : ℕ) ≤ nu a := fun j a => ql_mem_can hnu _ a
  have hU : ∀ a, a ∈ ql_U N (fun j => i j \ k j) ↔ mu a < nu a := by
    intro a
    rw [ql_mem_U]
    simp only [mem_sdiff, hmk, hmi]
    constructor
    · rintro ⟨j, h1, h2⟩; omega
    · intro hlt
      have h1 : lo ≤ mu a := hmu (qb_le_lastIdx a)
      have h2 : nu a ≤ nu 0 := hnu (Fin.zero_le a)
      refine ⟨⟨(nu a - lo - 1).toNat, by omega⟩, ?_, ?_⟩
      · show lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ nu a; omega
      · show ¬ lo + 1 + ((nu a - lo - 1).toNat : ℤ) ≤ mu a; omega
  have hind : ∀ a, (if a ∈ ql_U N (fun j => i j \ k j) then (1 : ℤ) else 0) = nu a - mu a := by
    intro a
    have := hb a
    split_ifs with h1
    · rw [hU] at h1; omega
    · rw [hU] at h1; omega
  have hcard : (ql_U N (fun j => i j \ k j)).card = b := by
    have : ((ql_U N (fun j => i j \ k j)).card : ℤ) = b := by
      rw [← hs, ← sum_congr rfl fun a _ => hind a, Finset.sum_boole, filter_mem_eq_inter, univ_inter]
    exact_mod_cast this
  refine ⟨⟨_, hcard⟩, ?_, ?_⟩
  · funext a
    rw [ql_be_apply, Pi.sub_apply]
    exact hind a
  · refine Int.isUnit_iff.1 (ql_P_unit k i ?_ ?_)
    · intro j a ha
      rw [hmk] at ha; rw [hmi]; exact ha.trans (hb a).1
    · intro j j' hjj
      rw [Finset.disjoint_left]
      intro a h1 h2
      simp only [mem_sdiff, hmk, hmi] at h1 h2
      have := hb a
      apply hjj; ext; omega

theorem lamStrip_of (hc : CntLam) : LamStrip := by
  intro n _ b
  refine ⟨ql_be b, ql_ps b, ql_be_inj b, ql_torus b, fun mu _ nu h => (ql_mem_strVert h).2.1, ?_,
    fun mu hmu nu h => ql_lead b hmu h, fun mu hmu => hc n mu b hmu⟩
  intro mu hmu nu h
  ext ⟨K, L⟩ I
  exact ql_ps_equiv b hmu h K L I

end Formalism.InvariantFactorPaths.ColumnFamilies
end
end
