import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InertDensity.AnisoPeelAlt

section
open Finset

noncomputable section

namespace DensInertW

theorem Fr_zero_zero (q d : ℕ) : Fr q d 0 0 = 1 := by
  rw [Fr]

theorem Fr_succ (q d r c : ℕ) : Fr q d (r + 1) c = valN q d * Fr q (d - 1) r c := by
  rw [Fr]

theorem Fr_zero_succ (q d c : ℕ) :
    Fr q d 0 (c + 1) = (valZ q d - 1) * (q : ℤ) ^ (2 * c) * Fr q (d - 2) 0 c := by
  rw [Fr]

theorem top_cnt_fin_zero {L : Type} [Field L] {n : ℕ} (q : ℕ) (M : Matrix (Fin n) (Fin n) L)
    (W : Submodule L (Fin n → L)) (B : Matrix (Fin 0) (Fin 0) L) : cntT q M W B = 1 := by
  unfold cntT
  have h : {X : Fin 0 → Fin n → L | (∀ i, X i ∈ W) ∧ LinearIndependent L X ∧
      ∀ i j, hf q M (X i) (X j) = B i j} = Set.univ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact ⟨fun i => i.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  rw [h, Set.ncard_univ]
  simp

theorem top_diag_count (hA : AnisoPeel) (hI : IsoPeel) (K L : Type) [Field K] [Fintype K]
    [Field L] [Fintype L] [Algebra K L] (h2 : Module.finrank K L = 2) (n : ℕ)
    (M : Matrix (Fin n) (Fin n) L) (hM : IsHerm (Fintype.card K) M) :
    ∀ (m : ℕ) (w : Fin m → L) (r : ℕ), r ≤ m → (∀ i, w i ≠ 0 ↔ i.val < r) →
      (∀ i, w i ^ Fintype.card K = w i) →
      ∀ W : Submodule L (Fin n → L), NonDeg (Fintype.card K) M W →
        (cntT (Fintype.card K) M W (Matrix.diagonal w) : ℤ) =
          Fr (Fintype.card K) (Module.finrank L W) r (m - r) := by
  intro m
  induction m with
  | zero =>
    intro w r hr _ _ W _
    obtain rfl : r = 0 := by omega
    rw [top_cnt_fin_zero, Fr_zero_zero]
    rfl
  | succ c ih =>
    intro w r hr hw hwq W hW
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · subst h0
      have hw0 : w = 0 := by
        funext i
        by_contra h
        have := (hw i).mp h
        omega
      have hdiag : Matrix.diagonal w = (0 : Matrix (Fin (c + 1)) (Fin (c + 1)) L) := by
        rw [hw0]; exact Matrix.diagonal_zero
      rw [hdiag]
      have hk := hI K L h2 n M W hM hW c (Fr (Fintype.card K) (Module.finrank L W - 2) 0 c)
        (fun W' hW' hrk => by
          have h1 := ih (fun _ => 0) 0 (Nat.zero_le _) (fun i => by simp)
            (fun i => by simp [zero_pow Fintype.card_ne_zero]) W' hW'
          rw [Matrix.diagonal_zero] at h1
          rw [h1, show Module.finrank L W' = Module.finrank L W - 2 by omega, Nat.sub_zero])
      rw [hk, Nat.sub_zero, Fr_zero_succ]
    · obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
      have hw0 : w 0 ≠ 0 := (hw 0).mpr (by simp)
      have hcons : Matrix.diagonal w =
          Matrix.diagonal (Fin.cons (w 0) (Fin.tail w) : Fin (c + 1) → L) := by
        rw [Fin.cons_self_tail]
      rw [hcons]
      have hk := hA K L h2 n M W hM hW c (w 0) (Fin.tail w)
        (Fr (Fintype.card K) (Module.finrank L W - 1) r' (c - r')) (hwq 0) hw0
        (fun W' hW' hrk => by
          have h1 := ih (Fin.tail w) r' (by omega)
            (fun i => by simp only [Fin.tail]; rw [hw i.succ]; simp [Fin.val_succ])
            (fun i => hwq i.succ) W' hW'
          rw [h1, show Module.finrank L W' = Module.finrank L W - 1 by omega])
      rw [hk, show c + 1 - (r' + 1) = c - r' by omega, Fr_succ]

theorem top_nondeg_top {L : Type} [Field L] {n : ℕ} (q : ℕ) (hq : 0 < q)
    (M : Matrix (Fin n) (Fin n) L) (hdet : IsUnit M.det) : NonDeg q M ⊤ := by
  intro w _ hw
  have h0 : Matrix.vecMul w M = 0 := by
    funext l0
    have h := hw (Pi.single l0 1) Submodule.mem_top
    simp only [hf, Pi.single_apply, ite_pow, one_pow, zero_pow hq.ne', mul_ite, mul_one,
      mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
    simpa [Matrix.vecMul, dotProduct] using h
  calc w = Matrix.vecMul w (M * M⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
    _ = Matrix.vecMul (Matrix.vecMul w M) M⁻¹ := by rw [Matrix.vecMul_vecMul]
    _ = 0 := by rw [h0, Matrix.zero_vecMul]

theorem top_rank (K L : Type) [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L]
    (m : ℕ) (B P : Matrix (Fin m) (Fin m) L) (hP : IsUnit P.det) :
    (P * B * (P.map (fun y => y ^ Fintype.card K)).transpose).rank = B.rank := by
  have hF : P.map (fun y => y ^ Fintype.card K) =
      P.map ((FiniteField.frobeniusAlgHom K L : L →ₐ[K] L) : L →+* L) := by
    ext i j
    simp [FiniteField.frobeniusAlgHom_apply]
  have hu : IsUnit (P.map (fun y => y ^ Fintype.card K)).transpose.det := by
    rw [Matrix.det_transpose, hF, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact hP.map _
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ hu, Matrix.rank_mul_eq_right_of_isUnit_det _ _ hP]

theorem densExactInert_of (hD : Diag) (hC : Congr) (hA : AnisoPeel) (hI : IsoPeel)
    (hR : Arith) : Formalism.L2.SG.DensExact.DensExactInert := by
  classical
  intro K L _ _ _ _ _ h2 n m Ph Gm hPh hPhH hGm
  obtain ⟨P, hP, w, r, hrm, hdiag, hw, hwq⟩ := hD K L h2 m Gm hGm
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  have hcnt : Formalism.L2.SG.DensExact.countInert K L n m Ph Gm = cntT (Fintype.card K) Ph ⊤ Gm := by
    unfold Formalism.L2.SG.DensExact.countInert cntT
    congr 1
    ext X
    simp [hf]
  have hcong := hC K L h2 n Ph ⊤ m Gm P hP
  rw [hdiag] at hcong
  have hrank : Gm.rank = r := by
    rw [← top_rank K L m Gm P hP, hdiag, Matrix.rank_diagonal,
      Fintype.card_congr (Equiv.subtypeEquivRight hw)]
    have e : {i : Fin m // i.val < r} ≃ Fin r :=
      { toFun := fun i => ⟨i.1.val, i.2⟩
        invFun := fun j => ⟨⟨j.val, by omega⟩, j.2⟩
        left_inv := fun i => rfl
        right_inv := fun j => rfl }
    rw [Fintype.card_congr e, Fintype.card_fin]
  have hcount := top_diag_count hA hI K L h2 n Ph hPhH m w r hrm hw hwq ⊤
    (top_nondeg_top _ (by omega) Ph hPh)
  rw [finrank_top, Module.finrank_fin_fun] at hcount
  rw [hcnt, ← hcong, hrank, ← hR (Fintype.card K) n m r hq hrm, ← hcount]
  norm_cast

end DensInertW
end
end

section
open Finset

noncomputable section

namespace DensInertW

def arF (q i : ℕ) : ℝ := 1 - (-1 : ℝ) ^ i * ((q : ℝ) ^ i)⁻¹



theorem ar_valN (q n : ℕ) (hq : 0 < q) :
    ((valN q (n + 1) : ℤ) : ℝ) = (q : ℝ) ^ (2 * n + 1) * arF q (n + 1) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have hb : (q : ℝ) ^ (n + 1) * ((q : ℝ) ^ (n + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  simp only [valN, arF, Nat.add_sub_cancel]
  push_cast
  linear_combination ((-1 : ℝ) ^ (n + 1) * (q : ℝ) ^ n) * hb

theorem ar_valN_zero (q : ℕ) : valN q 0 = 0 := by
  simp [valN]

theorem ar_valZ (q N : ℕ) (hq : 0 < q) :
    ((valZ q (N + 2) : ℤ) : ℝ) - 1 = (q : ℝ) ^ (2 * N + 3) * arF q (N + 2) * arF q (N + 1) := by
  have hq' : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
  have ha : (q : ℝ) ^ (N + 2) * ((q : ℝ) ^ (N + 2))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  have hb : (q : ℝ) ^ (N + 1) * ((q : ℝ) ^ (N + 1))⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hq')
  have hs : (-1 : ℝ) ^ N * (-1 : ℝ) ^ N = 1 := by rw [← mul_pow]; norm_num
  simp only [valZ, arF]
  rw [show 2 * (N + 2) - 1 = 2 * N + 3 by omega, show N + 2 - 1 = N + 1 by omega]
  push_cast
  linear_combination hs + (-((-1 : ℝ) ^ N) * (q : ℝ) ^ (N + 2) + ((-1 : ℝ) ^ N) ^ 2) * hb +
    ((-1 : ℝ) ^ N * (q : ℝ) ^ (N + 1) + ((-1 : ℝ) ^ N) ^ 2 +
      ((-1 : ℝ) ^ N) ^ 2 * ((q : ℝ) ^ (N + 1) * ((q : ℝ) ^ (N + 1))⁻¹ - 1)) * ha

theorem ar_valZ_zero (q : ℕ) : valZ q 0 - 1 = 0 := by
  simp [valZ]

theorem ar_valZ_one (q : ℕ) : valZ q 1 - 1 = 0 := by
  simp [valZ]

theorem densityProduct_succ_succ_add (q n r c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) (n + 1) (r + 1 + c) c =
      arF q (n + 1) * Formalism.L2.SG.DensExact.densProd q (-1) n (r + c) c := by
  unfold Formalism.L2.SG.DensExact.densProd
  rw [show n + 1 + 1 - (r + 1 + c + c) = n + 1 - (r + c + c) by omega,
    Finset.prod_Icc_succ_top (by omega), mul_comm]
  rfl

theorem densityProduct_add_two_succ_succ (q N c : ℕ) :
    Formalism.L2.SG.DensExact.densProd q (-1) (N + 2) (c + 1) (c + 1) =
      arF q (N + 2) * arF q (N + 1) * Formalism.L2.SG.DensExact.densProd q (-1) N c c := by
  unfold Formalism.L2.SG.DensExact.densProd arF
  rw [show N + 2 + 1 - (c + 1 + (c + 1)) = N + 1 - (c + c) by omega, show N + 2 = N + 1 + 1 from rfl,
    Finset.prod_Icc_succ_top (by omega), Finset.prod_Icc_succ_top (by omega)]
  ring

theorem ar_zero_prod (q n m c : ℕ) (h : n + 1 ≤ m + c) :
    Formalism.L2.SG.DensExact.densProd q (-1) n m c = 0 := by
  unfold Formalism.L2.SG.DensExact.densProd
  exact Finset.prod_eq_zero (i := 0) (Finset.mem_Icc.mpr ⟨by omega, Nat.zero_le _⟩) (by simp)

theorem frameCount_zero_mul_pow (q : ℕ) (hq : 0 < q) : ∀ c n : ℕ,
    ((Fr q n 0 c : ℤ) : ℝ) * (q : ℝ) ^ (c ^ 2) =
      (q : ℝ) ^ (2 * n * c) * Formalism.L2.SG.DensExact.densProd q (-1) n c c := by
  intro c
  induction c with
  | zero =>
    intro n
    have h0 : Fr q n 0 0 = 1 := by simp [Fr]
    unfold Formalism.L2.SG.DensExact.densProd
    rw [h0, Finset.Icc_eq_empty (by omega), Finset.prod_empty]
    simp
  | succ c ih =>
    intro n
    match n with
    | 0 =>
      rw [ar_zero_prod q 0 (c + 1) (c + 1) (by omega)]
      have h0 : Fr q 0 0 (c + 1) = 0 := by simp only [Fr, ar_valZ_zero, zero_mul]
      rw [h0]
      simp
    | 1 =>
      rw [ar_zero_prod q 1 (c + 1) (c + 1) (by omega)]
      have h0 : Fr q 1 0 (c + 1) = 0 := by simp only [Fr, ar_valZ_one, zero_mul]
      rw [h0]
      simp
    | N + 2 =>
      have hF : ((Fr q (N + 2) 0 (c + 1) : ℤ) : ℝ) =
          (((valZ q (N + 2) : ℤ) : ℝ) - 1) * (q : ℝ) ^ (2 * c) * ((Fr q N 0 c : ℤ) : ℝ) := by
        simp [Fr]
      rw [hF, ar_valZ q N hq, densityProduct_add_two_succ_succ]
      have e2 := ih N
      calc _ = (q : ℝ) ^ (2 * N + 4 * c + 4) * arF q (N + 2) * arF q (N + 1) *
            (((Fr q N 0 c : ℤ) : ℝ) * (q : ℝ) ^ (c ^ 2)) := by ring
        _ = _ := by rw [e2]; ring

theorem ar_main (q : ℕ) (hq : 0 < q) : ∀ r c n : ℕ,
    ((Fr q n r c : ℤ) : ℝ) * (q : ℝ) ^ ((r + c) ^ 2) =
      (q : ℝ) ^ (2 * n * (r + c)) * Formalism.L2.SG.DensExact.densProd q (-1) n (r + c) c := by
  intro r
  induction r with
  | zero =>
    intro c n
    simpa only [zero_add] using frameCount_zero_mul_pow q hq c n
  | succ r ih =>
    intro c n
    match n with
    | 0 =>
      rw [ar_zero_prod q 0 (r + 1 + c) c (by omega)]
      have h0 : Fr q 0 (r + 1) c = 0 := by simp only [Fr, ar_valN_zero, zero_mul]
      rw [h0]
      simp
    | N + 1 =>
      have hF : ((Fr q (N + 1) (r + 1) c : ℤ) : ℝ) = ((valN q (N + 1) : ℤ) : ℝ) * ((Fr q N r c : ℤ) : ℝ) := by
        simp [Fr]
      rw [hF, ar_valN q N hq, densityProduct_succ_succ_add]
      have e2 := ih c N
      calc _ = (q : ℝ) ^ (2 * N + 2 * r + 2 * c + 2) * arF q (N + 1) *
            (((Fr q N r c : ℤ) : ℝ) * (q : ℝ) ^ ((r + c) ^ 2)) := by ring
        _ = _ := by rw [e2]; ring

theorem quadraticDifferenceArith : Arith := by
  intro q n m r hq hrm
  have hq0 : 0 < q := by omega
  have e := ar_main q hq0 r (m - r) n
  rw [show r + (m - r) = m by omega] at e
  have hA : (q : ℝ) ^ (2 * n * m) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  rw [div_div_eq_mul_div, e, mul_div_cancel_left₀ _ hA]

end DensInertW
end
end
