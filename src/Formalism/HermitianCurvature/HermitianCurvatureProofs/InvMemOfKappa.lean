import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumPairAtStarMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.AdmissibleRecOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameOfAdmissibleWord
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SignedCoordinateEqSignSmul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MeasurableOfContinuousOnZero
import Formalism.HermitianCurvature.HermitianCurvatureProofs.QNFAsm

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Alg

variable {A S : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype S] [DecidableEq S] {r : ℕ}

def entSub (𝒜 : StarSubalgebra ℂ A) : Subalgebra ℂ (SlopeTestRemainingChoices S A) where
  carrier := {M | ∀ i j, M i j ∈ 𝒜}
  mul_mem' {M N} hM hN i j := by
    rw [Matrix.mul_apply]
    exact 𝒜.sum_mem fun k _ => 𝒜.mul_mem (hM i k) (hN k j)
  add_mem' {M N} hM hN i j := 𝒜.add_mem (hM i j) (hN i j)
  algebraMap_mem' a i j := by
    rw [Matrix.algebraMap_matrix_apply]
    split_ifs
    · exact 𝒜.algebraMap_mem a
    · exact 𝒜.zero_mem

variable {𝒜 : StarSubalgebra ℂ A}

theorem mem_entSub {M : SlopeTestRemainingChoices S A} : M ∈ entSub 𝒜 ↔ ∀ i j, M i j ∈ 𝒜 := by
  exact Iff.rfl

theorem star_mem_entSub {M : SlopeTestRemainingChoices S A} (h : M ∈ entSub 𝒜) : star M ∈ entSub 𝒜 := by
  rw [mem_entSub] at h ⊢
  intro i j
  rw [Matrix.star_apply]
  exact star_mem (h j i)

theorem io_mem {x : A} (h : x ∈ 𝒜) : (io x : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  rw [mem_entSub]
  intro i j
  simp only [io, Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact h
  · exact 𝒜.zero_mem

theorem eU_mem (a : S) (i j : Fin 2) : (eU a i j : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  rw [mem_entSub]
  intro x y
  simp only [eU, Matrix.of_apply]
  split_ifs
  · exact 𝒜.one_mem
  · exact 𝒜.zero_mem

def E2 (𝒜 : StarSubalgebra ℂ A) (M : M2 (SlopeTestRemainingChoices S A)) : Prop := ∀ i j, M i j ∈ entSub 𝒜

theorem entries_mem_mul {M N : M2 (SlopeTestRemainingChoices S A)} (hM : E2 𝒜 M) (hN : E2 𝒜 N) : E2 𝒜 (M * N) := by
  intro i j
  rw [Matrix.mul_apply]
  exact (entSub 𝒜).sum_mem fun k _ => (entSub 𝒜).mul_mem (hM i k) (hN k j)

theorem entries_mem_of_four {a b c d : SlopeTestRemainingChoices S A} (ha : a ∈ entSub 𝒜) (hb : b ∈ entSub 𝒜) (hc : c ∈ entSub 𝒜) (hd : d ∈ entSub 𝒜) :
    E2 𝒜 !![a, b; c, d] := by
  intro i j
  fin_cases i <;> fin_cases j <;> simp [ha, hb, hc, hd]

theorem entries_mem_one : E2 𝒜 (1 : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  rw [Matrix.one_apply]
  split_ifs
  · exact (entSub 𝒜).one_mem
  · exact (entSub 𝒜).zero_mem

theorem ins_mem (a : S) {M : M2 (SlopeTestRemainingChoices S A)} (hM : E2 𝒜 M) : ins a M ∈ entSub 𝒜 := by
  unfold ins
  exact (entSub 𝒜).sum_mem fun i _ => (entSub 𝒜).sum_mem fun j _ =>
    (entSub 𝒜).mul_mem (eU_mem a i j) (hM i j)

theorem eval_two_smul (a : ℂ) {M : M2 (SlopeTestRemainingChoices S A)} (hM : E2 𝒜 M) : E2 𝒜 (a • M) := by
  intro i j
  rw [Matrix.smul_apply]
  exact (entSub 𝒜).smul_mem (hM i j) a

theorem eval_two_sub {M N : M2 (SlopeTestRemainingChoices S A)} (hM : E2 𝒜 M) (hN : E2 𝒜 N) : E2 𝒜 (M - N) := by
  intro i j
  rw [Matrix.sub_apply]
  exact sub_mem (hM i j) (hN i j)

theorem permutation_entries_mem (a : S) : E2 𝒜 (P0 a : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  exact eU_mem a j i

theorem permutation_left_entries_mem (a : S) : E2 𝒜 (Q0 a : M2 (SlopeTestRemainingChoices S A)) := by
  intro i j
  exact eU_mem a i j

theorem reflection_entries_mem (a : S) (D : ℂ) : E2 𝒜 (Rh0 (K := ℂ) a D : M2 (SlopeTestRemainingChoices S A)) := by
  unfold Rh0
  exact eval_two_smul _ (eval_two_sub (eval_two_smul _ entries_mem_one) (permutation_entries_mem a))

theorem reflection_transpose_entries_mem (b : S) (D : ℂ) : E2 𝒜 (Rht0 (K := ℂ) b D : M2 (SlopeTestRemainingChoices S A)) := by
  unfold Rht0
  exact eval_two_smul _ (eval_two_sub (eval_two_smul _ entries_mem_one) (permutation_left_entries_mem b))

def Gens (𝒜 : StarSubalgebra ℂ A) (L : LevelData A r) (st : Start A) : Prop :=
  (∀ g ∈ zfns L, g ∈ 𝒜) ∧ (∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ 𝒜) ∧
    (∀ Y : ℂ, star Y = Y → st.x Y ∈ 𝒜) ∧ (∀ Y ∈ st.inv, star Y = Y → st.xi Y ∈ 𝒜)

def Cl (𝒜 : StarSubalgebra ℂ A) (st : Start A) (f : FrameData S A) : Prop :=
  f.F ∈ entSub 𝒜 ∧ f.Fi ∈ entSub 𝒜 ∧ f.c ∈ entSub 𝒜 ∧ f.ci ∈ entSub 𝒜 ∧
    (∀ Y : ℂ, star Y = Y → E2 𝒜 (f.TT Y)) ∧ (∀ Y : ℂ, star Y = Y → f.x Y ∈ entSub 𝒜) ∧
    (∀ Y ∈ st.inv, star Y = Y → f.xi Y ∈ entSub 𝒜)

theorem io_one_mul (L : LevelData A r) : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := by
  unfold io
  rw [← map_mul, L.GGi_GG, map_one]

theorem l_eq (L : LevelData A r) (f : FrameData S A) (hf : IsFrame L f) {Y : ℂ} (h0 : Y ∈ f.inv)
    (h1 : Y + 1 ∈ f.inv) : f.l L Y = f.xi Y * io L.GGi * (f.F * f.TT Y 1 0 * f.Fi) := by
  rw [hf.frame_l Y h0 h1, mul_assoc _ f.F f.Fi, hf.F_Fi, mul_one]
  have e1 : (io L.GGi : SlopeTestRemainingChoices S A) * io L.GG = 1 := io_one_mul L
  have e2 := (hf.x_xi Y h0).2
  calc f.l L Y = f.xi Y * f.x Y * f.l L Y := by rw [e2, one_mul]
    _ = f.xi Y * ((io L.GGi : SlopeTestRemainingChoices S A) * io L.GG) * f.x Y * f.l L Y := by rw [e1, mul_one]
    _ = f.xi Y * io L.GGi * (io L.GG * f.x Y * f.l L Y) := by simp only [mul_assoc]

theorem zfn_mem (L : LevelData A r) (hz : ∀ g ∈ zfns L, g ∈ 𝒜) :
    (io L.ζ : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 ∧ (io L.ζi : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 ∧ (io L.ζb : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 ∧
      (io L.ζbi : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 ∧ (io L.GG : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 ∧ (io L.GGi : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  exact ⟨io_mem (hz _ (by simp [zfns])), io_mem (hz _ (by simp [zfns])), io_mem (hz _ (by simp [zfns])), io_mem (hz _ (by simp [zfns])), io_mem (hz _ (by simp [zfns])), io_mem (hz _ (by simp [zfns]))⟩

theorem l_mem (L : LevelData A r) (st : Start A) (f : FrameData S A) (hf : IsFrame L f) (hC : Cl 𝒜 st f)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) {Y : ℂ} (hY : star Y = Y) (hYs : Y ∈ st.inv) (h0 : Y ∈ f.inv)
    (h1 : Y + 1 ∈ f.inv) : f.l L Y ∈ entSub 𝒜 := by
  rw [l_eq L f hf h0 h1]
  have hT := hC.2.2.2.2.1 Y hY 1 0
  have hG := (zfn_mem (S := S) (𝒜 := 𝒜) L hz).2.2.2.2.2
  exact (entSub 𝒜).mul_mem ((entSub 𝒜).mul_mem (hC.2.2.2.2.2.2 Y hYs hY) hG)
    ((entSub 𝒜).mul_mem ((entSub 𝒜).mul_mem hC.1 hT) hC.2.1)

theorem wt_mem (L : LevelData A r) (hz : ∀ g ∈ zfns L, g ∈ 𝒜) : (wt L : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  exact io_mem (𝒜.mul_mem (𝒜.mul_mem (hz _ (by simp [zfns])) (hz _ (by simp [zfns]))) (hz _ (by simp [zfns])))

theorem wti_mem (L : LevelData A r) (hz : ∀ g ∈ zfns L, g ∈ 𝒜) : (wti L : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := by
  exact io_mem (𝒜.mul_mem (𝒜.mul_mem (hz _ (by simp [zfns])) (hz _ (by simp [zfns]))) (hz _ (by simp [zfns])))

theorem d_mem (L : LevelData A r) (st : Start A) (f : FrameData S A) (hC : Cl 𝒜 st f)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) : f.d L ∈ entSub 𝒜 := by
  exact (entSub 𝒜).mul_mem (pow_mem (wt_mem L hz) _) hC.2.2.1

theorem di_mem (L : LevelData A r) (st : Start A) (f : FrameData S A) (hC : Cl 𝒜 st f)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) : f.di L ∈ entSub 𝒜 := by
  exact (entSub 𝒜).mul_mem hC.2.2.2.1 (pow_mem (wti_mem L hz) _)

theorem scal_mem (a : ℂ) : (a • (1 : SlopeTestRemainingChoices S A)) ∈ entSub 𝒜 := by
  exact (entSub 𝒜).smul_mem (entSub 𝒜).one_mem a

theorem cl_start (L : LevelData A r) (st : Start A) (hg : Gens 𝒜 L st) : Cl 𝒜 st (st.frame : FrameData S A) := by
  refine ⟨(entSub 𝒜).one_mem, (entSub 𝒜).one_mem, (entSub 𝒜).one_mem, (entSub 𝒜).one_mem, ?_, ?_, ?_⟩
  · intro Y hY i j
    exact io_mem (hg.2.1 Y hY i j)
  · intro Y hY
    exact io_mem (hg.2.2.1 Y hY)
  · intro Y hYs hY
    exact io_mem (hg.2.2.2 Y hYs hY)

theorem cl_plus (L : LevelData A r) (st : Start A) (f : FrameData S A) (hf : IsFrame L f) (hC : Cl 𝒜 st f)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (a : S) {Ya : ℂ} (hY : star Ya = Ya) (hYs : Ya ∈ st.inv) (hY1s : Ya + 1 ∈ st.inv)
    (h0 : Ya ∈ f.inv) (h1 : Ya + 1 ∈ f.inv) : Cl 𝒜 st (f.plus L a Ya) := by
  have hl := l_mem L st f hf hC hz hY hYs h0 h1
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ := zfn_mem (S := S) (𝒜 := 𝒜) L hz
  have h0m : (0 : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := (entSub 𝒜).zero_mem
  have h1m : (1 : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := (entSub 𝒜).one_mem
  have hY1 : star (Ya + 1) = Ya + 1 := by simp [hY]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (entSub 𝒜).mul_mem (ins_mem a (entries_mem_mul (entries_mem_of_four hz2 h0m h0m hz4)
      (entries_mem_of_four h1m h0m ((entSub 𝒜).mul_mem hz5 hl) hz5))) hC.1
  · exact (entSub 𝒜).mul_mem hC.2.1 (ins_mem a (entries_mem_mul (entries_mem_of_four h1m h0m (neg_mem hl) hz6)
      (entries_mem_of_four hz1 h0m h0m hz3)))
  · exact (entSub 𝒜).mul_mem hC.2.2.1 (ins_mem a (entries_mem_of_four
      ((entSub 𝒜).smul_mem (hC.2.2.2.2.2.2 (Ya + 1) hY1s hY1) _) h0m h0m (hC.2.2.2.2.2.1 Ya hY)))
  · exact (entSub 𝒜).mul_mem hC.2.2.2.1 (ins_mem a (entries_mem_of_four
      ((entSub 𝒜).smul_mem (hC.2.2.2.2.2.1 (Ya + 1) hY1) _) h0m h0m (hC.2.2.2.2.2.2 Ya hYs hY)))
  · intro Y hYr
    exact entries_mem_mul (hC.2.2.2.2.1 Y hYr) (reflection_entries_mem a (Y - Ya))
  · intro Y hYr
    exact (entSub 𝒜).mul_mem (hC.2.2.2.2.2.1 Y hYr) (ins_mem a (entries_mem_of_four (scal_mem _) h0m h0m h1m))
  · intro Y hYs' hYr
    exact (entSub 𝒜).mul_mem (hC.2.2.2.2.2.2 Y hYs' hYr) (ins_mem a (entries_mem_of_four (scal_mem _) h0m h0m h1m))

theorem cl_minus (L : LevelData A r) (st : Start A) (f : FrameData S A) (hf : IsFrame L f) (hC : Cl 𝒜 st f)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (b : S) {Yb : ℂ} (hY : star Yb = Yb) (hYs : Yb ∈ st.inv)
    (hYm1s : Yb - 1 ∈ st.inv) (h0 : Yb ∈ f.inv) (hm1 : Yb - 1 ∈ f.inv) : Cl 𝒜 st (f.minus L b Yb) := by
  have hY1 : star (Yb - 1) = Yb - 1 := by simp [hY]
  have hl := l_mem L st f hf hC hz hY1 hYm1s hm1 (by rw [sub_add_cancel]; exact h0)
  have hm : f.m L Yb ∈ entSub 𝒜 :=
    (entSub 𝒜).mul_mem ((entSub 𝒜).mul_mem (di_mem L st f hC hz) (star_mem_entSub hl)) (d_mem L st f hC hz)
  obtain ⟨hz1, hz2, hz3, hz4, hz5, hz6⟩ := zfn_mem (S := S) (𝒜 := 𝒜) L hz
  have h0m : (0 : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := (entSub 𝒜).zero_mem
  have h1m : (1 : SlopeTestRemainingChoices S A) ∈ entSub 𝒜 := (entSub 𝒜).one_mem
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (entSub 𝒜).mul_mem (ins_mem b (entries_mem_mul (entries_mem_of_four hz4 h0m h0m hz2)
      (entries_mem_of_four h1m h0m ((entSub 𝒜).mul_mem hz5 hm) hz5))) hC.1
  · exact (entSub 𝒜).mul_mem hC.2.1 (ins_mem b (entries_mem_mul (entries_mem_of_four h1m h0m (neg_mem hm) hz6)
      (entries_mem_of_four hz3 h0m h0m hz1)))
  · exact (entSub 𝒜).mul_mem hC.2.2.1 (ins_mem b (entries_mem_of_four
      ((entSub 𝒜).smul_mem (hC.2.2.2.2.2.2 (Yb - 1) hYm1s hY1) _) h0m h0m (hC.2.2.2.2.2.1 Yb hY)))
  · exact (entSub 𝒜).mul_mem hC.2.2.2.1 (ins_mem b (entries_mem_of_four
      ((entSub 𝒜).smul_mem (hC.2.2.2.2.2.1 (Yb - 1) hY1) _) h0m h0m (hC.2.2.2.2.2.2 Yb hYs hY)))
  · intro Y hYr
    exact entries_mem_mul (reflection_transpose_entries_mem b (Yb - Y)) (hC.2.2.2.2.1 Y hYr)
  · intro Y hYr
    exact (entSub 𝒜).mul_mem (hC.2.2.2.2.2.1 Y hYr) (ins_mem b (entries_mem_of_four (scal_mem _) h0m h0m h1m))
  · intro Y hYs' hYr
    exact (entSub 𝒜).mul_mem (hC.2.2.2.2.2.2 Y hYs' hYr) (ins_mem b (entries_mem_of_four (scal_mem _) h0m h0m h1m))

theorem cl_ofWord (L : LevelData A r) (st : Start A) (hL : IsStarLevel L) (hst : IsLevelStart L st)
    (hg : Gens 𝒜 L st) (w : List (Letter ℂ S)) (hA : admitted st w) : Cl 𝒜 st (ofWord L st w) := by
  induction w with
  | nil => exact cl_start L st hg
  | cons l w ih =>
    obtain ⟨hnd, hst', hinv, hpw⟩ := hA
    rw [List.map_cons, List.nodup_cons] at hnd
    have hpw' := List.pairwise_cons.mp hpw
    have hA' : admitted st w :=
      ⟨hnd.2, fun l' hl' => hst' l' (by simp [hl']), fun l' hl' => hinv l' (by simp [hl']), hpw'.2⟩
    have hC := ih hA'
    have hf := Formalism.FourierDecayAlt.P.frame_of_admissible_word A S r L st w hL hst hA'
    obtain ⟨hp0, hp1, hpm1, -, -⟩ := hinv l (by simp)
    have hreal := hst' l (by simp)
    have hd : ∀ l' ∈ w, ∀ n : ℤ, |n| ≤ 2 → l.pt - l'.pt ≠ (n : ℂ) := hpw'.1
    have hz : ∀ g ∈ zfns L, g ∈ 𝒜 := hg.1
    have i0 : l.pt ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ hp0 fun l' hl' =>
      ⟨fun h => hd l' hl' (0) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (1) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination h)⟩
    have i1 : l.pt + 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ hp1 fun l' hl' =>
      ⟨fun h => hd l' hl' (-1) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (0) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (-2) (by norm_num) (by push_cast; linear_combination h)⟩
    have im : l.pt - 1 ∈ (ofWord L st w).inv := Formalism.FourierDecayAlt.P.Fr2.mem_inv L st w _ hpm1 fun l' hl' =>
      ⟨fun h => hd l' hl' (1) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (2) (by norm_num) (by push_cast; linear_combination h), fun h => hd l' hl' (0) (by norm_num) (by push_cast; linear_combination h)⟩
    simp only [ofWord]
    split_ifs
    · exact cl_plus L st _ hf hC hz l.intersection_update_fsHerm_neg_one hreal hp0 hp1 i0 i1
    · exact cl_minus L st _ hf hC hz l.intersection_update_fsHerm_neg_one hreal hp0 hpm1 i0 im

theorem frameAlg (L : LevelData A r) (st : Start A) (hL : IsStarLevel L) (hst : IsLevelStart L st)
    (hg : Gens 𝒜 L st) (w : List (Letter ℂ S)) (hA : admitted st w) (e e' : Ix S) :
    (ofWord L st w).F e e' ∈ 𝒜 ∧ (ofWord L st w).d L e e' ∈ 𝒜 := by
  have hC := cl_ofWord L st hL hst hg w hA
  exact ⟨hC.1 e e', d_mem L st _ hC hg.1 e e'⟩

end Alg

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_gens (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hg : Gens (adjAlg μ U hU) L st) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  exact adjTop_of_adjAlg P z z' π π' μ L st K l0 U hU hK fun w hw e e' =>
    frameAlg L st hD.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.2 hg w hw.1 e e'

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end

section
open Matrix MeasureTheory
open scoped ComplexConjugate

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerA

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Fr

section Inv

variable {A T : Type} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] [Fintype T]

theorem aeval_mem' (𝒜 : StarSubalgebra ℂ A) {x : A} (hx : x ∈ 𝒜) (p : Polynomial ℂ) :
    Polynomial.aeval x p ∈ 𝒜 := by
  refine Polynomial.induction_on p (fun a => ?_) (fun p q hp hq => ?_) (fun n a _ => ?_)
  · rw [Polynomial.aeval_C]; exact 𝒜.algebraMap_mem a
  · rw [map_add]; exact 𝒜.add_mem hp hq
  · rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    exact 𝒜.mul_mem (𝒜.algebraMap_mem a) (𝒜.pow_mem hx _)

theorem inv_mem_of_kappa (κ : (T → ℂ) →ₐ[ℂ] A) (𝒜 : StarSubalgebra ℂ A) (f : T → ℂ) (hf : κ f ∈ 𝒜) :
    κ (fun ρ => (f ρ)⁻¹) ∈ 𝒜 := by
  classical
  set N : Finset ℂ := Finset.univ.image f
  set p : Polynomial ℂ := Lagrange.interpolate N id (fun v => v⁻¹)
  have hp : ∀ ρ, p.eval (f ρ) = (f ρ)⁻¹ := by
    intro ρ
    have hmem : f ρ ∈ N := Finset.mem_image_of_mem _ (Finset.mem_univ ρ)
    have h := Lagrange.eval_interpolate_at_node (fun v : ℂ => v⁻¹) (Set.injOn_id _) hmem
    simpa only [id] using h
  have he : (fun ρ => (f ρ)⁻¹) = Polynomial.aeval f p := by
    funext ρ
    rw [← hp ρ]
    have := Polynomial.aeval_algHom_apply (Pi.evalAlgHom ℂ (fun _ : T => ℂ) ρ) f p
    rw [Pi.evalAlgHom_apply, Polynomial.coe_aeval_eq_eval] at this
    rw [this]
    rfl
  rw [he, ← Polynomial.aeval_algHom_apply]
  exact aeval_mem' 𝒜 hf p

variable {r : ℕ}

theorem x_eq_of_start (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st) (Y : ℂ) :
    st.x Y = L.GGi * st.QQ Y 1 1 := by
  rw [hst.tau, ← mul_assoc, L.GGi_GG, one_mul]

theorem gens_of (𝒜 : StarSubalgebra ℂ A) (L : LevelData A r) (st : Start A) (hst : IsLevelStart L st)
    (κ : (T → ℂ) →ₐ[ℂ] A) (x0 : T → ℂ → ℂ) (hx : ∀ Y, st.x Y = κ fun ρ => x0 ρ Y)
    (hxi : ∀ Y ∈ st.inv, st.xi Y = κ fun ρ => (x0 ρ Y)⁻¹)
    (hz : ∀ g ∈ zfns L, g ∈ 𝒜) (hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ 𝒜) : Gens 𝒜 L st := by
  have hxm : ∀ Y : ℂ, star Y = Y → st.x Y ∈ 𝒜 := fun Y hY => by
    rw [x_eq_of_start L st hst Y]
    exact 𝒜.mul_mem (hz _ (by simp [zfns])) (hQ Y hY 1 1)
  refine ⟨hz, hQ, hxm, fun Y hYs hY => ?_⟩
  rw [hxi Y hYs]
  exact inv_mem_of_kappa κ 𝒜 (fun ρ => x0 ρ Y) (by rw [← hx Y]; exact hxm Y hY)

end Inv

section Fn

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem fnVal_conj (j : Fin 6) (g : Mx k r) : conj (fnVal k r z z' (fnConj j) g) = fnVal k r z z' j g := by
  fin_cases j <;> simp [fnVal, fnConj, map_inv₀]

theorem fn_adj (X : ActualOps k r z z' π π') (μ : Measure (Mt k r)) (U : Submodule ℂ (RadSp k r z z' π π'))
    (hU : IntOn μ U) (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U) (j : Fin 6) :
    mkP (X.fn j) (X.fn (fnConj j)) ∈ adjAlg μ U hU := by
  refine ⟨fun Φ hΦ => hfn j Φ hΦ, fun Φ hΦ => hfn _ Φ hΦ, fun c _ Φ _ Ψ _ => ?_⟩
  show pairAt μ (X.fn j Φ) Ψ c = pairAt μ Φ (X.fn (fnConj j) Ψ) c
  unfold pairAt
  congr 1
  funext g
  by_cases hx : (c, Matrix.of g) ∈ DomR k r z z'
  · have e1 := X.fn_apply j Φ (c, Matrix.of g) hx
    have e2 := X.fn_apply (fnConj j) Ψ (c, Matrix.of g) hx
    simp only at e1 e2
    rw [e1, e2, hsInner_smul_left', hsInner_smul_right', fnVal_conj]
  · have h0 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off Φ hx
    have h1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g) = 0 := radSp_zero_off (X.fn j Φ) hx
    rw [h0, h1, hsInner_zero_left, hsInner_zero_left]

end Fn

section Top

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem adjTop_of_tAdj (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π')))
    (K : Fin (P.r + 1) → Submodule ℂ (RadSp P.k P.r z z' π π')) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0)
    (U : Submodule ℂ (RadSp P.k P.r z z' π π')) (hU : IntOn μ U) (hK : K (Fin.last P.r) ≤ U)
    (hfn : ∀ j, ∀ Φ ∈ U, X.fn j Φ ∈ U)
    (hT : ∀ Y : ℂ, star Y = Y → ∀ a b, X.QQ Y a b ∈ adjAlg μ U hU) :
    AdjTop (S := S) P z z' π π' μ L st K l0 := by
  have hD' := hD
  obtain ⟨κ, hx, hxi, -⟩ :=
    xKappaOfNF Formalism.FourierDecayAlt.P.normal_form_actual kappaFibrePos Wp Wq P z z' π π' X μ L st l0 hD
  obtain ⟨-, -, hAL, hQQ, -, -, -, hst⟩ := hD
  obtain ⟨-, -, -, -, -, -, hζ, hζi, hζb, hζbi, hGG, hGGi, -⟩ := hAL
  have hz : ∀ g ∈ zfns L, g ∈ adjAlg μ U hU := by
    intro g hg
    simp only [zfns, Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hζ]; exact fn_adj X μ U hU hfn 0
    · rw [hζi]; exact fn_adj X μ U hU hfn 1
    · rw [hζb]; exact fn_adj X μ U hU hfn 2
    · rw [hζbi]; exact fn_adj X μ U hU hfn 3
    · rw [hGG]; exact fn_adj X μ U hU hfn 4
    · rw [hGGi]; exact fn_adj X μ U hU hfn 5
  have hQ : ∀ Y : ℂ, star Y = Y → ∀ i j, st.QQ Y i j ∈ adjAlg μ U hU := by
    intro Y hY i j
    rw [hQQ Y, Matrix.smul_apply]
    exact (adjAlg μ U hU).smul_mem (hT Y hY i j) _
  exact adjTop_of_gens P z z' π π' X μ L st K l0 hD' U hU hK
    (gens_of _ L st hst κ _ hx hxi hz hQ)

end Top

end Formalism.FourierDecayAlt.P5.HerA
end
end
