import Mathlib
import Formalism.GL3MeanSquares.QuadraticFormLowerBound

namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

section A
open Finset




end A

section B
open Finset
open scoped ComplexOrder


end B

section C
open Finset MeasureTheory
open scoped ComplexOrder

lemma halfSum (N : ℕ) (sg : Fin N → Bool) (f : Fin N → Fin N → ℝ)
    (hs : ∀ a b, f a b = f b a) (h0 : ∀ a b, sg a = sg b → f a b = 0) :
    ∑ a, ∑ b, f a b = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
  have split : ∀ a b, f a b = (if b < a then f a b else 0) + (if a < b then f a b else 0) := by
    intro a b
    rcases lt_trichotomy a b with h | h | h
    · simp [h, lt_asymm h]
    · subst h
      simp [h0 a a rfl]
    · simp [h, lt_asymm h]
  have swap : ∑ a, ∑ b, (if a < b then f a b else 0) = ∑ a, ∑ b, (if b < a then f a b else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs]
  have filt : ∀ a, ∑ b, (if b < a then f a b else 0) =
      ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
    intro a
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun b _ => ?_
    by_cases hb : b < a <;> by_cases hsg : sg a = sg b <;> simp [hb, hsg, h0 a b]
  calc ∑ a, ∑ b, f a b = ∑ a, ∑ b, (if b < a then f a b else 0) +
        ∑ a, ∑ b, (if a < b then f a b else 0) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun b _ => split a b
    _ = 2 * ∑ a, ∑ b ∈ univ.filter (fun b => b < a ∧ sg a ≠ sg b), f a b := by
        rw [swap, ← two_mul]
        simp only [filt]





lemma natIneq (p q : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (h : ¬ (p = 1 ∧ q = 1)) :
    p + q + 1 ≤ 2 * p * q := by
  by_cases hp2 : 2 ≤ p
  · have h1 : p * 1 ≤ p * q := Nat.mul_le_mul le_rfl hq
    have h2 : 2 * q ≤ p * q := Nat.mul_le_mul hp2 le_rfl
    nlinarith
  · have hp1 : p = 1 := by omega
    subst hp1
    omega

set_option maxHeartbeats 800000 in

theorem zBound : Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.PartitionFunctionBound
  intro C' hC'
  refine ⟨8 * C' + 1, by linarith, ?_⟩
  intro C'' hC'' p q ε₀ hp hq hexp he1
  push_cast at hexp ⊢
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hqR : (1:ℝ) ≤ q := by exact_mod_cast hq
  have hM : (1:ℝ) ≤ (p:ℝ) * q := by nlinarith
  have hε0 : 0 < ε₀ := lt_of_lt_of_le (Real.exp_pos _) hexp
  have hCpos : 0 < C'' := by linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = C' * (ε₀ / (C'' * ((p:ℝ) * q))) := ⟨_, rfl⟩
  rw [← hδ]
  have hCi : C'' * C''⁻¹ = 1 := mul_inv_cancel₀ hCpos.ne'
  have hMi : ((p:ℝ) * q) * ((p:ℝ) * q)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hCi0 : 0 < C''⁻¹ := inv_pos.2 hCpos
  have hMi0 : 0 < ((p:ℝ) * q)⁻¹ := inv_pos.2 (by linarith)
  have hδ' : δ = C' * ε₀ * C''⁻¹ * ((p:ℝ) * q)⁻¹ := by
    rw [hδ, div_eq_mul_inv, mul_inv]
    ring
  have k1 : 8 * C' * C''⁻¹ ≤ C'' * C''⁻¹ := mul_le_mul_of_nonneg_right (by linarith) hCi0.le
  have hMδ : ((p:ℝ) * q) * δ = C' * C''⁻¹ * ε₀ := by
    rw [hδ']
    linear_combination (C' * ε₀ * C''⁻¹) * hMi
  have k2 := mul_le_mul_of_nonneg_right k1 hε0.le
  have k2' : C'' * C''⁻¹ * ε₀ = ε₀ := by rw [hCi, one_mul]
  have hMδ8 : ((p:ℝ) * q) * δ ≤ ε₀ / 8 := by linarith
  have hδ0 : 0 ≤ δ := by
    rw [hδ']
    exact mul_nonneg (mul_nonneg (mul_nonneg hC' hε0.le) hCi0.le) hMi0.le
  have hδ1 : δ ≤ ε₀ / 8 := by linarith [mul_le_mul_of_nonneg_right hM hδ0]
  refine ⟨by linarith, ?_⟩
  have hb := one_add_mul_le_pow (show (-2 : ℝ) ≤ -δ by linarith) (p * q)
  push_cast at hb
  rw [← sub_eq_add_neg] at hb
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = (1 - δ) ^ (p * q) := ⟨_, rfl⟩
  rw [inv_pow, ← hY]
  rw [← hY] at hb
  have hYlow : 1 - ε₀ / 8 ≤ Y := by linarith
  have hY1 : Y ≤ 1 := by
    rw [hY]
    first
      | exact pow_le_one₀ (by linarith) (by linarith)
      | exact pow_le_one _ (by linarith) (by linarith)
  have hYpos : 0 < Y := by linarith
  have hU : (1 - ε₀) * (1 - ε₀)⁻¹ = 1 := mul_inv_cancel₀ (by linarith)
  have hV : Y * Y⁻¹ = 1 := mul_inv_cancel₀ hYpos.ne'
  have hU0 : 0 < (1 - ε₀)⁻¹ := inv_pos.2 (by linarith)
  have hV0 : 0 < Y⁻¹ := inv_pos.2 hYpos
  have hU1 : 1 ≤ (1 - ε₀)⁻¹ := by linarith [mul_pos hε0 hU0]
  have hV1 : 1 ≤ Y⁻¹ := by linarith [mul_nonneg (sub_nonneg.2 hY1) hV0.le]
  have hUV : (1 - ε₀)⁻¹ - Y⁻¹ = (1 - ε₀)⁻¹ * Y⁻¹ * (Y - (1 - ε₀)) := by
    linear_combination (-(1 - ε₀)⁻¹) * hV + Y⁻¹ * hU
  have hY7 : 7 * ε₀ / 8 ≤ Y - (1 - ε₀) := by linarith
  have hUV0 : 0 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := (mul_pos hU0 hV0).le
  have key := mul_le_mul_of_nonneg_left hY7 hUV0
  have hUV1 : 1 * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul hU1 hV1 zero_le_one hU0.le
  have hE0 : Real.exp (-(2 * (p:ℝ) * q)) ≤ ε₀ := by
    refine le_trans (Real.exp_le_exp.2 ?_) hexp
    linarith [mul_nonneg (sub_nonneg.2 hpR) (sub_nonneg.2 hqR)]
  by_cases h11 : p = 1 ∧ q = 1
  · obtain ⟨hp1, hq1⟩ := h11
    have hp1' : (p:ℝ) = 1 := by exact_mod_cast hp1
    have hq1' : (q:ℝ) = 1 := by exact_mod_cast hq1
    rw [hp1', hq1'] at hexp
    have he2 : Real.exp 2 ≤ 8 := by
      have h := Real.exp_one_lt_d9
      have h' : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      rw [h']
      have h3 : Real.exp 1 ≤ 2.72 := by linarith
      calc Real.exp 1 * Real.exp 1 ≤ 2.72 * 2.72 := mul_le_mul h3 h3 (Real.exp_pos 1).le (by norm_num)
        _ ≤ 8 := by norm_num
    have hm2 : Real.exp (-2) * Real.exp 2 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have hε8 : 1 / 8 ≤ ε₀ := by
      have : Real.exp (-(1 + 1)) = Real.exp (-2) := by norm_num
      rw [this] at hexp
      have h5 := mul_le_mul_of_nonneg_left he2 (Real.exp_pos (-2)).le
      linarith
    have hU8 : 8 / 7 ≤ (1 - ε₀)⁻¹ := by
      linarith [mul_le_mul_of_nonneg_right hε8 hU0.le]
    have hUVb : (1 - ε₀)⁻¹ * 1 ≤ (1 - ε₀)⁻¹ * Y⁻¹ := mul_le_mul_of_nonneg_left hV1 hU0.le
    have k3 := mul_le_mul_of_nonneg_right (show 8 / 7 ≤ (1 - ε₀)⁻¹ * Y⁻¹ by linarith)
      (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith
  · have hnat := natIneq p q hp hq h11
    have hreal : (p:ℝ) + q + 1 ≤ 2 * p * q := by exact_mod_cast hnat
    have hE1 : Real.exp (-(2 * (p:ℝ) * q)) ≤ Real.exp (-((p:ℝ) + q) + -1) :=
      Real.exp_le_exp.2 (by linarith)
    rw [Real.exp_add] at hE1
    have hx : Real.exp (-1) * Real.exp 1 = 1 := by
      rw [← Real.exp_add]
      norm_num
    have h2 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
    have hm1 : Real.exp (-1) ≤ 1 / 2 := by linarith [mul_le_mul_of_nonneg_left h2 (Real.exp_pos (-1)).le]
    have hE2 : Real.exp (-((p:ℝ) + q)) * Real.exp (-1) ≤ ε₀ * (1 / 2) :=
      mul_le_mul hexp hm1 (Real.exp_pos _).le hε0.le
    have k4 := mul_le_mul_of_nonneg_right hUV1 (show (0:ℝ) ≤ 7 * ε₀ / 8 by linarith)
    linarith

end C

section D
open Finset
open scoped Nat







end D

section E
open Finset Matrix Unitary


end E

section F
open Finset

lemma cardUni (F : Type) [Field F] [Fintype F] (r : ℕ) (blk : Fin r → ℕ) :
    Nat.card {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} =
      Fintype.card F ^ (univ.filter (fun ij : Fin r × Fin r => blk ij.1 < blk ij.2)).card := by
  classical
  have e : {A : Matrix (Fin r) (Fin r) F // ∀ i j, blk j ≤ blk i → A i j = if i = j then 1 else 0} ≃
      ({ij : Fin r × Fin r // blk ij.1 < blk ij.2} → F) :=
    { toFun := fun A ij => A.1 ij.1.1 ij.1.2
      invFun := fun g => ⟨fun i j => if h : blk i < blk j then g ⟨(i, j), h⟩ else if i = j then 1 else 0,
        fun i j hij => by simp [not_lt.2 hij]⟩
      left_inv := fun A => by
        apply Subtype.ext
        funext i j
        by_cases h : blk i < blk j
        · simp [h]
        · simp [h, A.2 i j (not_lt.1 h)]
      right_inv := fun g => by
        funext ij
        simp [ij.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_subtype]

def bb (k rS : ℕ) (i : ℕ) : ℕ := if i < rS then i else if i < rS + (k + 1) then rS else i - k
def cc (k rS : ℕ) (j : ℕ) : ℕ := if j < rS then j else if j < rS + (k + 1) then rS else j

lemma inner (k rS j : ℕ) (hj : j < rS + (k + 1) + rS) :
    ((range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j)).card = cc k rS j := by
  have h : (range (rS + (k + 1) + rS)).filter (fun i => bb k rS i < bb k rS j) = range (cc k rS j) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    simp only [bb, cc]
    constructor
    · rintro ⟨h1, h2⟩
      split_ifs at h2 ⊢ <;> omega
    · intro h1
      refine ⟨by split_ifs at h1 <;> omega, ?_⟩
      split_ifs at h1 ⊢ <;> omega
  rw [h, card_range]

lemma total (k rS : ℕ) : ∑ j ∈ range (rS + (k + 1) + rS), cc k rS j = rS * (2 * k + 1 + 2 * rS) := by
  rw [Finset.sum_range_add, Finset.sum_range_add]
  have e1 : ∑ x ∈ range rS, cc k rS x = ∑ x ∈ range rS, x :=
    Finset.sum_congr rfl fun x hx => by simp [cc, mem_range.1 hx]
  have e2 : ∑ x ∈ range (k + 1), cc k rS (rS + x) = ∑ x ∈ range (k + 1), rS :=
    Finset.sum_congr rfl fun x hx => by
      have := mem_range.1 hx
      simp only [cc]
      split_ifs <;> omega
  have e3 : ∑ x ∈ range rS, cc k rS (rS + (k + 1) + x) = ∑ x ∈ range rS, (rS + (k + 1) + x) :=
    Finset.sum_congr rfl fun x _ => by
      simp only [cc]
      split_ifs <;> omega
  rw [e1, e2, e3, Finset.sum_add_distrib, Finset.sum_const, Finset.sum_const, card_range, card_range,
    smul_eq_mul, smul_eq_mul]
  have hS := Finset.sum_range_id_mul_two rS
  rcases rS with _ | m
  · simp
  · simp only [Nat.add_sub_cancel] at hS
    nlinarith [hS]

lemma countFree (k rS r : ℕ) (hr : r = rS + (k + 1) + rS) :
    (univ.filter (fun ij : Fin r × Fin r => bb k rS ij.1.val < bb k rS ij.2.val)).card =
      rS * (2 * k + 1 + 2 * rS) := by
  subst hr
  simp only [Finset.card_filter, Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  have h : ∀ j : Fin (rS + (k + 1) + rS),
      ∑ i : Fin (rS + (k + 1) + rS), (if bb k rS i.val < bb k rS j.val then 1 else 0) = cc k rS j.val := by
    intro j
    have h1 := inner k rS j.val j.isLt
    rw [Finset.card_filter] at h1
    rw [Fin.sum_univ_eq_sum_range (fun i => if bb k rS i < bb k rS j.val then 1 else 0), h1]
  rw [Finset.sum_congr rfl (fun j _ => h j), Fin.sum_univ_eq_sum_range (fun j => cc k rS j), total]


end F

end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates

namespace Formalism.HermitianLattices.CumulantEstimateDefs


end Formalism.HermitianLattices.CumulantEstimateDefs
