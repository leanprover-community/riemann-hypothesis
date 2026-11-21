import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MatrixKroneckerPowerTensorActionAlgebra

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin.ActNorm

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_apply_eq_prod {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ)
    (a b : Fin n → ι) : _root_.GlobalTheory.ClassFin.tpow n y a b = ∏ k, y (a k) (b k) := by
  simp [_root_.GlobalTheory.ClassFin.tpow]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma tpow_conjTranspose {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) :
    (_root_.GlobalTheory.ClassFin.tpow n y)ᴴ = _root_.GlobalTheory.ClassFin.tpow n yᴴ := by
  ext a b
  simp [tpow_apply_eq_prod, conjTranspose_apply, star_prod]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma nsq_eq_sum_sum_norm_sq_components {ι : Type} [Fintype ι] {m : ℕ} (d : Fin m → ℕ)
    (x : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) :
    _root_.GlobalTheory.ClassFin.nsq x = ∑ i, ∑ a : Fin (d i) → ι, ‖x ⟨i, a⟩‖ ^ 2 := by
  unfold _root_.GlobalTheory.ClassFin.nsq _root_.GlobalTheory.ClassFin.TIdx at *
  exact Fintype.sum_sigma _

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma act_apply_eq_vecMul_tpow {ι : Type} [Fintype ι] {m : ℕ}
    (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ) (i : Fin m)
    (a : Fin (d i) → ι) :
    _root_.GlobalTheory.ClassFin.act d v y ⟨i, a⟩ =
      ((fun b => v ⟨i, b⟩) ᵥ* _root_.GlobalTheory.ClassFin.tpow (d i) y) a := rfl

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one {κ : Type} [Fintype κ] [DecidableEq κ] (w : κ → ℂ)
    (M : Matrix κ κ ℂ) (hM : M * Mᴴ = 1) : ∑ c, ‖(w ᵥ* M) c‖ ^ 2 = ∑ a, ‖w a‖ ^ 2 := by
  have key : ∀ x : κ → ℂ, ((∑ c, ‖x c‖ ^ 2 : ℝ) : ℂ) = x ⬝ᵥ star x := by
    intro x
    push_cast
    simp [dotProduct, Complex.mul_conj']
  apply Complex.ofReal_injective
  rw [key, key, star_vecMul, dotProduct_mulVec, vecMul_vecMul, hM, vecMul_one]

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma sum_norm_sq_vecMul_le_card_sq_mul_bound_sq {κ : Type} [Fintype κ] (w : κ → ℂ) (M : Matrix κ κ ℂ)
    (K : ℝ) (hK : ∀ a c, ‖M a c‖ ≤ K) :
    ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) ^ 2 * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
  have hc : ∀ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 := by
    intro c
    have h1 : ‖(w ᵥ* M) c‖ ≤ ∑ a, ‖w a‖ * K := by
      simp only [vecMul, dotProduct]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hK a c) (norm_nonneg _)
    calc ‖(w ᵥ* M) c‖ ^ 2 ≤ (∑ a, ‖w a‖ * K) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ = K ^ 2 * (∑ a, ‖w a‖) ^ 2 := by rw [← Finset.sum_mul]; ring
      _ ≤ K ^ 2 * ((Fintype.card κ : ℝ) * ∑ a, ‖w a‖ ^ 2) := by
          gcongr
          simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun a => ‖w a‖)
      _ = _ := by ring
  calc ∑ c, ‖(w ᵥ* M) c‖ ^ 2 ≤ ∑ _c : κ, (Fintype.card κ : ℝ) * K ^ 2 * ∑ a, ‖w a‖ ^ 2 :=
        Finset.sum_le_sum fun c _ => hc c
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in
private lemma norm_tpow_apply_le_pow_of_forall_norm_le {ι : Type} (n : ℕ) (y : Matrix ι ι ℂ) (B : ℝ)
    (hy : ∀ i j, ‖y i j‖ ≤ B) (a b : Fin n → ι) : ‖_root_.GlobalTheory.ClassFin.tpow n y a b‖ ≤ B ^ n := by
  rw [tpow_apply_eq_prod, norm_prod]
  calc ∏ k, ‖y (a k) (b k)‖ ≤ ∏ _k : Fin n, B :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun k _ => hy _ _
    _ = B ^ n := by simp

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ), (∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ), U * Uᴴ = 1 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v U) = _root_.GlobalTheory.ClassFin.nsq v) ∧ (∀ C : ℝ, ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (y : Matrix ι ι ℂ), (∀ i j, ‖y i j‖ ≤ C) → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v y) ≤ C' * _root_.GlobalTheory.ClassFin.nsq v) ∧ ∀ v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ, Continuous (_root_.GlobalTheory.ClassFin.act d v) := by
  intro ι _ _ m d
  refine ⟨fun v U hU => ?_, fun C => ?_, fun v => ?_⟩
  · have hK : ∀ n, _root_.GlobalTheory.ClassFin.tpow n U * (_root_.GlobalTheory.ClassFin.tpow n U)ᴴ = 1 := by
      intro n
      have h := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).1 n
      rw [tpow_conjTranspose, ← h.2.1, hU, h.1]
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    exact sum_norm_sq_vecMul_eq_of_mul_conjTranspose_eq_one _ _ (hK _)
  · set B := max C 0
    refine ⟨∑ i, (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2,
      Finset.sum_nonneg fun _ _ => by positivity, fun v y hy => ?_⟩
    have hyB : ∀ i j, ‖y i j‖ ≤ B := fun i j => (hy i j).trans (le_max_left _ _)
    rw [nsq_eq_sum_sum_norm_sq_components, nsq_eq_sum_sum_norm_sq_components, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    simp only [act_apply_eq_vecMul_tpow]
    refine (sum_norm_sq_vecMul_le_card_sq_mul_bound_sq _ _ _ (norm_tpow_apply_le_pow_of_forall_norm_le _ y B hyB)).trans ?_
    gcongr
    exact Finset.single_le_sum
      (f := fun i => (Fintype.card (Fin (d i) → ι) : ℝ) ^ 2 * (B ^ d i) ^ 2)
      (fun _ _ => by positivity) (Finset.mem_univ i)
  · unfold _root_.GlobalTheory.ClassFin.act
    simp only [vecMul, dotProduct, tpow_apply_eq_prod]
    fun_prop

end GlobalTheory.ClassFin.ActNorm
end

section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct

namespace GlobalTheory.ClassFin

open Matrix in
open scoped Kronecker ComplexOrder TensorProduct in

theorem _root_.GlobalTheory.ClassFin.act_exp_eq_of_isMinVec : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (m : ℕ) (d : Fin m → ℕ) (v : _root_.GlobalTheory.ClassFin.TIdx ι d → ℂ) (U : Matrix ι ι ℂ) (δ : ι → ℝ), _root_.GlobalTheory.ClassFin.IsMinVec d v → U * Uᴴ = 1 → ∑ i, δ i = 0 → _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (δ i) : ℂ)) * Uᴴ)) = _root_.GlobalTheory.ClassFin.nsq v → ∀ s : ℝ, _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (s * δ i) : ℂ)) * Uᴴ) = v := by
  intro ι _ _ m d v U δ hmin hU hδ hone s
  obtain ⟨act1, actmul, -⟩ := (_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d v
  have hUH : Uᴴ * Uᴴᴴ = 1 := by
    rw [conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hU
  have hnormU := (_root_.GlobalTheory.ClassFin.ActNorm.act_norm_continuity ι m d).1
  set u := _root_.GlobalTheory.ClassFin.act d v U with hu
  set lam : _root_.GlobalTheory.ClassFin.TIdx ι d → ℝ := fun k => ∑ j, δ (k.2 j) with hlam
  have hdiag : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d u (diagonal fun i => (Real.exp (r * δ i) : ℂ)) =
        fun k => u k * (Real.exp (r * lam k) : ℂ) := by
    intro r
    funext k
    rw [((_root_.GlobalTheory.ClassFin.tpow_act_algebra ι ℂ).2 m d u).2.2.1]
    simp only [hlam, Finset.mul_sum, Real.exp_sum, Complex.ofReal_prod]
  have hsplit : ∀ r : ℝ,
      _root_.GlobalTheory.ClassFin.act d v (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ) =
        _root_.GlobalTheory.ClassFin.act d (fun k => u k * (Real.exp (r * lam k) : ℂ)) Uᴴ := by
    intro r
    rw [actmul, actmul, hdiag]
  have hF : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq (_root_.GlobalTheory.ClassFin.act d v
      (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ)) =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [hsplit, hnormU _ _ hUH]
    unfold _root_.GlobalTheory.ClassFin.nsq
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, mul_pow]
  have hdet : ∀ r : ℝ, (U * diagonal (fun i => (Real.exp (r * δ i) : ℂ)) * Uᴴ).det = 1 := by
    intro r
    have h1 : U.det * Uᴴ.det = 1 := by rw [← det_mul, hU, det_one]
    rw [det_mul, det_mul, det_diagonal, ← Complex.ofReal_prod, ← Real.exp_sum, ← Finset.mul_sum,
      hδ, mul_zero, Real.exp_zero, Complex.ofReal_one, mul_one, h1]
  have hmin' : ∀ r : ℝ, _root_.GlobalTheory.ClassFin.nsq v ≤ ∑ k, ‖u k‖ ^ 2 * Real.exp (r * lam k) ^ 2 := by
    intro r
    rw [← hF r]
    exact hmin _ ⟨_, hdet r, rfl⟩
  have h0 : ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    simp only [zero_mul, Real.exp_zero, one_pow, mul_one]
    exact hnormU v U hU
  have h1 : ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 = _root_.GlobalTheory.ClassFin.nsq v := by
    rw [← hF 1]
    simpa only [one_mul] using hone
  have hhalf := hmin' (1 / 2)
  have hsq : ∀ k, Real.exp (1 * lam k) ^ 2 = (Real.exp (1 / 2 * lam k) ^ 2) ^ 2 := by
    intro k
    have e : Real.exp (1 * lam k) = Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [e]
  have hterm : ∀ k ∈ Finset.univ, 0 ≤ ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 :=
    fun k _ => by positivity
  have hsum : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 = 0 := by
    have e : ∑ k, ‖u k‖ ^ 2 * (Real.exp (1 / 2 * lam k) ^ 2 - 1) ^ 2 =
        ∑ k, ‖u k‖ ^ 2 * Real.exp (1 * lam k) ^ 2 + ∑ k, ‖u k‖ ^ 2 * Real.exp (0 * lam k) ^ 2
          - 2 * ∑ k, ‖u k‖ ^ 2 * Real.exp (1 / 2 * lam k) ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsq]
      simp only [zero_mul, Real.exp_zero]
      ring
    refine le_antisymm ?_ (Finset.sum_nonneg hterm)
    rw [e, h0, h1]
    linarith
  have hfix : ∀ k, u k * (Real.exp (s * lam k) : ℂ) = u k := by
    intro k
    have hk := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hsum k (Finset.mem_univ k)
    rcases mul_eq_zero.mp hk with ha | hb
    · have hz : u k = 0 := by simpa using ha
      simp [hz]
    · have ht : Real.exp (1 / 2 * lam k) ^ 2 = 1 := by
        have := (pow_eq_zero_iff (n := 2) two_ne_zero).mp hb
        linarith
      have hl : lam k = 0 := by
        rw [← Real.exp_nat_mul] at ht
        simpa using (Real.exp_eq_one_iff _).mp ht
      simp [hl]
  rw [hsplit s]
  simp only [hfix]
  rw [← actmul, hU, act1]

end GlobalTheory.ClassFin
end
