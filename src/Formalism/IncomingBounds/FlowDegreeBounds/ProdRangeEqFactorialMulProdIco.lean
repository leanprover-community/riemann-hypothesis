import Formalism.IncomingBounds.LemmaMNumerics

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds





theorem padicValFactorialBounds : FactValBounds := by
  intro l hl N hN
  haveI := Fact.mk hl
  have key := sub_one_mul_padicValNat_factorial (p := l) N
  have hsN : (l.digits N).sum ≤ N := Nat.digit_sum_le l N
  have hne : l.digits N ≠ [] := Nat.digits_ne_nil_iff_ne_zero.2 (by omega)
  have hs1 : 1 ≤ (l.digits N).sum := by
    have hpos : 0 < (l.digits N).getLast hne :=
      Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero l (by omega))
    have := List.le_sum_of_mem (List.getLast_mem hne)
    omega
  have hdig : (l.digits N).sum ≤ (Nat.log l N + 1) * (l - 1) := by
    have hlen := Nat.digits_len l N hl.one_lt (by omega)
    have := List.sum_le_card_nsmul (l.digits N) (l - 1)
      (fun x hx => by have := Nat.digits_lt_base hl.one_lt hx; omega)
    rwa [smul_eq_mul, hlen] at this
  have hl2 : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hl1 : (0 : ℝ) < l - 1 := by linarith
  have e := congrArg (fun t : ℕ => (t : ℝ)) key
  simp only [Nat.cast_mul, Nat.cast_sub hsN, Nat.cast_sub hl.one_le, Nat.cast_one] at e
  have hs1R : (1 : ℝ) ≤ ((l.digits N).sum : ℝ) := by exact_mod_cast hs1
  have hdigR := (Nat.cast_le (α := ℝ)).2 hdig
  simp only [Nat.cast_mul, Nat.cast_sub hl.one_le, Nat.cast_add, Nat.cast_one] at hdigR
  have hlog : (Nat.log l N : ℝ) ≤ Real.logb l N := Real.natLog_le_logb N l
  constructor
  · have h : (N : ℝ) / ((l : ℝ) - 1) ≤ (padicValNat l N.factorial : ℝ) + ((Nat.log l N : ℝ) + 1) := by
      rw [div_le_iff₀ hl1]
      nlinarith
    linarith
  · rw [le_div_iff₀ hl1]
    nlinarith





lemma num_one_add_four_mul_le (v : ℕ) : 1 + 4 * v ≤ 5 ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [pow_succ]
    have := Nat.one_le_pow v 5 (by norm_num)
    omega



lemma num_bern_real (a : ℝ) (ha : 1 ≤ a) (w : ℕ) : 1 + (w : ℝ) * (a - 1) ≤ a ^ w := by
  have h := one_add_mul_le_pow (show (-2 : ℝ) ≤ a - 1 by linarith) w
  simpa using h

set_option maxHeartbeats 800000 in
theorem weightNumerics : LemmaMNumerics := by
  intro l hl i hi
  obtain ⟨k, rfl⟩ := hi
  have hL : (5 : ℝ) ≤ l := by exact_mod_cast hl
  set L : ℝ := (l : ℝ) with hLdef
  have hL2 : L ^ 2 - 1 ≠ 0 := by nlinarith
  have hρpos : 0 < rho l := by
    unfold rho
    apply div_pos one_pos
    nlinarith
  have hρeq : L ^ 2 * rho l = 1 + rho l := by
    unfold rho
    rw [← hLdef]
    field_simp
    ring
  have hk1 : 1 ≤ L ^ (2 * k) := one_le_pow₀ (by linarith)
  have hLi : L ≤ L ^ (2 * k + 1) := by rw [pow_succ]; nlinarith
  have hLipos : 0 < L ^ (2 * k + 1) := by positivity
  have hinv : (L ^ (2 * k + 1))⁻¹ ≤ L⁻¹ := inv_anti₀ (by linarith) hLi
  have hinv5 : L⁻¹ ≤ 5⁻¹ := inv_anti₀ (by norm_num) hL
  have hinvpos : 0 < (L ^ (2 * k + 1))⁻¹ := inv_pos.2 hLipos
  have h14 : 1 / (L - 1) ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨hρeq, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 3 := ⟨i' - 3, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 3) * rho l = L ^ (j + 1) * (1 + rho l) := by rw [← hρeq]; ring
    have hp : 0 < L ^ (j + 1) := by positivity
    have h1 : (1 + j * (L - 1)) * L ≤ L ^ j * L := mul_le_mul_of_nonneg_right b (by linarith)
    have h3 : (0 : ℝ) ≤ j * (L * (L - 1) - 1) := mul_nonneg (Nat.cast_nonneg j) (by nlinarith)
    have h4 : L ^ (j + 1) ≤ L ^ (j + 1) * (1 + rho l) := by nlinarith
    have hpow : L ^ (j + 1) = L ^ j * L := pow_succ L j
    rw [e]
    nlinarith
  · intro i' hi'
    obtain ⟨j, rfl⟩ : ∃ j, i' = j + 2 := ⟨i' - 2, by omega⟩
    push_cast
    have b := num_bern_real L (by linarith) j
    have e : L ^ (j + 2) * rho l = L ^ j * (1 + rho l) := by rw [← hρeq]; ring
    have hpj : 0 < L ^ j := by positivity
    have hm := mul_pos hpj hρpos
    have h : (0 : ℝ) ≤ j * (L - 5) := mul_nonneg (Nat.cast_nonneg j) (by linarith)
    have h25 : L ^ j * 25 ≤ L ^ j * L ^ 2 := mul_le_mul_of_nonneg_left (by nlinarith) hpj.le
    have hpow : L ^ (j + 2) = L ^ j * L ^ 2 := pow_add L j 2
    refine ⟨?_, ?_⟩
    · rw [e]
      nlinarith
    · nlinarith
  · have := mul_nonneg (by linarith : (0 : ℝ) ≤ L - 1) hρpos.le
    nlinarith
  · rw [show (2 * k + 1 + 1) / 2 = k + 1 by omega, ← pow_mul]
    have : L ^ (2 * k + 1) ≠ 0 := hLipos.ne'
    field_simp
    ring
  · linarith
  · linarith
  · have e8 : (1 : ℝ) / (8 * L) = L⁻¹ / 8 := by ring
    rw [e8]
    linarith
  · intro i' hi'
    rw [lt_div_iff₀ (by linarith : (0 : ℝ) < L - 1)]
    have b := num_bern_real L (by linarith) i'
    linarith
  · intro J v hJ hv
    dsimp only
    have hδ : 9 / 40 ≤ rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1) := by linarith
    have hJR : (2 : ℝ) ≤ J := by exact_mod_cast hJ
    refine ⟨?_, ?_⟩
    · intro hv0
      subst hv0
      have hprod : 0 ≤ ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_nonneg (by linarith) (by linarith)
      push_cast
      linarith
    · intro hv1
      obtain ⟨w, rfl⟩ : ∃ w, v = w + 1 := ⟨v - 1, by omega⟩
      have h5 : 5 ^ (w + 1) ≤ l ^ (w + 1) := Nat.pow_le_pow_left (by omega) _
      have h4 := num_one_add_four_mul_le w
      have hps : 5 ^ (w + 1) = 5 ^ w * 5 := pow_succ 5 w
      have hJn : 20 * w + 5 ≤ J := by omega
      have hJr : 20 * (w : ℝ) + 5 ≤ J := by exact_mod_cast hJn
      have hprod : (20 * (w : ℝ) + 4) * (9 / 40) ≤
          ((J : ℝ) - 1) * (rho l + 1 / 2 - (L ^ (2 * k + 1))⁻¹ / 8 - 1 / (L - 1)) :=
        mul_le_mul (by linarith) hδ (by norm_num) (by linarith)
      push_cast
      nlinarith

end Formalism.IncomingBounds
