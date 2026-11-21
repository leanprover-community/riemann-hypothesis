import ReciprocityTheory.GeometryOfNumbers.SphericalMonomials.ChiPSt
import Mathlib

section
noncomputable section

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Topology Asymptotics

def hsDefect (D : ℕ) (chi : ℕ → ℝ) (top : ℝ) (n : ℕ) : ℝ :=
  chi n - top * (n : ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)

theorem isLittleO_pow_mul_log (D : ℕ) :
    (fun n : ℕ => (n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have h1 : (fun n : ℕ => Real.log ((n : ℝ) + 1)) =o[atTop] fun n : ℕ => (n : ℝ) + 1 :=
    Real.isLittleO_log_id_atTop.comp_tendsto ht
  have h2 : (fun n : ℕ => (n : ℝ) + 1) =O[atTop] fun n : ℕ => (n : ℝ) := by
    refine IsBigO.of_bound 2 ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1:ℝ) ≤ n := by exact_mod_cast hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos (by linarith)]
    linarith
  have h3 := (isBigO_refl (fun n : ℕ => (n : ℝ) ^ D) atTop).mul_isLittleO (h1.trans_isBigO h2)
  exact h3.congr (fun n => rfl) (fun n => by ring)

theorem isEquivalent_add_pow (D j : ℕ) :
    (fun n : ℕ => ((n : ℝ) + j) ^ D) ~[atTop] fun n : ℕ => (n : ℝ) ^ D := by
  have h1 : (fun _n : ℕ => (j : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
    have : (fun _n : ℕ => (1 : ℝ)) =o[atTop] fun n : ℕ => (n : ℝ) := by
      rw [isLittleO_one_left_iff]
      simpa [Real.norm_eq_abs] using
        (tendsto_natCast_atTop_atTop (R := ℝ)).congr' (Eventually.of_forall fun n => by simp)
    simpa using this.const_mul_left (j : ℝ)
  have h2 := (IsEquivalent.refl (u := fun n : ℕ => (n : ℝ)) (l := atTop)).add_isLittleO h1
  exact h2.pow D


theorem isLittleO_succ_pow_sub (D : ℕ) :
    (fun n : ℕ => ((n : ℝ) + 1) ^ (D + 1) - (n : ℝ) ^ (D + 1)) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have h := (isEquivalent_add_pow (D + 1) 1).isLittleO
  exact h.congr (fun n => by simp) (fun n => rfl)

theorem powLog_mono (D : ℕ) {m n : ℕ} (h : m ≤ n) :
    (m : ℝ) ^ D * Real.log ((m : ℝ) + 1) ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have hmn : (m : ℝ) ≤ n := by exact_mod_cast h
  have hm0 : (0 : ℝ) ≤ m := by positivity
  have hl0 : 0 ≤ Real.log ((m : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hl : Real.log ((m : ℝ) + 1) ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  exact mul_le_mul (pow_le_pow_left₀ hm0 hmn D) hl hl0 (by positivity)

theorem powLog_nonneg (D n : ℕ) : 0 ≤ (n : ℝ) ^ D * Real.log ((n : ℝ) + 1) := by
  have : (0 : ℝ) ≤ n := by positivity
  exact mul_nonneg (by positivity) (Real.log_nonneg (by linarith))

theorem chiP_add_sub_le (D : ℕ) (C : ℝ)
    (hC : ∀ n : ℕ, 1 ≤ n → chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1))
    (k n : ℕ) (hn : 1 ≤ n) :
    chiP D (n + k) - chiP D n ≤
      ∑ j ∈ Finset.range k, |C| * (((n + j : ℕ) : ℝ) ^ D * Real.log (((n + j : ℕ) : ℝ) + 1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have h1 := hC (n + k) (by omega)
    have h2 : C * (((n + k : ℕ) : ℝ) ^ D) * Real.log (((n + k : ℕ) : ℝ) + 1) ≤
        |C| * (((n + k : ℕ) : ℝ) ^ D * Real.log (((n + k : ℕ) : ℝ) + 1)) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (powLog_nonneg D (n + k))
    have h3 : chiP D (n + (k + 1)) = chiP D (n + k + 1) := by rw [Nat.add_assoc]
    rw [h3]
    linarith

theorem hilbertSamuelDefect_projectiveSpace_abs_le (D : ℕ) (hh : ℝ) :
    ∃ C : ℝ, ∀ n : ℕ, |hsDefect D (chiP D) hh n| ≤ C * (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_le D
  refine ⟨|C| + |hh|, fun n => ?_⟩
  have h0 := chiP_nonneg D n
  have h1 := hC n
  have hp : (0:ℝ) ≤ (n:ℝ) ^ (D + 1) := by positivity
  have hFpos : (0:ℝ) < ((D + 1).factorial : ℝ) := by positivity
  have hf : (1:ℝ) ≤ ((D + 1).factorial : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hq : |hh * (n:ℝ) ^ (D + 1) / ((D + 1).factorial : ℝ)| ≤ |hh| * (n:ℝ) ^ (D + 1) := by
    rw [abs_div, abs_mul, abs_of_nonneg hp, abs_of_pos hFpos]
    exact div_le_self (by positivity) hf
  have hc : chiP D n ≤ |C| * (n:ℝ) ^ (D + 1) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self C) hp)
  have hq' := abs_le.mp hq
  unfold hsDefect
  rw [abs_le]
  constructor <;> nlinarith [abs_nonneg C, abs_nonneg hh]

theorem hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO (D : ℕ) (hh : ℝ) :
    (fun n => hsDefect D (chiP D) hh (n + 1) - hsDefect D (chiP D) hh n) =o[atTop]
      fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := exists_chiP_succ_sub_le D
  have hA : (fun n : ℕ => chiP D (n + 1) - chiP D n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
    refine IsBigO.trans_isLittleO ?_ (isLittleO_pow_mul_log D)
    refine IsBigO.of_bound |C| ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have h0 := chiP_succ_sub_nonneg D n
    have h1 := hC n hn
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0, ← abs_mul]
    calc chiP D (n + 1) - chiP D n ≤ C * (n : ℝ) ^ D * Real.log (n + 1) := h1
      _ = C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1)) := by ring
      _ ≤ |C * ((n : ℝ) ^ D * Real.log ((n : ℝ) + 1))| := le_abs_self _
  have hB := (isLittleO_succ_pow_sub D).const_mul_left (hh / ((D + 1).factorial : ℝ))
  refine (hA.sub hB).congr (fun n => ?_) (fun n => rfl)
  simp only [hsDefect]
  push_cast
  ring




end ReciprocityTheory.GeometryOfNumbersTheory
end
end

section
namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Topology Asymptotics

theorem hsDefect_two_mul (D : ℕ) (hh : ℝ) (n : ℕ) :
    hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n = hsDefect D (chiP D) hh (2 * n) := by
  unfold hsDefect
  push_cast
  rw [mul_pow]
  ring

private theorem eventually_abs_le_half_add_of_doubling_bounds (D : ℕ) (f : ℕ → ℝ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (h1 : ∀ᶠ n : ℕ in atTop, |f (2 * n) - 2 ^ D * f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (h2 : ∀ᶠ n : ℕ in atTop, |f (n + 1) - f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (hf : ∀ᶠ n : ℕ in atTop, |f n| ≤ A * (n : ℝ) ^ (D + 1)) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (A / 2 + 2 * δ) * (n : ℝ) ^ (D + 1) := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 hf
  have hp : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
  have hp0 : (0 : ℝ) < 2 ^ D := by positivity

  have hev : ∀ n : ℕ, N1 + N2 + N3 ≤ n →
      |f (2 * n)| ≤ 2 ^ D * A * (n : ℝ) ^ (D + 1) + δ * (n : ℝ) ^ (D + 1) := by
    intro n hn
    have e1 := hN1 n (by omega)
    have e3 := hN3 n (by omega)
    have h0 := abs_sub_abs_le_abs_sub (f (2 * n)) (2 ^ D * f n)
    rw [abs_mul, abs_of_pos hp0] at h0
    have hpA : 2 ^ D * |f n| ≤ 2 ^ D * (A * (n : ℝ) ^ (D + 1)) :=
      mul_le_mul_of_nonneg_left e3 hp0.le
    nlinarith
  have hcast : ∀ n : ℕ, (((2 * n : ℕ) : ℝ)) ^ (D + 1) = 2 * 2 ^ D * (n : ℝ) ^ (D + 1) := by
    intro n
    push_cast
    rw [mul_pow, pow_succ]
    ring
  refine eventually_atTop.2 ⟨2 * (N1 + N2 + N3) + 1, fun m hm => ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hn : N1 + N2 + N3 ≤ n := by omega
    have hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
    have e := hev n hn
    rw [hcast]
    have hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)
    nlinarith
  · have hn : N1 + N2 + N3 ≤ n := by omega
    have hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
    have e := hev n hn
    have e2 := hN2 (2 * n) (by omega)
    rw [hcast] at e2
    have h0 := abs_sub_abs_le_abs_sub (f (2 * n + 1)) (f (2 * n))
    have hmono : (((2 * n : ℕ) : ℝ)) ^ (D + 1) ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ (D + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.le_succ _
    rw [hcast] at hmono
    have hco : 0 ≤ A / 2 + 2 * δ := by positivity
    have h3 := mul_le_mul_of_nonneg_left hmono hco
    have hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)
    nlinarith

private theorem isLittleO_pow_of_doubling_and_increment_bounds (D : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (D + 1))
    (h1 : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, |f (2 * n) - 2 ^ D * f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (h2 : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, |f (n + 1) - f n| ≤ δ * (n : ℝ) ^ (D + 1)) :
    f =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have hC' : ∀ n : ℕ, |f n| ≤ |C| * (n : ℝ) ^ (D + 1) := fun n =>
    (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have key : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |f n| ≤ (|C| / 2 ^ k + 2 * (c / 3)) * (n : ℝ) ^ (D + 1) := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun n => (hC' n).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [pow_zero, div_one]
      linarith
    | succ k ih =>
      have := eventually_abs_le_half_add_of_doubling_bounds D f _ (c / 3 / 2) (by positivity) (by positivity)
        (h1 _ (by positivity)) (h2 _ (by positivity)) ih
      refine this.mono fun n hn => hn.trans (le_of_eq ?_)
      rw [pow_succ]
      ring
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|C| * 3 / c) (by norm_num : (1 : ℝ) < 2)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_lt_iff₀ hc] at hk
  have hsmall : |C| / 2 ^ k ≤ c / 3 := by
    rw [div_le_iff₀ h2k]
    linarith
  refine (key k).mono fun n hn => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  linarith

theorem hilbertSamuelDefect_projectiveSpace_isLittleO (D : ℕ) (hh : ℝ)
    (hver : (fun n => hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n -
      2 ^ D * hsDefect D (chiP D) hh n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1)) :
    hsDefect D (chiP D) hh =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := hilbertSamuelDefect_projectiveSpace_abs_le D hh
  refine isLittleO_pow_of_doubling_and_increment_bounds D _ C hC (fun δ hδ => ?_) (fun δ hδ => ?_)
  · refine (hver.def hδ).mono fun n hn => ?_
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, hsDefect_two_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))] at hn
  · refine ((hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO D hh).def hδ).mono fun n hn => ?_
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))] at hn

end ReciprocityTheory.GeometryOfNumbersTheory
end
