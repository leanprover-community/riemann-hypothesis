import Formalism.HermitianCurvature.LevelRecursionCondNeeded

namespace Formalism.FourierDecayAlt.P.ProductFactorBounds

open Formalism.FourierDecayAlt.F7


theorem prod_bounds (a b : ℝ) (ha1 : a ≤ 1) (hb : 0 ≤ b) (L : List ℝ)
    (h : ∀ f ∈ L, 1 - a ≤ f ∧ f ≤ 1 + b) :
    (1 - a) ^ L.length ≤ L.prod ∧ L.prod ≤ (1 + b) ^ L.length := by
  induction L with
  | nil => simp
  | cons f L ih =>
    have hf := h f (by simp)
    have hL := ih (fun g hg => h g (by simp [hg]))
    have h0 : 0 ≤ 1 - a := by linarith
    have h1 : 0 ≤ (1 - a) ^ L.length := pow_nonneg h0 _
    have h2 : 0 ≤ L.prod := le_trans h1 hL.1
    have h3 : 0 ≤ f := le_trans h0 hf.1
    simp only [List.length_cons, List.prod_cons, pow_succ']
    exact ⟨mul_le_mul hf.1 hL.1 h1 h3, mul_le_mul hf.2 hL.2 h2 (by linarith)⟩

theorem one_add_pow_le (u : ℝ) (hu : 0 ≤ u) (k : ℕ) (hk : (k : ℝ) * u ≤ 1) :
    (1 + u) ^ k ≤ 1 + k * u + (k * u) ^ 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk' : (k : ℝ) * u ≤ 1 := by
      push_cast at hk; nlinarith
    have h := ih hk'
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    rw [pow_succ]
    push_cast
    have h1 : (1 + u) ^ k * (1 + u) ≤ (1 + k * u + (k * u) ^ 2) * (1 + u) :=
      mul_le_mul_of_nonneg_right h (by linarith)
    have h2 : (k : ℝ) * u * (k * u ^ 2) ≤ 1 * (k * u ^ 2) :=
      mul_le_mul_of_nonneg_right hk' (by positivity)
    nlinarith [sq_nonneg u]

theorem factor_bounds (N : ℝ) (hN : 2 ≤ N) (l : WLetter ℝ) (Y : ℝ) (h : N ^ 2 ≤ |Y - l.pt|) :
    1 - 1 / N ^ 2 ≤ wFactor l Y ∧ wFactor l Y ≤ 1 + 1 / (N ^ 2 - 1) := by
  obtain ⟨p, t, f⟩ := l
  have hN2 : 4 ≤ N ^ 2 := by nlinarith
  have hN2p : 0 < N ^ 2 := by linarith
  have hpos : 0 < N ^ 2 - 1 := by linarith
  have e1 : 0 ≤ 1 / N ^ 2 := (one_div_pos.2 hN2p).le
  have e2 : 0 ≤ 1 / (N ^ 2 - 1) := (one_div_pos.2 hpos).le
  have e3 : 1 / N ^ 2 ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
  replace h : N ^ 2 ≤ |Y - t| := h
  cases p <;> cases f <;> simp only [wFactor, if_true, Bool.false_eq_true, if_false]
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t + 1 := by linarith
      have hne : t - Y - 1 ≠ 0 := by
        intro e; linarith
      have e : (t - Y) / (t - Y - 1) = 1 - 1 / (Y - t + 1) := by
        field_simp
        ring
      have b1 : 1 / (Y - t + 1) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (Y - t + 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y - 1 := by linarith
      have e : (t - Y) / (t - Y - 1) = 1 + 1 / (t - Y - 1) := by
        field_simp
        ring
      have b1 : 1 / (t - Y - 1) ≤ 1 / (N ^ 2 - 1) := one_div_le_one_div_of_le hpos (by linarith)
      have b2 : 0 ≤ 1 / (t - Y - 1) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · have hsq : N ^ 2 ≤ (t - Y - 1) ^ 2 := by
      rcases le_abs.1 h with h | h
      · nlinarith
      · nlinarith
    have b1 : 1 / (t - Y - 1) ^ 2 ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p hsq
    have b2 : 0 ≤ 1 / (t - Y - 1) ^ 2 := by positivity
    constructor <;> linarith
  · rcases le_abs.1 h with h | h
    · have hx : 0 < Y - t := by linarith
      have e : (Y - t + 1) / (Y - t) = 1 + 1 / (Y - t) := by
        field_simp
      have b1 : 1 / (Y - t) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p h
      have b2 : 0 ≤ 1 / (Y - t) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
    · have hx : 0 < t - Y := by linarith
      have hne : Y - t ≠ 0 := by
        intro e; linarith
      have e : (Y - t + 1) / (Y - t) = 1 - 1 / (t - Y) := by
        field_simp
        ring
      have b1 : 1 / (t - Y) ≤ 1 / N ^ 2 := one_div_le_one_div_of_le hN2p (by linarith)
      have b2 : 0 ≤ 1 / (t - Y) := (one_div_pos.2 hx).le
      rw [e]
      constructor <;> linarith
  · constructor <;> linarith


end Formalism.FourierDecayAlt.P.ProductFactorBounds

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.F7 Formalism.FourierDecayAlt.P.ProductFactorBounds





end Formalism.FourierDecayAlt.P
