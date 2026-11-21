import Formalism.HermitianCurvature.LevelRecursionCondNeeded
import Mathlib

namespace Formalism.FourierDecayAlt.P.LevelGrowthBounds

open Finset Real

lemma geom_le (a : ℝ) (h0 : 0 ≤ a) (h1 : a ≤ 1/2) :
    ∀ i : ℕ, ∑ t ∈ Icc 2 i, a ^ (t-1) ≤ 2 * a := by
  have aux : ∀ k : ℕ, ∑ t ∈ Icc 2 (k+1), a ^ (t-1) + 2 * a ^ (k+1) ≤ 2 * a := by
    intro k
    induction k with
    | zero =>
      rw [Finset.Icc_eq_empty (by norm_num)]
      simp
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have e : k + 1 + 1 - 1 = k + 1 := by omega
      rw [e]
      have hp := pow_nonneg h0 (k+1)
      have hs : a ^ (k + 1 + 1) = a ^ (k+1) * a := pow_succ a (k+1)
      rw [hs]
      nlinarith [mul_le_mul_of_nonneg_left h1 hp]
  intro i
  rcases i with _ | k
  · rw [Finset.Icc_eq_empty (by norm_num)]; simp; linarith
  · have := aux k
    have hp := pow_nonneg h0 (k+1)
    linarith

noncomputable def Pp (e : ℕ → ℝ) (i : ℕ) : ℝ := ∏ l ∈ Icc 1 i, √(1 + e l)

lemma Pp_zero (e : ℕ → ℝ) : Pp e 0 = 1 := by
  simp [Pp]

lemma Pp_succ (e : ℕ → ℝ) (i : ℕ) : Pp e (i+1) = Pp e i * √(1 + e (i+1)) := by
  unfold Pp
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma one_le_sqrt_e {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (l : ℕ) : (1:ℝ) ≤ √(1 + e l) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + e l by linarith [he l])
  rwa [Real.sqrt_one] at this

lemma one_le_Pp {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : ∀ i, 1 ≤ Pp e i := by
  intro i
  induction i with
  | zero => rw [Pp_zero]
  | succ k ih =>
    rw [Pp_succ]
    have := one_le_sqrt_e he (k+1)
    nlinarith

lemma Pp_nonneg {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) (i : ℕ) : 0 ≤ Pp e i :=
  le_trans zero_le_one (one_le_Pp he i)

lemma Pp_mono {e : ℕ → ℝ} (he : ∀ i, 0 ≤ e i) : Monotone (Pp e) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [Pp_succ]
  exact le_mul_of_one_le_right (Pp_nonneg he n) (one_le_sqrt_e he (n+1))


lemma growth (r : ℕ) (ε δ : ℝ) (e a : ℕ → ℝ) (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (hδ2 : δ ≤ 1/2)
    (he : ∀ i, 0 ≤ e i) (ha : ∀ i, 0 ≤ a i)
    (hrec : ∀ i, 1 ≤ i → i ≤ r + 1 →
      a i ≤ √(1 + e i) * ((1 + ε) * a (i - 1) + ∑ s ∈ Icc 2 i, δ ^ (s - 1) * a (i - s))) :
    ∀ i, i ≤ r + 1 → a i ≤ (1 + (ε + 2 * δ)) ^ i * Pp e i * a 0 := by
  set ρ : ℝ := 1 + (ε + 2 * δ) with hρdef
  have hρ : (1:ℝ) ≤ ρ := by rw [hρdef]; linarith
  have hρ0 : (0:ℝ) ≤ ρ := by linarith
  have ha0 := ha 0
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases i with _ | k
    · simp [Pp_zero]
    · have h1 := hrec (k+1) (by omega) hi
      simp only [Nat.add_sub_cancel] at h1
      have hB : 0 ≤ ρ ^ k * Pp e k * a 0 :=
        mul_nonneg (mul_nonneg (pow_nonneg hρ0 _) (Pp_nonneg he _)) ha0
      have hsum : ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s) ≤
          2 * δ * (ρ ^ k * Pp e k * a 0) := by
        calc ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)
            ≤ ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * (ρ ^ k * Pp e k * a 0) := by
              apply Finset.sum_le_sum
              intro s hs
              have hs' := Finset.mem_Icc.mp hs
              apply mul_le_mul_of_nonneg_left _ (pow_nonneg hδ _)
              calc a (k+1-s) ≤ ρ ^ (k+1-s) * Pp e (k+1-s) * a 0 := ih _ (by omega) (by omega)
                _ ≤ ρ ^ k * Pp e k * a 0 := by
                  apply mul_le_mul_of_nonneg_right _ ha0
                  exact mul_le_mul (pow_le_pow_right₀ hρ (by omega)) (Pp_mono he (by omega))
                    (Pp_nonneg he _) (pow_nonneg hρ0 _)
          _ = (∑ s ∈ Icc 2 (k+1), δ ^ (s-1)) * (ρ ^ k * Pp e k * a 0) := by
              rw [Finset.sum_mul]
          _ ≤ 2 * δ * (ρ ^ k * Pp e k * a 0) :=
              mul_le_mul_of_nonneg_right (geom_le δ hδ hδ2 _) hB
      have h3 := ih k (by omega) (by omega)
      have hs1 : 0 ≤ √(1 + e (k+1)) := Real.sqrt_nonneg _
      have hc : (0:ℝ) ≤ 1 + ε := by linarith
      calc a (k+1) ≤ √(1 + e (k+1)) * ((1 + ε) * a k +
            ∑ s ∈ Icc 2 (k+1), δ ^ (s-1) * a (k+1-s)) := h1
        _ ≤ √(1 + e (k+1)) * ((1 + ε) * (ρ ^ k * Pp e k * a 0) +
            2 * δ * (ρ ^ k * Pp e k * a 0)) :=
            mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h3 hc) hsum) hs1
        _ = ρ ^ (k+1) * Pp e (k+1) * a 0 := by rw [Pp_succ, pow_succ, hρdef]; ring

lemma pow_bound (r : ℕ) (η : ℝ) (hη : 0 ≤ η) (hx : ((r:ℝ) + 1) * η ≤ 1 / 2) :
    ((1 + η) ^ (r+1)) ^ 2 ≤ 1 + 4 * ((r:ℝ) + 1) * η := by
  have hx0 : 0 ≤ ((r:ℝ) + 1) * η := by positivity
  have h1 : 1 + η ≤ Real.exp η := by
    have := Real.add_one_le_exp η; linarith
  have h2 : ((1 + η) ^ (r+1)) ^ 2 ≤ Real.exp (2 * (((r:ℝ) + 1) * η)) := by
    rw [← pow_mul]
    have h3 : Real.exp (2 * (((r:ℝ) + 1) * η)) = Real.exp η ^ ((r+1) * 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3]
    exact pow_le_pow_left₀ (by linarith) h1 _
  have hy0 : 0 ≤ 2 * (((r:ℝ) + 1) * η) := by linarith
  have hE := Real.abs_exp_sub_one_le (x := 2 * (((r:ℝ) + 1) * η))
    (by rw [abs_of_nonneg hy0]; linarith)
  rw [abs_of_nonneg hy0] at hE
  have hE' := le_abs_self (Real.exp (2 * (((r:ℝ) + 1) * η)) - 1)
  nlinarith

lemma half_bound (r : ℕ) (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ 1 / 8) (hr : (r:ℝ) * (12 * u) ≤ 1) :
    ((r:ℝ) + 1) * (3 * u) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp; linarith
  · have h1 : (1:ℝ) ≤ r := by exact_mod_cast h
    nlinarith [mul_le_mul_of_nonneg_right h1 hu0]

end Formalism.FourierDecayAlt.P.LevelGrowthBounds

namespace Formalism.FourierDecayAlt.P

open Finset Real Formalism.FourierDecayAlt.P.LevelGrowthBounds






end Formalism.FourierDecayAlt.P
