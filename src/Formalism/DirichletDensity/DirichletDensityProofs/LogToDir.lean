import Mathlib
import Formalism.DirichletDensity.Statement

open Filter Topology Set

noncomputable section

namespace Formalism.HF.P

lemma log_div_rpow_nonneg (n : ℕ) (x : ℝ) : 0 ≤ Real.log n / (n : ℝ) ^ x :=
  div_nonneg (Real.log_natCast_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) x)

lemma summable_log_div_rpow {y : ℝ} (hy : 1 < y) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ y) := by
  set ε := (y - 1) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hs : Summable (fun n : ℕ => (1 / ε) * ((n : ℝ) ^ (y - ε))⁻¹) :=
    (Real.summable_nat_rpow_inv.2 (by rw [hε]; linarith)).mul_left _
  refine Summable.of_nonneg_of_le (fun n => log_div_rpow_nonneg n y) (fun n => ?_) hs
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero, zero_div]
    exact mul_nonneg (div_nonneg zero_le_one hε0.le) (inv_nonneg.2 (Real.rpow_nonneg le_rfl _))
  · have hn' : (0:ℝ) < n := Nat.cast_pos.2 hn
    have h1 := Real.log_le_rpow_div hn'.le hε0
    have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos hn' y
    have hposε : 0 < (n:ℝ) ^ ε := Real.rpow_pos_of_pos hn' ε
    calc Real.log n / (n:ℝ) ^ y ≤ ((n:ℝ) ^ ε / ε) / (n:ℝ) ^ y := by gcongr
      _ = (1 / ε) * ((n:ℝ) ^ (y - ε))⁻¹ := by
        rw [Real.rpow_sub hn', inv_div]
        field_simp

lemma hasDerivAt_term (S : Set ℕ) (n : ℕ) (x : ℝ) :
    HasDerivAt (fun x : ℝ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n) x := by
  by_cases h : n ∈ {p : ℕ | p.Prime ∧ p ∈ S}
  · simp only [Set.indicator_of_mem h]
    have hn : (0:ℝ) < n := Nat.cast_pos.2 h.1.pos
    have h1 := (Real.hasStrictDerivAt_const_rpow hn x).hasDerivAt
    have h2 := h1.inv (Real.rpow_pos_of_pos hn x).ne'
    have hfun : (fun x : ℝ => 1 / (n:ℝ) ^ x) = fun x => ((n:ℝ) ^ x)⁻¹ := by
      funext z; exact one_div _
    have h3 : HasDerivAt (fun x : ℝ => ((n:ℝ) ^ x)⁻¹) (-((n:ℝ) ^ x * Real.log n) / ((n:ℝ) ^ x) ^ 2) x := h2
    rw [hfun]
    refine h3.congr_deriv ?_
    have : 0 < (n:ℝ) ^ x := Real.rpow_pos_of_pos hn x
    rw [neg_div, pow_two, mul_div_mul_left _ _ this.ne']
  · simp only [Set.indicator_of_notMem h, neg_zero]
    exact hasDerivAt_const x 0

lemma summable_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ x) n) := by
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) (Real.summable_nat_rpow_inv.2 hx)
  · exact Set.indicator_nonneg (fun m _ => by positivity) n
  · calc _ ≤ 1 / (n:ℝ) ^ x := Set.indicator_le_self' (fun m _ => by positivity) n
      _ = _ := one_div _

lemma hasDerivAt_F (S : Set ℕ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun x : ℝ => ∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator
        (fun m : ℕ => 1 / (m : ℝ) ^ x) n)
      (-∑' n : ℕ, {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ x) n)
      x := by
  set y := (1 + x) / 2 with hy
  have hy1 : 1 < y := by rw [hy]; linarith
  have hyx : y < x := by rw [hy]; linarith
  rw [← tsum_neg]
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => Real.log n / (n : ℝ) ^ y)
    (g := fun n z => {p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => 1 / (m : ℝ) ^ z) n)
    (g' := fun n z => -{p : ℕ | p.Prime ∧ p ∈ S}.indicator (fun m : ℕ => Real.log m / (m : ℝ) ^ z) n)
    (summable_log_div_rpow hy1) isOpen_Ioi isPreconnected_Ioi
    (fun n z _ => hasDerivAt_term S n z) (fun n z hz => ?_) (mem_Ioi.2 hyx) ?_ (mem_Ioi.2 hyx)
  · have hz' : y < z := mem_Ioi.1 hz
    rw [norm_neg, Real.norm_eq_abs,
      abs_of_nonneg (Set.indicator_nonneg (fun m _ => log_div_rpow_nonneg m z) n)]
    refine (Set.indicator_le_self' (fun m _ => log_div_rpow_nonneg m z) n).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hn1 : (1:ℝ) ≤ n := Nat.one_le_cast.2 hn
      have hpos : 0 < (n:ℝ) ^ y := Real.rpow_pos_of_pos (by linarith) y
      exact div_le_div_of_nonneg_left (Real.log_natCast_nonneg n) hpos
        (Real.rpow_le_rpow_of_exponent_le hn1 hz'.le)
  · exact summable_F S (by linarith)



end Formalism.HF.P

namespace Formalism.HF


end Formalism.HF
