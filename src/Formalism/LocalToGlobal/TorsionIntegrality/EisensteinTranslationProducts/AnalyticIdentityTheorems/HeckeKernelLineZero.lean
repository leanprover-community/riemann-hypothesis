import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.HkRowIntegral

noncomputable section
open scoped BigOperators ComplexConjugate Topology
open Filter MeasureTheory

namespace Formalism.L2.Th1.F

namespace Hk3


lemma integrable_J {a : ℝ} (ha : 1 / 2 < a) : Integrable (fun t : ℝ => (1 + t ^ 2) ^ (-a)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume) (r := 2 * a)
    (by simp; linarith)
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only [Real.norm_eq_abs, sq_abs]
  congr 1
  ring



lemma tendsto_top : Tendsto (fun t : ℝ => 1 + t ^ 2) atTop atTop :=
  tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop (by norm_num))

lemma tendsto_bot : Tendsto (fun t : ℝ => 1 + t ^ 2) atBot atTop := by
  have := tendsto_top.comp tendsto_neg_atBot_atTop
  simpa [Function.comp_def] using this



lemma J_one : hkJ 1 = Real.pi := by
  unfold hkJ
  rw [← integral_univ_inv_one_add_sq]
  congr 1
  ext t
  rw [Real.rpow_neg_one]


end Hk3


namespace Hk3



end Hk3


namespace Hk3

lemma tsum_abs_int {b : ℝ} (hb : 1 < b) :
    ∑' n : ℤ, |(n : ℝ)| ^ (-b) = 2 * ∑' n : ℕ, 1 / (n : ℝ) ^ b := by
  have hs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ b) := Real.summable_one_div_nat_rpow.mpr hb
  have e1 : (fun n : ℕ => |((n : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n), Real.rpow_neg (Nat.cast_nonneg n),
      one_div]
  have e2 : (fun n : ℕ => |((-(n : ℤ) : ℤ) : ℝ)| ^ (-b)) = fun n : ℕ => 1 / (n : ℝ) ^ b := by
    ext n
    rw [Int.cast_neg, abs_neg, Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n),
      Real.rpow_neg (Nat.cast_nonneg n), one_div]
  rw [Summable.tsum_of_nat_of_neg (f := fun n : ℤ => |(n : ℝ)| ^ (-b)) (by rw [e1]; exact hs)
    (by rw [e2]; exact hs), e1, e2, Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
  ring

lemma term_eq (hv : HkIntValue) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) (n : ℤ) :
    (if n = 0 then 0 else hkInt τ s n) =
      ((|(n : ℝ)| ^ (-(1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (hkJ (1 + s) - 2 * hkJ (2 + s))) : ℝ) : ℂ) := by
  split_ifs with h
  · subst h
    rw [Int.cast_zero, abs_zero, Real.zero_rpow (by linarith)]
    simp
  · rw [hv τ s n hτ hs h, Real.mul_rpow (abs_nonneg _) (abs_nonneg _), mul_assoc]

lemma K_eq (hj : HkJRules) {s : ℝ} (hs : 0 < s) :
    hkJ (1 + s) - 2 * hkJ (2 + s) = -(s / (s + 1)) * hkJ (1 + s) := by
  have h := hj.1 (1 + s) (by linarith)
  have e : 1 + s + 1 = 2 + s := by ring
  rw [e] at h
  rw [h]
  have h1 : s + 1 ≠ 0 := by linarith
  have h2 : 1 + s ≠ 0 := by linarith
  field_simp
  ring

lemma tsum_eq (hv : HkIntValue) (hj : HkJRules) {τ : ℂ} (hτ : τ.im ≠ 0) {s : ℝ} (hs : 0 < s) :
    (∑' n : ℤ, if n = 0 then 0 else hkInt τ s n) =
      (((((1 + 2 * s) - 1) * ∑' n : ℕ, 1 / (n : ℝ) ^ (1 + 2 * s)) *
        (|τ.im| ^ (-(1 + 2 * s)) * (-(1 / (s + 1)) * hkJ (1 + s))) : ℝ) : ℂ) := by
  simp_rw [term_eq hv hτ hs]
  rw [← Complex.ofReal_tsum, tsum_mul_right, tsum_abs_int (by linarith), K_eq hj hs]
  congr 1
  ring


end Hk3


end Formalism.L2.Th1.F
