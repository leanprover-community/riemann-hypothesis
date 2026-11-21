import Formalism.NormUnitaryBounds.Statement

section
open MeasureTheory Complex

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures

lemma integral_exp_int (k : ℤ) :
    ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi), Complex.exp ((k : ℂ) * I * (θ : ℂ)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hk
  · subst hk; simp
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((k : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; push_cast; ring
    rw [h1]; simp

abbrev mu1 : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))

abbrev muT (G : ℕ) : Measure (Fin G → ℝ) := Measure.pi (fun _ : Fin G => mu1)

lemma muT_real_univ (G : ℕ) : (muT G).real Set.univ = (2 * Real.pi) ^ G := by
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod]
  simp [Real.volume_Ioc, Real.pi_pos.le]

theorem cauchy_torus (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (r : Fin G → ℝ) (B : ℝ)
    (hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤ B)
    (e : Fin G → ℕ) : ‖c e‖ * ∏ i, |r i| ^ e i ≤ B := by
  set zθ : (Fin G → ℝ) → Fin G → ℂ := fun θ i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I) with hzθ
  set w : (Fin G → ℝ) → ℂ := fun θ => ∏ i, Complex.exp (-(e i : ℂ) * I * (θ i : ℂ)) with hw
  set F : (Fin G → ℕ) → (Fin G → ℝ) → ℂ :=
    fun e' θ => c e' * (∏ i, zθ θ i ^ e' i) * w θ with hF
  set a : (Fin G → ℕ) → ℂ := fun e' => c e' * ∏ i, ((r i : ℂ)) ^ e' i with ha
  set k : (Fin G → ℕ) → Fin G → ℤ := fun e' i => (e' i : ℤ) - (e i : ℤ) with hk
  have key : ∀ e' θ, F e' θ = a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) := by
    intro e' θ
    simp only [hF, ha, hw, hzθ, hk]
    rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hnormexp : ∀ (m : ℤ) (t : ℝ), ‖Complex.exp ((m : ℂ) * I * (t : ℂ))‖ = 1 := by
    intro m t
    rw [Complex.norm_exp]; simp
  have hnormF : ∀ e' θ, ‖F e' θ‖ = ‖a e'‖ := by
    intro e' θ
    rw [key, norm_mul, norm_prod]
    simp [hnormexp]
  have hcont : ∀ e', Continuous (F e') := by
    intro e'
    have : F e' = fun θ => a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) :=
      funext (key e')
    rw [this]
    fun_prop
  have hint : ∀ e', Integrable (F e') (muT G) := by
    intro e'
    exact Integrable.of_bound (hcont e').aestronglyMeasurable ‖a e'‖
      (Filter.Eventually.of_forall fun θ => (hnormF e' θ).le)
  have hsumr : Summable a := (hΘ (fun i => (r i : ℂ))).summable
  have hsum : Summable fun e' => ∫ θ, ‖F e' θ‖ ∂(muT G) := by
    simp_rw [hnormF, integral_const, smul_eq_mul]
    exact (summable_norm_iff.mpr hsumr).mul_left _
  have htsum : ∀ θ, ∑' e', F e' θ = Θ (zθ θ) * w θ := fun θ => ((hΘ (zθ θ)).mul_right (w θ)).tsum_eq
  have hI : ∀ e', ∫ θ, F e' θ ∂(muT G) =
      a e' * ∏ i, (if k e' i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
    intro e'
    simp_rw [key]
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin G => mu1)
      (fun i (t : ℝ) => Complex.exp (((k e' i : ℤ) : ℂ) * I * (t : ℂ)))]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_exp_int (k e' i)
  have hmain : ∫ θ, Θ (zθ θ) * w θ ∂(muT G) = a e * ((2 * Real.pi : ℝ) : ℂ) ^ G := by
    simp_rw [← htsum]
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    rw [tsum_eq_single e]
    · rw [hI]; congr 1
      simp [hk]
    · intro e' he'
      rw [hI]
      obtain ⟨i, hi⟩ : ∃ i, e' i ≠ e i := by
        by_contra h; push Not at h; exact he' (funext h)
      have : k e' i ≠ 0 := by simp only [hk]; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg this), mul_zero]
  have hbound : ‖∫ θ, Θ (zθ θ) * w θ ∂(muT G)‖ ≤ B * (muT G).real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [norm_mul, hw, norm_prod]
    have : ∀ i ∈ Finset.univ, ‖Complex.exp (-(e i : ℂ) * I * (θ i : ℂ))‖ = 1 := by
      intro i _; rw [Complex.norm_exp]; simp
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, mul_one]
    exact hB θ
  rw [hmain, muT_real_univ, norm_mul, norm_pow] at hbound
  have h2pi : (0:ℝ) < (2 * Real.pi) ^ G := by positivity
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn2] at hbound
  have ha' : ‖a e‖ = ‖c e‖ * ∏ i, |r i| ^ e i := by
    simp only [ha, norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [← ha']
  exact le_of_mul_le_mul_right hbound h2pi

end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
end
end

section
open MeasureTheory Complex

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas

open ExponentialIntegralMeasures

lemma norm_sq_coeff_le_gaussian_growth (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (hS : ∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2))
    (e : Fin G → ℕ) :
    ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i ≤ S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
  set r : Fin G → ℝ := fun i => Real.sqrt (e i) with hr
  have hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤
      S * Real.exp ((∑ i, (e i : ℝ)) / 2) := by
    intro θ
    have h := hS (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))
    have hz : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2 = (e i : ℝ) := by
      intro i
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, hr, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [hz] at h
    exact h
  have h1 := cauchy_torus G Θ c hΘ r _ hB e
  have hr' : ∀ i, |r i| = Real.sqrt (e i) := fun i => abs_of_nonneg (Real.sqrt_nonneg _)
  simp only [hr'] at h1
  have h0 : 0 ≤ ‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have hl : (‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i) ^ 2 = ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i := by
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hrr : (S * Real.exp ((∑ i, (e i : ℝ)) / 2)) ^ 2 = S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  rw [hl, hrr] at h2
  exact h2

theorem gaussian_coefficient_bound_holds : N1 := by
  intro G Θ c S hΘ hS e
  have h := norm_sq_coeff_le_gaussian_growth G Θ c S hΘ hS e
  have hpos : 0 < ∏ i, ((e i : ℝ)) ^ e i := by
    apply Finset.prod_pos
    intro i _
    rcases Nat.eq_zero_or_pos (e i) with h0 | h0
    · rw [h0]; simp
    · positivity
  have hprod : ∏ i, (Real.exp 1 / (e i : ℝ)) ^ e i =
      Real.exp (∑ i, (e i : ℝ)) / ∏ i, ((e i : ℝ)) ^ e i := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Real.exp_sum]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.exp_nat_mul, mul_one]
  rw [hprod, ← mul_div_assoc, le_div_iff₀ hpos]
  exact h

end Formalism.NormUnitaryCountingLemmas
end
end
