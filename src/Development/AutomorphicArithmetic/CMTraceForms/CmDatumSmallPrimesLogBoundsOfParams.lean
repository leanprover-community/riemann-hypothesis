import Mathlib
import Formalism.LocalRingCardinality.DataParams
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.PrimeDiscriminants.SlopeTestRemainingChoices

section
theorem UpperTheory.sum_log_primeFactors_mul_two_add_logb_le :
    ∀ (Q : ℕ) (y : ℝ), Q ≠ 0 → 1 ≤ y → Real.log Q ≤ y →
      (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q) ≤ 11 * y ^ 4 := by
  intro Q y hQ hy hlog
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
  have hl0 : 0 ≤ Real.log Q := Real.log_nonneg hQ1
  have hpos : ∀ p ∈ Q.primeFactors, (0 : ℝ) < p := fun p hp => by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  have h1 : (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) ≤ y := by
    rw [← Real.log_prod (fun p hp => (hpos p hp).ne')]
    refine le_trans (Real.log_le_log (Finset.prod_pos hpos) ?_) hlog
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hQ) (Nat.prod_primeFactors_dvd Q)
    rw [← Nat.cast_prod]
    exact Nat.cast_le.mpr this
  have h2 : Real.logb 2 Q ≤ 2 * y := by
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    rw [Real.logb, div_le_iff₀ (by linarith)]
    nlinarith
  have h3 : 0 ≤ Real.logb 2 Q := Real.logb_nonneg (by norm_num) hQ1
  have h4 : y ^ 2 ≤ y ^ 4 := pow_le_pow_right₀ hy (by norm_num)
  calc (∑ p ∈ Q.primeFactors, Real.log (p : ℝ)) * (2 + Real.logb 2 Q)
      ≤ y * (2 + Real.logb 2 Q) := mul_le_mul_of_nonneg_right h1 (by linarith)
    _ ≤ y * (4 * y) := mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    _ ≤ 11 * y ^ 4 := by nlinarith
end

section
open NumberField Formalism.BasicNotions Formalism.HC

theorem UpperTheory.cmDatum_smallPrimes_log_bounds_of_params :
    ∀ (D : D7) (L : SizeData₂ D), ParameterChoice' D L →
      (∑ p ∈ D.host.small, Real.log (p : ℝ)) * (2 + Real.logb 2 D.host.QS) ≤ 11 * L.sc.L ∧ Real.log D.host.QS ≤ L.sc.x ^ (L.sc.eps / 4) := by
  intro D L P
  have hx : 0 < L.sc.x := lt_trans one_pos L.sc.one_lt_alt
  have hy : 1 ≤ L.sc.x ^ (L.sc.eps / 4) :=
    Real.one_le_rpow L.sc.one_lt_alt.le (by have := L.sc.eps_pos; positivity)
  have hQ0 : 0 < D.host.QS := D.host.QS_pos
  have hQn : D.host.QS ≤ D.R.n ^ 2 := D.host.QS_le
  have hnN : D.R.n ≤ D.R.N D.R.m := by
    have := D.R.f_le_k
    unfold Ranks.n Ranks.N
    omega
  have hm : (1 : ℝ) ≤ (D.R.m : ℝ) ^ 10 := by
    have : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (le_trans one_le_two D.R.two_le_m)
    exact one_le_pow₀ this
  have hN : (D.R.n : ℝ) ≤ (D.s.Del : ℝ) := by
    have h1 : (D.R.n : ℝ) ≤ (D.R.N D.R.m : ℝ) := by exact_mod_cast hnN
    have h2 := P.Del_ge.2.2.2
    have h3 : (D.R.N D.R.m : ℝ) ≤ (D.R.N D.R.m : ℝ) * (D.R.m : ℝ) ^ 10 :=
      le_mul_of_one_le_right (Nat.cast_nonneg _) hm
    linarith
  have hn0 : (0 : ℝ) < D.R.n := by
    have : 0 < D.R.n := by
      rcases Nat.eq_zero_or_pos D.R.n with h | h
      · rw [h] at hQn; omega
      · exact h
    exact_mod_cast this
  have hlog : Real.log D.host.QS ≤ L.sc.x ^ (L.sc.eps / 4) := by
    have h1 : Real.log D.host.QS ≤ Real.log ((D.R.n : ℝ) ^ 2) :=
      Real.log_le_log (by exact_mod_cast hQ0) (by exact_mod_cast hQn)
    rw [Real.log_pow] at h1
    have h2 := Real.log_le_log hn0 hN
    have h3 := P.logDel
    push_cast at h1
    linarith
  refine ⟨?_, hlog⟩
  have h4 : (L.sc.x ^ (L.sc.eps / 4)) ^ 4 = L.sc.L := by
    unfold Scale.L
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    congr 1
    push_cast
    ring
  have := UpperTheory.sum_log_primeFactors_mul_two_add_logb_le D.host.QS _ hQ0.ne' hy hlog
  rw [h4] at this
  exact this
end
