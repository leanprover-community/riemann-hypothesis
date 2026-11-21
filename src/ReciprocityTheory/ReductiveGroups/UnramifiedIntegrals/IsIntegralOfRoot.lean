import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModLatTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModHnf
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmForm
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGmQ

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem omegaK_sq (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs : (Complex.I * ((Real.sqrt d : ℝ) : ℂ)) ^ 2 = -(d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
    push_cast
    ring
  unfold omegaK
  linear_combination hs

theorem omegaK_lin {d : ℕ} (hd : 0 < d) {t n : ℤ} (h : (t : ℂ) * omegaK d + n = 0) :
    t = 0 ∧ n = 0 := by
  have h2 : (t : ℂ) * (1 + Complex.I * ((Real.sqrt d : ℝ) : ℂ)) + 2 * n = 0 := by
    rw [omegaK] at h
    linear_combination 2 * h
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have h3 : (((t : ℝ) + 2 * n : ℝ) : ℂ) + (((t : ℝ) * Real.sqrt d : ℝ) : ℂ) * Complex.I = 0 := by
    push_cast
    linear_combination h2
  have him : (t : ℝ) * Real.sqrt d = 0 := by
    have := congrArg Complex.im h3
    simpa using this
  have hre : (t : ℝ) + 2 * n = 0 := by
    have := congrArg Complex.re h3
    simpa using this
  have ht : (t : ℝ) = 0 := by
    rcases mul_eq_zero.mp him with h | h
    · exact h
    · exact absurd h hsq.ne'
  have hn : (n : ℝ) = 0 := by linarith
  exact ⟨by exact_mod_cast ht, by exact_mod_cast hn⟩

theorem cmPoint {d : ℕ} (hd : 0 < d) {L : PeriodPair} (hL : HasCMBy d L) {c : ℂ} {τ : ℍ}
    (h : IsTauOf L c τ) (x y : ℤ) :
    ∃ A B C D : ℤ, ((x : ℂ) + y * omegaK d) * τ = A * τ + B ∧ (x : ℂ) + y * omegaK d = C * τ + D ∧
      4 * (A * D - B * C) = 4 * x ^ 2 + 4 * x * y + y ^ 2 * (1 + d) := by
  obtain ⟨hc, hmem⟩ := h
  have hmul : ∀ w ∈ L.lattice, ((x : ℂ) + y * omegaK d) * w ∈ L.lattice := by
    intro w hw
    have h1 : (x : ℂ) * w ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem hw x
    have h2 : (y : ℂ) * (omegaK d * w) ∈ L.lattice := by
      rw [← zsmul_eq_mul]
      exact zsmul_mem (hL w hw) y
    have e : ((x : ℂ) + y * omegaK d) * w = (x : ℂ) * w + (y : ℂ) * (omegaK d * w) := by ring
    rw [e]
    exact add_mem h1 h2
  have hcτ : c * (τ : ℂ) ∈ L.lattice := (hmem _).2 ⟨1, 0, by push_cast; ring⟩
  have hc1 : c ∈ L.lattice := (hmem _).2 ⟨0, 1, by push_cast; ring⟩
  obtain ⟨A, B, hAB⟩ := (hmem _).1 (hmul _ hcτ)
  obtain ⟨C, D, hCD⟩ := (hmem _).1 (hmul _ hc1)
  have e1 : ((x : ℂ) + y * omegaK d) * τ = A * τ + B := by
    apply mul_left_cancel₀ hc
    linear_combination hAB
  have e2 : (x : ℂ) + y * omegaK d = C * τ + D := by
    apply mul_left_cancel₀ hc
    linear_combination hCD
  refine ⟨A, B, C, D, e1, e2, ?_⟩

  have key : ((x : ℂ) + y * omegaK d - A) * ((x : ℂ) + y * omegaK d - D) = B * C := by
    linear_combination ((x : ℂ) + y * omegaK d - A) * e2 + (C : ℂ) * e1
  have hω := omegaK_sq d
  obtain ⟨ht, hn⟩ := omegaK_lin hd (t := 8 * x * y + 4 * y ^ 2 - 4 * (A + D) * y)
    (n := 4 * x ^ 2 - y ^ 2 * (1 + d) - 4 * (A + D) * x + 4 * (A * D - B * C)) (by
      push_cast
      linear_combination 4 * key - (y : ℂ) ^ 2 * hω)
  by_cases hy : y = 0
  · subst hy
    simp only [Int.cast_zero, zero_mul, add_zero] at e1 e2
    have hτ : 0 < (τ : ℂ).im := τ.im_pos
    have e2' : (x : ℂ) - D = (C : ℂ) * τ := by linear_combination e2
    have e1' : ((x : ℂ) - A) * τ = (B : ℂ) := by linear_combination e1
    have hC : C = 0 := by
      have := congrArg Complex.im e2'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re] at this
      have h0 : (C : ℝ) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · exact_mod_cast h0
      · exact absurd h0 hτ.ne'
    have hA : A = x := by
      have := congrArg Complex.im e1'
      simp only [Complex.sub_im, Complex.intCast_im, Complex.mul_im, Complex.intCast_re,
        Complex.sub_re] at this
      have h0 : ((x : ℝ) - A) * (τ : ℂ).im = 0 := by linarith
      rcases mul_eq_zero.mp h0 with h0 | h0
      · have : (A : ℝ) = x := by linarith
        exact_mod_cast this
      · exact absurd h0 hτ.ne'
    subst hC hA
    have hD : D = A := by
      have : ((A : ℤ) : ℂ) = D := by linear_combination e2'
      exact_mod_cast this.symm
    subst hD
    ring
  · have h4 : 4 * (y * (2 * x + y - (A + D))) = 0 := by linear_combination ht
    have hs : 2 * x + y - (A + D) = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp h4).resolve_left (by norm_num))).resolve_left hy
    linear_combination hn - 4 * x * hs

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem fac_eq_zero_of_smul (t : ℕ × ℕ × ℕ) (τ : ℍ) (γ : SL(2, ℤ))
    (h : γ • pt t.1 t.2.1 t.2.2 τ = τ) : fac t τ = 0 := by
  unfold fac
  have h1 : AA τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * AA (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← AA_smul, h]
  have h2 : DD τ = denom γ (pt t.1 t.2.1 t.2.2 τ) ^ 12 * DD (pt t.1 t.2.1 t.2.2 τ) := by
    rw [← DD_smul, h]
  rw [h1, h2]
  ring

private lemma exists_SL2_mul_eq_Tmat_of_det_eq {m : ℕ} (hm : 0 < m) (A B C D : ℤ) (hdet : A * D - B * C = m) :
    ∃ g : SL(2, ℤ), ∃ s ∈ Tm m, 0 < s.2.2 ∧ (g : Matrix (Fin 2) (Fin 2) ℤ) * !![A, B; C, D] = Tmat s := by
  have hAC : A ≠ 0 ∨ C ≠ 0 := by
    by_contra hc
    push_neg at hc
    have h0 : (m : ℤ) = 0 := by rw [← hdet, hc.1, hc.2]; ring
    omega
  obtain ⟨G, hG⟩ : ∃ G : ℕ, G = Int.gcd A C := ⟨_, rfl⟩
  have hGpos : 0 < G := by
    rw [hG]
    first
    | exact Int.gcd_pos_iff.mpr hAC
    | (rcases hAC with h | h
       · exact Int.gcd_pos_of_ne_zero_left C h
       · exact Int.gcd_pos_of_ne_zero_right A h)
  obtain ⟨a0, ha0⟩ : (G : ℤ) ∣ A := by
    rw [hG]
    first | exact Int.gcd_dvd_left | exact Int.gcd_dvd_left A C | exact Int.gcd_dvd_left _ _
  obtain ⟨c0, hc0⟩ : (G : ℤ) ∣ C := by
    rw [hG]
    first | exact Int.gcd_dvd_right | exact Int.gcd_dvd_right A C | exact Int.gcd_dvd_right _ _
  obtain ⟨x, y, hbez⟩ : ∃ x y : ℤ, (G : ℤ) = A * x + C * y :=
    ⟨_, _, by rw [hG]; exact Int.gcd_eq_gcd_ab A C⟩
  have hG0 : (G : ℤ) ≠ 0 := by exact_mod_cast hGpos.ne'
  have h1 : a0 * x + c0 * y = 1 := by
    apply mul_left_cancel₀ hG0
    linear_combination -hbez - x * ha0 - y * hc0
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = a0 * D - c0 * B := ⟨_, rfl⟩
  have hGd : (G : ℤ) * d = m := by
    rw [hd]
    linear_combination hdet - D * ha0 + B * hc0
  have hdpos : 0 < d := by
    have h2 : 0 < (G : ℤ) * d := by rw [hGd]; exact_mod_cast hm
    have h3 : (0 : ℤ) < G := by exact_mod_cast hGpos
    by_contra h4
    push_neg at h4
    nlinarith
  obtain ⟨q, b, hdiv, hb0, hbd⟩ : ∃ q b : ℤ, d * q + b = x * B + y * D ∧ 0 ≤ b ∧ b < d :=
    ⟨(x * B + y * D) / d, (x * B + y * D) % d,
      (by first
          | (have h5 := Int.emod_add_ediv (x * B + y * D) d; linarith)
          | (have h5 := Int.ediv_add_emod' (x * B + y * D) d; linarith)
          | (have h5 := Int.mul_ediv_add_emod (x * B + y * D) d; linarith)), Int.emod_nonneg _ hdpos.ne',
      Int.emod_lt_of_pos _ hdpos⟩
  have hdet1 : (x + q * c0) * a0 - (y - q * a0) * -c0 = 1 := by linear_combination h1
  have e1 : (x + q * c0) * A + (y - q * a0) * C = (G : ℤ) := by
    linear_combination -hbez + q * c0 * ha0 - q * a0 * hc0
  have e2 : (x + q * c0) * B + (y - q * a0) * D = b := by
    linear_combination -hdiv + q * hd
  have e3 : -c0 * A + a0 * C = 0 := by
    linear_combination -c0 * ha0 + a0 * hc0
  have e4 : -c0 * B + a0 * D = d := by
    linear_combination -hd
  lift d to ℕ using hdpos.le
  lift b to ℕ using hb0
  have hGdn : G * d = m := by exact_mod_cast hGd
  have hmd : m / G = d := by rw [← hGdn, Nat.mul_div_cancel_left _ hGpos]
  refine ⟨⟨!![x + q * c0, y - q * a0; -c0, a0], by rw [Matrix.det_fin_two_of]; exact hdet1⟩, (G, b, d), ?_, by show 0 < d; exact_mod_cast hdpos, ?_⟩
  · simp only [Tm, Finset.mem_image, Finset.mem_sigma, Nat.mem_divisors, Finset.mem_range]
    refine ⟨⟨G, b⟩, ⟨⟨⟨d, hGdn.symm⟩, hm.ne'⟩, ?_⟩, ?_⟩
    · rw [hmd]; exact_mod_cast hbd
    · simp [hmd]
  · show !![x + q * c0, y - q * a0; -c0, a0] * !![A, B; C, D] = Tmat (G, b, d)
    rw [Matrix.mul_fin_two, e1, e2, e3, e4]
    all_goals first | rfl | (unfold Tmat; rfl) | simp [Tmat]

theorem Gm_vanish {m : ℕ} (hm : 0 < m) (τ : ℍ) (A B C D : ℤ) (hdet : A * D - B * C = m)
    (hfix : (A : ℂ) * τ + B = τ * (C * τ + D)) : Gm m τ = 0 := by
  obtain ⟨g, s, hs, he, hgs⟩ := exists_SL2_mul_eq_Tmat_of_det_eq hm A B C D hdet
  obtain ⟨p, q, r, w, hg⟩ : ∃ p q r w : ℤ, (g : Matrix (Fin 2) (Fin 2) ℤ) = !![p, q; r, w] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hdg : p * w - q * r = 1 := by
    have h0 := Matrix.SpecialLinearGroup.det_coe g
    rw [hg, Matrix.det_fin_two_of] at h0
    exact h0
  have hp : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = p := by rw [hg]; rfl
  have hq : (g : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = q := by rw [hg]; rfl
  have hr : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = r := by rw [hg]; rfl
  have hw : (g : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = w := by rw [hg]; rfl
  rw [hg] at hgs
  unfold Tmat at hgs
  rw [Matrix.mul_fin_two] at hgs
  have e00 : p * A + q * C = ((s.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 0
  have e01 : p * B + q * D = ((s.2.1 : ℕ) : ℤ) := congrFun (congrFun hgs 0) 1
  have e10 : r * A + w * C = 0 := congrFun (congrFun hgs 1) 0
  have e11 : r * B + w * D = ((s.2.2 : ℕ) : ℤ) := congrFun (congrFun hgs 1) 1
  have ea : (s.1 : ℂ) = p * A + q * C := by exact_mod_cast e00.symm
  have eb : (s.2.1 : ℂ) = p * B + q * D := by exact_mod_cast e01.symm
  have ez : (r : ℂ) * A + w * C = 0 := by exact_mod_cast e10
  have ee : (s.2.2 : ℂ) = r * B + w * D := by exact_mod_cast e11.symm
  have hE : (s.2.2 : ℂ) ≠ 0 := by exact_mod_cast he.ne'
  have hden : (r : ℂ) * τ + w ≠ 0 := by
    intro h0
    have him : (r : ℝ) * τ.im = 0 := by
      have h3 := congrArg Complex.im h0
      simpa using h3
    have hτ := τ.im_pos
    have hr0 : r = 0 := by
      rcases mul_eq_zero.mp him with h4 | h4
      · exact_mod_cast h4
      · linarith
    rw [hr0] at h0
    have hw0 : w = 0 := by
      have h3 := congrArg Complex.re h0
      simp at h3
      exact_mod_cast h3
    rw [hr0, hw0] at hdg
    simp at hdg
  have c1 : ∀ z : ℤ, (((algebraMap ℤ ℝ) z : ℝ) : ℂ) = (z : ℂ) := by
    intro z
    rw [eq_intCast]
    push_cast
    rfl
  have hform : ((g • τ : ℍ) : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom,
      UpperHalfPlane.σ, hp, hq, hr, hw]
    try rw [c1 p, c1 q, c1 r, c1 w]
  have hX : ((s.1 : ℂ) * τ + (s.2.1 : ℂ)) / (s.2.2 : ℂ) = ((p : ℂ) * τ + q) / ((r : ℂ) * τ + w) := by
    rw [div_eq_div_iff hE hden]
    linear_combination ((τ : ℂ) * (r * τ + w)) * ea + ((r : ℂ) * τ + w) * eb
      + ((p : ℂ) * (r * τ + w) - (p * τ + q) * r) * hfix + ((p : ℂ) * τ + q) * τ * ez
      - ((p : ℂ) * τ + q) * ee
  have hpt : pt s.1 s.2.1 s.2.2 τ = g • τ := by
    unfold pt
    rw [hX, ← hform]
    first
    | exact UpperHalfPlane.ofComplex_apply (g • τ)
    | simp
  unfold Gm
  apply Finset.prod_eq_zero hs
  apply fac_eq_zero_of_smul s τ g⁻¹
  rw [hpt, inv_smul_smul]

end ReciprocityTheory.ChartRestriction.L1
end
end

section
noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem isIntegral_of_root {P : Polynomial ℂ} (hP : ∀ i, IsIntegral ℤ (P.coeff i))
    (hu : IsIntegral ℤ (P.leadingCoeff)⁻¹) (h0 : P.leadingCoeff ≠ 0) {x : ℂ} (hx : P.eval x = 0) :
    IsIntegral ℤ x := by
  have hmon : (Polynomial.C (P.leadingCoeff)⁻¹ * P).Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ h0)
  have hdeg : (Polynomial.C (P.leadingCoeff)⁻¹ * P).natDegree ≠ 0 := by
    rw [Polynomial.natDegree_C_mul (inv_ne_zero h0)]
    intro hd
    rw [Polynomial.eq_C_of_natDegree_eq_zero hd, Polynomial.eval_C] at hx
    apply h0
    rw [Polynomial.leadingCoeff, hd]
    exact hx
  refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hmon hdeg ?_ ?_
  · rw [Polynomial.eval_mul, hx, mul_zero]
    exact isIntegral_zero
  · intro i
    rw [Polynomial.coeff_C_mul]
    exact hu.mul (hP i)

theorem jT_isIntegral {m : ℕ} (hm : 0 < m) (hsq : ¬ IsSquare m) {τ : ℍ} (h : Gm m τ = 0) :
    IsIntegral ℤ (jT τ) := by
  obtain ⟨n0, u, hu1, hu2, hu3, hlow, hcoef⟩ := gmQ_low hm hsq
  have hmf : IsMF (12 * ((2 * (Tm m).card : ℕ) : ℤ)) (Gm m) :=
    (gmForm hm).congr_weight (by push_cast; ring)
  obtain ⟨P, hPR, -, hlead, hval⟩ := qPrin_low (Rm m) _ (Gm m) hmf (gmQ_coeffIn hm) n0 u hu3 hlow hcoef
  have h1 := hval τ
  rw [h] at h1
  have h2 : P.eval (jT τ) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 (pow_ne_zero _ (DD_ne_zero τ))
    · exact h3
  exact isIntegral_of_root (fun i => Rm_isIntegral hm (hPR i)) (by rw [hlead]; exact Rm_isIntegral hm hu2)
    (by rw [hlead]; exact hu3) h2

theorem cm1 : JInvariantIntegrality := by
  intro d L hsf hd4 hL
  obtain ⟨c, τ, hτ⟩ := latTau L
  have hd : 0 < d := by omega
  obtain ⟨A, B, C, D, h1, h2, h3⟩ := cmPoint hd hL hτ (-1) 2
  rw [jInv_eq_jT hτ]
  refine jT_isIntegral hd ?_ (Gm_vanish hd τ A B C D (by linarith) ?_)
  · rintro ⟨r, hr⟩
    have : r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 := by omega
    rcases this with h | h | h | h <;> simp [hr, Nat.mul_mod, h] at hd4
  · rw [← h1, h2]; ring

end ReciprocityTheory.ChartRestriction.L1
end
end
