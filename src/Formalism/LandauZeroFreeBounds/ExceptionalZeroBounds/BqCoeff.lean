import Formalism.LandauZeroFreeBounds.SameCharacterLFunctionOne

section
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma convolution_nonneg_of_divisors (f g : ArithmeticFunction ℂ) (n : ℕ)
    (hf : ∀ d, d ∣ n → 0 ≤ f d) (hg : ∀ d, d ∣ n → 0 ≤ g d) : 0 ≤ (f * g) n := by
  rw [mul_apply]
  refine Finset.sum_nonneg fun x hx => ?_
  have h := (Nat.mem_divisorsAntidiagonal.1 hx).1
  exact mul_nonneg (hf _ (Dvd.intro _ h)) (hg _ (Dvd.intro_left _ h))

lemma character_convolution_eq {N N' M : ℕ} (χ : DirichletCharacter ℂ N) (χ' : DirichletCharacter ℂ N')
    (ψ : DirichletCharacter ℂ M) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    (n : ℕ) :
    (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) * toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M))) n
      = χ' (n : ZMod N') * DirichletCharacter.zetaMul χ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [mul_apply, Nat.sum_divisorsAntidiagonal' (fun a b => toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) a *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)) b), DirichletCharacter.zetaMul,
    coe_zeta_mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hdvd : i ∣ n := Nat.dvd_of_mem_divisors hi
  have hi0 : i ≠ 0 := (Nat.pos_of_mem_divisors hi).ne'
  have hni : n / i ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd) (Nat.pos_of_ne_zero hi0)).ne'
  simp only [toArithmeticFunction, coe_mk, hi0, hni, if_false]
  rw [hψ i]
  calc χ' ((n / i : ℕ) : ZMod N') * (χ (i : ZMod N) * χ' (i : ZMod N'))
      = (χ' ((n / i : ℕ) : ZMod N') * χ' (i : ZMod N')) * χ (i : ZMod N) := by ring
    _ = χ' (n : ZMod N') * χ (i : ZMod N) := by
      rw [← map_mul, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

set_option backward.isDefEq.respectTransparency.types false in

lemma prime_power_coefficient_nonneg {N N' M : ℕ} {χ : DirichletCharacter ℂ N} {χ' : DirichletCharacter ℂ N'}
    {ψ : DirichletCharacter ℂ M} (hχ : χ ^ 2 = 1) (hψ : ∀ n : ℕ, ψ (n : ZMod M) = χ (n : ZMod N) * χ' (n : ZMod N'))
    {p : ℕ} (hp : p.Prime)
    (hc : χ' (p : ZMod N') = 0 ∨ χ' (p : ZMod N') = 1 ∨ (χ' (p : ZMod N') = -1 ∧ χ (p : ZMod N) = -1))
    (k : ℕ) :
    0 ≤ (DirichletCharacter.zetaMul χ * (toArithmeticFunction (fun m : ℕ => χ' (m : ZMod N')) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod M)))) (p ^ k) := by
  have hζ : ∀ j, DirichletCharacter.zetaMul χ (p ^ j) = ∑ i ∈ Finset.range (j + 1), χ (p : ZMod N) ^ i := by
    intro j
    rw [DirichletCharacter.zetaMul, coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [toArithmeticFunction, hp.ne_zero]
  apply convolution_nonneg_of_divisors
  · intro d _
    exact DirichletCharacter.zetaMul_nonneg hχ d
  · intro d hd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [character_convolution_eq χ χ' ψ hψ, Nat.cast_pow, map_pow]
    rcases hc with h | h | ⟨h, h'⟩
    · exact mul_nonneg (by rw [h]; exact pow_nonneg le_rfl j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · exact mul_nonneg (by rw [h]; exact pow_nonneg zero_le_one j) (DirichletCharacter.zetaMul_nonneg hχ _)
    · rw [h, hζ, h', neg_one_geom_sum]
      split_ifs with he
      · simp
      · have hj : Even j := by
          rcases Nat.even_or_odd j with hj | hj
          · exact hj
          · exact absurd hj.add_one he
        rw [hj.neg_one_pow]
        norm_num

end Formalism.ZeroFreeDirichlet
end
end

section
open Complex ArithmeticFunction
open scoped ComplexOrder LSeries.notation

noncomputable section

namespace Formalism.ZeroFreeDirichlet

lemma dirichlet_character_lseries_summable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s := by
  refine (LSeriesSummable_congr s (fun {n} hn => ?_)).mpr (χ.LSeriesSummable_of_one_lt_re hs)
  simp [toArithmeticFunction, hn]

lemma dirichlet_character_lseries_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries ⇑(toArithmeticFunction (fun m : ℕ => χ (m : ZMod N))) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact LSeries_congr (fun {n} hn => by simp [toArithmeticFunction, hn]) s

set_option backward.isDefEq.respectTransparency.types false in
lemma lseries_zetaMul_eq {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) :
    LSeries (DirichletCharacter.zetaMul χ) s = riemannZeta s * DirichletCharacter.LFunction χ s := by
  have h1 : LSeriesSummable ⇑(ArithmeticFunction.zeta : ArithmeticFunction ℂ) s := by
    have := ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs
    exact (LSeriesSummable_congr s (fun {n} hn => by simp [hn])).mp this
  rw [DirichletCharacter.zetaMul, ArithmeticFunction.LSeries_mul' h1 (dirichlet_character_lseries_summable χ hs),
    dirichlet_character_lseries_eq χ hs]
  congr 1
  rw [← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs]
  exact LSeries_congr (fun {n} hn => by simp [hn]) s

theorem dirichlet_product_coefficients : BqCoeff := by
  intro q₁ q₂ _ _ _ χ₁ χ₂ ψ h1 h2 hψ
  set f : ArithmeticFunction ℂ := DirichletCharacter.zetaMul χ₁ *
    (toArithmeticFunction (fun m : ℕ => χ₂ (m : ZMod q₂)) *
      toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) with hf

  have hvals : ∀ {N : ℕ} (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 →
      ∀ x, χ x = 0 ∨ χ x = 1 ∨ χ x = -1 := by
    intro N χ hχ x
    by_cases hx : IsUnit x
    · have h := congrArg (fun φ : DirichletCharacter ℂ N => φ x) hχ
      simp only [MulChar.pow_apply' χ two_ne_zero, MulChar.one_apply hx] at h
      have h' : χ x * χ x = 1 := by rw [← sq]; exact h
      rcases (mul_self_eq_one_iff).mp h' with h' | h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr h')
    · exact Or.inl (MulChar.map_nonunit χ hx)
  have hmul : f.IsMultiplicative :=
    (DirichletCharacter.isMultiplicative_zetaMul χ₁).mul
      ((DirichletCharacter.isMultiplicative_toArithmeticFunction χ₂).mul
        (DirichletCharacter.isMultiplicative_toArithmeticFunction ψ))
  have hswap : f = DirichletCharacter.zetaMul χ₂ *
      (toArithmeticFunction (fun m : ℕ => χ₁ (m : ZMod q₁)) *
        toArithmeticFunction (fun m : ℕ => ψ (m : ZMod (q₁ * q₂)))) := by
    simp only [hf, DirichletCharacter.zetaMul]
    ring
  have hψ' : ∀ n : ℕ, ψ (n : ZMod (q₁ * q₂)) = χ₂ (n : ZMod q₂) * χ₁ (n : ZMod q₁) := by
    intro n
    rw [hψ n, mul_comm]
  have hpp : ∀ p k : ℕ, p.Prime → 0 ≤ f (p ^ k) := by
    intro p k hp
    rcases hvals χ₂ h2 (p : ZMod q₂) with h | h | h
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inl h) k
    · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inl h)) k
    · rcases hvals χ₁ h1 (p : ZMod q₁) with h' | h' | h'
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inl h') k
      · rw [hswap]; exact prime_power_coefficient_nonneg h2 hψ' hp (Or.inr (Or.inl h')) k
      · exact prime_power_coefficient_nonneg h1 hψ hp (Or.inr (Or.inr ⟨h, h'⟩)) k
  have hnn : ∀ n, 0 ≤ f n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [ArithmeticFunction.IsMultiplicative.multiplicative_factorization f hmul hn, Finsupp.prod]
      exact Finset.prod_nonneg fun p hp =>
        hpp p _ (Nat.prime_of_mem_primeFactors (by simpa using hp))
  have hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable (⇑f) s := fun s hs =>
    ArithmeticFunction.LSeriesSummable_mul (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs))
  refine ⟨⇑f, hnn, hmul.map_one, ?_, ?_⟩
  · have := LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable (f := ⇑f) (x := 1)
      (fun y hy => hsum y (by simpa using hy))
    simpa using this
  · intro s hs
    rw [Fbq, ArithmeticFunction.LSeries_mul' (DirichletCharacter.LSeriesSummable_zetaMul χ₁ hs)
      (ArithmeticFunction.LSeriesSummable_mul (dirichlet_character_lseries_summable χ₂ hs)
        (dirichlet_character_lseries_summable ψ hs)),
      ArithmeticFunction.LSeries_mul' (dirichlet_character_lseries_summable χ₂ hs) (dirichlet_character_lseries_summable ψ hs),
      lseries_zetaMul_eq χ₁ hs, dirichlet_character_lseries_eq χ₂ hs, dirichlet_character_lseries_eq ψ hs]
    ring

end Formalism.ZeroFreeDirichlet
end
end
