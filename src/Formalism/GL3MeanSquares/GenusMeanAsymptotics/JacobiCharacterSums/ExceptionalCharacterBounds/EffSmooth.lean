import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffBase

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

open Finset
open scoped ComplexOrder

set_option backward.isDefEq.respectTransparency.types false in
theorem one_le_zetaMul_prime_pow_even {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {p : ℕ}
    (hp : p.Prime) (a : ℕ) : 1 ≤ DirichletCharacter.zetaMul χ (p ^ (2 * a)) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk,
    Nat.sum_divisors_prime_pow hp, pow_eq_zero_iff', hp.ne_zero, ne_eq, false_and, ↓reduceIte,
    Nat.cast_pow, map_pow]
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p with h | h | h
  · simp only [h, zero_geom_sum]
    simp
  · simp only [h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have : (1 : ℝ) ≤ ((2 * a + 1 : ℕ) : ℝ) := by
      push_cast
      have : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      linarith
    exact_mod_cast this
  · simp only [h, neg_one_geom_sum]
    have : ¬ Even (2 * a + 1) := by simp
    simp [this]

theorem one_le_zetaMul_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) (k : ℕ)
    (hk : k ≠ 0) : 1 ≤ DirichletCharacter.zetaMul χ (k ^ 2) := by
  rw [χ.isMultiplicative_zetaMul.multiplicative_factorization _ (pow_ne_zero 2 hk)]
  unfold Finsupp.prod
  calc (1 : ℂ) = ∏ _p ∈ (k ^ 2).factorization.support, (1 : ℂ) := by simp
    _ ≤ _ := by
      refine Finset.prod_le_prod (fun _ _ => zero_le_one) (fun p hp => ?_)
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (by simpa using hp)
      rw [Nat.factorization_pow]
      simpa using one_le_zetaMul_prime_pow_even hχ hpp (k.factorization p)

set_option backward.isDefEq.respectTransparency.types false in
theorem zetaMul_eq_sum {q : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    DirichletCharacter.zetaMul χ n = ∑ d ∈ n.divisors, χ (d : ZMod q) := by
  simp only [DirichletCharacter.zetaMul, toArithmeticFunction, ArithmeticFunction.coe_zeta_mul_apply,
    ArithmeticFunction.coe_mk]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  simp [this]



theorem regroup (N : ℕ) (F : ℕ → ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, ∑ m ∈ Icc 1 (N / d), F d (d * m) := by
  have h1 : ∀ n ∈ Icc 1 N, ∑ d ∈ n.divisors, F d n = ∑ d ∈ Icc 1 N, if d ∣ n then F d n else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
    constructor
    · rintro ⟨hdn, hn0⟩
      have := Nat.le_of_dvd (by omega) hdn
      have := Nat.pos_of_dvd_of_pos hdn (by omega)
      exact ⟨⟨by omega, by omega⟩, hdn⟩
    · rintro ⟨_, hdn⟩
      exact ⟨hdn, by omega⟩
  rw [Finset.sum_congr rfl h1, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [← Finset.sum_filter]
  have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
  symm
  refine Finset.sum_nbij (fun m => d * m) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro m hm
    simp only [Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    refine ⟨⟨Nat.mul_pos hd1 hm.1, ?_⟩, Dvd.intro _ rfl⟩
    calc d * m ≤ d * (N / d) := Nat.mul_le_mul_left d hm.2
      _ ≤ N := Nat.mul_div_le N d
  · intro a _ b _ hab
    exact Nat.eq_of_mul_eq_mul_left hd1 hab
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    obtain ⟨⟨hn1, hnN⟩, m, rfl⟩ := hn
    refine ⟨m, ?_, rfl⟩
    simp only [Finset.coe_Icc, Set.mem_Icc]
    refine ⟨Nat.pos_of_ne_zero (by rintro rfl; simp at hn1), ?_⟩
    exact (Nat.le_div_iff_mul_le hd1).mpr (by rw [Nat.mul_comm]; exact hnN)



end Formalism.HermitianLattices.Ext.SupplyAP
