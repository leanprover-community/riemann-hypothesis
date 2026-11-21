import Formalism.LandauZeroFreeBounds.SiegelWalfiszAPOfSiegelLower
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.ExcTerm
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.ExceptionalCharacterBounds.EffBase
import Mathlib
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LGrowth
import Formalism.LandauZeroFreeBounds.ExceptionalZeroBounds.LDerivNearOne
import Formalism.LandauZeroFreeBounds.SiegelWalfiszAP

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP


end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP




end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP



end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem gExp_nonpos {t : ℝ} (ht : 0 < t) : gExp t ≤ 0 := by
  unfold gExp
  have h1 : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have : 1 / (Real.exp t - 1) ≤ 1 / t := one_div_le_one_div_of_le ht h1
  linarith

private def hFun (t : ℝ) : ℝ := (2 + t) - (2 - t) * Real.exp t

private theorem hFun_hasDerivAt (t : ℝ) : HasDerivAt hFun (1 - (1 - t) * Real.exp t) t := by
  have h1 : HasDerivAt (fun t : ℝ => 2 + t) 1 t := (hasDerivAt_id t).const_add 2
  have h2 : HasDerivAt (fun t : ℝ => 2 - t) (-1) t := by
    simpa using (hasDerivAt_id t).const_sub 2
  have h3 := h2.mul (Real.hasDerivAt_exp t)
  have h4 := h1.sub h3
  exact h4.congr_deriv (by ring)

private theorem hFun_mono : Monotone hFun := by
  refine monotone_of_deriv_nonneg (fun t => (hFun_hasDerivAt t).differentiableAt) ?_
  intro t
  rw [(hFun_hasDerivAt t).deriv]
  have h1 : 1 - t ≤ Real.exp (-t) := by linarith [Real.add_one_le_exp (-t)]
  have h2 : Real.exp (-t) * Real.exp t = 1 := by rw [← Real.exp_add]; simp
  have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos t).le
  linarith

theorem neg_half_le_gExp {t : ℝ} (ht : 0 < t) : -(1 / 2) ≤ gExp t := by
  unfold gExp
  have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
  have hh : hFun 0 ≤ hFun t := hFun_mono ht.le
  have h0 : hFun 0 = 0 := by simp [hFun]
  rw [h0] at hh
  unfold hFun at hh
  rw [div_sub_div _ _ hE.ne' ht.ne', le_div_iff₀ (mul_pos hE ht)]
  nlinarith

private theorem gExp_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt gExp (-(Real.exp t) / (Real.exp t - 1) ^ 2 - (-(1 / t ^ 2))) t := by
  have hE : Real.exp t - 1 ≠ 0 := by linarith [Real.add_one_le_exp t]
  have h1 : HasDerivAt (fun t => 1 / (Real.exp t - 1)) (-(Real.exp t) / (Real.exp t - 1) ^ 2) t := by
    have := (hasDerivAt_const t (1:ℝ)).div ((Real.hasDerivAt_exp t).sub_const 1) hE
    exact this.congr_deriv (by ring)
  have h2 : HasDerivAt (fun t : ℝ => 1 / t) (-(1 / t ^ 2)) t := by
    have := (hasDerivAt_const t (1:ℝ)).div (hasDerivAt_id' t) ht.ne'
    exact this.congr_deriv (by ring)
  exact h1.sub h2

theorem gExp_monotoneOn : MonotoneOn gExp (Set.Ioi 0) := by
  refine monotoneOn_of_deriv_nonneg (convex_Ioi 0) ?_ ?_ ?_
  · intro t ht; exact (gExp_hasDerivAt ht).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    exact (gExp_hasDerivAt ht).differentiableAt.differentiableWithinAt
  · intro t ht
    rw [interior_Ioi] at ht
    have ht : 0 < t := ht
    rw [(gExp_hasDerivAt ht).deriv]
    have hE : 0 < Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
    set a := Real.exp (t / 2)
    set b := Real.exp (-(t / 2))
    have hab : a * b = 1 := by simp only [a, b]; rw [← Real.exp_add]; simp
    have haa : a * a = Real.exp t := by simp only [a]; rw [← Real.exp_add]; ring_nf
    have hs : t / 2 ≤ Real.sinh (t / 2) := Real.self_le_sinh_iff.mpr (by linarith)
    rw [Real.sinh_eq] at hs
    have hd : t ≤ a - b := by linarith
    have ha : 0 < a := Real.exp_pos _
    have key : Real.exp t * t ^ 2 ≤ (Real.exp t - 1) ^ 2 := by
      rw [← haa, ← hab]
      have : t ^ 2 ≤ (a - b) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_self_nonneg a)]
    have : Real.exp t / (Real.exp t - 1) ^ 2 ≤ 1 / t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]; linarith
    rw [neg_div]; linarith

open Finset in

theorem abelG (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) (x : ℝ) (hx : 0 < x) (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, χ (d : ZMod q) * ((gExp ((d : ℝ) / x) : ℝ) : ℂ)‖ ≤ ((q : ℝ) + 1) / 2 := by
  set b : ℕ → ℝ := fun d => gExp ((d : ℝ) / x) with hb
  set S : ℕ → ℂ := fun M => ∑ n ∈ Icc 1 M, χ (n : ZMod q) with hS
  set B : ℝ := (q : ℝ) + 1 with hB
  have hSB : ∀ M, ‖S M‖ ≤ B := fun M => Formalism.ZeroFreeDirichlet.norm_character_sum_Icc_le χ hχ M
  have hB0 : 0 ≤ B := by positivity
  have hpos : ∀ d : ℕ, 1 ≤ d → (0 : ℝ) < (d : ℝ) / x := fun d hd => by
    have : (1 : ℝ) ≤ d := by exact_mod_cast hd
    positivity
  have hmono : ∀ d : ℕ, 1 ≤ d → b d ≤ b (d + 1) := by
    intro d hd
    refine gExp_monotoneOn (hpos d hd) (hpos (d + 1) (by omega)) ?_
    push_cast
    exact div_le_div_of_nonneg_right (by linarith) hx.le
  have hle0 : ∀ d : ℕ, 1 ≤ d → b d ≤ 0 := fun d hd => gExp_nonpos (hpos d hd)
  have hhalf : -(1 / 2) ≤ b 1 := neg_half_le_gExp (hpos 1 le_rfl)
  set F : ℕ → ℂ := fun N => ∑ d ∈ Icc 1 N, χ (d : ZMod q) * ((b d : ℝ) : ℂ) with hF
  have hT : ∀ M : ℕ, ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (b (M + 1) - b 1) := by
    intro M
    induction M with
    | zero => simp [hF, hS]
    | succ M ih =>
      have hF1 : F (M + 1 + 1) = F (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) * ((b (M + 1 + 1) : ℝ) : ℂ) := by
        simp only [hF]; rw [Finset.sum_Icc_succ_top (by omega)]
      have hS1 : S (M + 1 + 1) = S (M + 1) + χ ((M + 1 + 1 : ℕ) : ZMod q) := by
        simp only [hS]; rw [Finset.sum_Icc_succ_top (by omega)]
      have heq : F (M + 1 + 1) - S (M + 1 + 1) * ((b (M + 1 + 1) : ℝ) : ℂ) =
          (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) - S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ) := by
        rw [hF1, hS1]; push_cast; ring
      rw [heq]
      have hd := hmono (M + 1) (by omega)
      calc _ ≤ ‖F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ + ‖S (M + 1) * ((b (M + 1 + 1) - b (M + 1) : ℝ) : ℂ)‖ :=
            norm_sub_le _ _
        _ ≤ B * (b (M + 1) - b 1) + B * (b (M + 1 + 1) - b (M + 1)) := by
            gcongr
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
            exact mul_le_mul_of_nonneg_right (hSB _) (by linarith)
        _ = B * (b (M + 1 + 1) - b 1) := by ring
  change ‖F N‖ ≤ B / 2
  rcases N with _ | M
  · simp [hF]; positivity
  · have h1 := hT M
    have h2 : ‖S (M + 1) * ((b (M + 1) : ℝ) : ℂ)‖ ≤ B * (-b (M + 1)) := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (hle0 _ (by omega))]
      exact mul_le_mul_of_nonneg_right (hSB _) (by linarith [hle0 (M + 1) (by omega)])
    have h3 : F (M + 1) = (F (M + 1) - S (M + 1) * ((b (M + 1) : ℝ) : ℂ)) + S (M + 1) * ((b (M + 1) : ℝ) : ℂ) := by ring
    rw [h3]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ B * (b (M + 1) - b 1) + B * (-b (M + 1)) := add_le_add h1 h2
      _ = B * (-b 1) := by ring
      _ ≤ B / 2 := by nlinarith

end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
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
end
end

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

theorem tail_small {x : ℝ} (hx : 1 ≤ x) : x ^ 3 * (x + 1) * Real.exp (-(x ^ 3) / x) ≤ 48 / x ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hdiv : -(x ^ 3) / x = -(x ^ 2) := by field_simp
  rw [hdiv, Real.exp_neg]
  have he := Real.pow_div_factorial_le_exp (x ^ 2) (sq_nonneg x) 4
  have h24 : ((4 : ℕ).factorial : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [h24] at he
  have hE : 0 < Real.exp (x ^ 2) := Real.exp_pos _
  rw [le_div_iff₀ (by positivity), mul_assoc, mul_assoc]
  have hx1 : x + 1 ≤ 2 * x := by linarith
  have hpos : 0 < (Real.exp (x ^ 2))⁻¹ := inv_pos.mpr hE
  have key : x ^ 3 * (x + 1) * x ^ 4 ≤ 2 * x ^ 8 := by nlinarith [pow_pos hx0 7]
  have h8 : x ^ 8 ≤ 24 * Real.exp (x ^ 2) := by
    have : (x ^ 2) ^ 4 = x ^ 8 := by ring
    rw [this] at he
    rw [div_le_iff₀ (by norm_num)] at he; linarith
  calc x ^ 3 * ((x + 1) * ((Real.exp (x ^ 2))⁻¹ * x ^ 4))
      = (x ^ 3 * (x + 1) * x ^ 4) * (Real.exp (x ^ 2))⁻¹ := by ring
    _ ≤ (2 * x ^ 8) * (Real.exp (x ^ 2))⁻¹ := mul_le_mul_of_nonneg_right key hpos.le
    _ ≤ (2 * (24 * Real.exp (x ^ 2))) * (Real.exp (x ^ 2))⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ = 48 := by field_simp; ring


end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP



end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP

def primesAP (m a : ℕ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD m])


end Formalism.HermitianLattices.Ext.SupplyAP
end
end

section
open Formalism.ZeroFreeDirichlet

noncomputable section

namespace Formalism.HermitianLattices.Ext.SupplyAP




end Formalism.HermitianLattices.Ext.SupplyAP
end
end
