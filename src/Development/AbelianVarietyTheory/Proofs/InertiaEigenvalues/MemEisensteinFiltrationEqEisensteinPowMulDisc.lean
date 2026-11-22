module

public import Mathlib
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ImagePolynomialAction

@[expose] public section

noncomputable section

namespace GlobalTheory.FilDiv

open PowerSeries Filter Topology GlobalTheory.BK

section
variable {O K : Type} [CommRing O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] (l : ℕ) [Fact l.Prime] [NormedAlgebra ℚ_[l] K] (e : ℕ) [NeZero e]

theorem norm_coeff_pow_mul_le (n : ℕ) {h : K⟦X⟧} (hh : h ∈ S O K e) (k : ℕ) :
    ‖coeff k ((l : K⟦X⟧) ^ n * h)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  rw [← map_natCast (C : K →+* K⟦X⟧), ← map_pow, coeff_C_mul, norm_mul, norm_pow, mul_assoc]
  refine mul_le_of_le_one_right (by positivity) ?_
  refine le_trans ?_ (hh.1 k)
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans ?_ (norm_pow_le_norm_factorial l (k / e))
  rw [← rad_pow l e, ← pow_mul]
  exact pow_le_pow_of_le_one (rad_nonneg _ _) (rad_le_one l (by positivity)) (Nat.mul_div_le k e)

theorem norm_coeff_E_le (k : ℕ) : ‖coeff k (E K l e)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ := by
  have he := NeZero.ne e
  rw [E, map_add (f := _), coeff_X_pow, ← map_natCast (C : K →+* K⟦X⟧), coeff_C]
  by_cases hk : k = e
  · rw [if_pos hk, if_neg (by omega), add_zero, norm_one, one_mul, hk, rad_pow (K := K) l e]
  · by_cases h0 : k = 0
    · rw [if_neg hk, if_pos h0, zero_add, h0, pow_zero, mul_one]
    · rw [if_neg hk, if_neg h0, add_zero, norm_zero, zero_mul]
      exact norm_nonneg _

variable [CompleteSpace K]

theorem norm_coeff_quotE_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ n := by
  have hρ := rad_pos l (1 / (e : ℝ))
  have hl : 0 < ‖(l : K)‖ := norm_pos_iff.2 (l_ne_zero l)
  rw [quotE, coeff_mk]
  have h1 : ‖tail l e r (k + e)‖ ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) := by
    refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun j => ?_
    rw [le_div_iff₀ (pow_pos hρ _), norm_term_eq]
    exact hr _
  calc ‖tail l e r (k + e)‖ * rad l (1 / e) ^ k
      ≤ ‖(l : K)‖ ^ (n + 1) / rad l (1 / e) ^ (k + e) * rad l (1 / e) ^ k :=
        mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = ‖(l : K)‖ ^ n := by
        rw [pow_add (rad l (1 / (e : ℝ))) k e, rad_pow (K := K) l e, pow_succ]
        field_simp

theorem norm_coeff_rem_le {r : K⟦X⟧} {n : ℕ}
    (hr : ∀ k, ‖coeff k r‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1)) (k : ℕ) :
    ‖coeff k (r - E K l e * quotE l e r)‖ * rad l (1 / e) ^ k ≤ ‖(l : K)‖ ^ (n + 1) := by
  have hw : ∀ i, 0 ≤ rad l (1 / (e : ℝ)) ^ i := fun i => pow_nonneg (rad_nonneg _ _) i
  rw [sub_eq_add_neg]
  refine (norm_coeff_add_le hw _ _ k).trans (max_le (hr k) ?_)
  rw [map_neg, norm_neg, pow_succ']
  exact norm_coeff_mul_le (w := fun i => rad l (1 / (e : ℝ)) ^ i) hw (fun i j => (pow_add _ i j).le)
    (norm_nonneg _) (by positivity) (norm_coeff_E_le l e) (norm_coeff_quotE_le l e hr) k

end

end GlobalTheory.FilDiv
