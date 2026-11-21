import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.LogDeterminesLaw

noncomputable section

open PowerSeries

namespace Formalism.LT.PadicP

open Formalism.G

theorem padicInt_norm_le_p {p : ℕ} [Fact p.Prime] (y : ℤ_[p]) (hy : PadicInt.toZMod y = 0) :
    ‖y‖ ≤ ‖(p : ℤ_[p])‖ := by
  have hy' : y ∈ RingHom.ker (PadicInt.toZMod (p := p)) := RingHom.mem_ker.mpr hy
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hy'
  obtain ⟨z, rfl⟩ := hy'
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (PadicInt.norm_le_one z)


def unitBallEquiv (p : ℕ) [Fact p.Prime] : unitBall ℚ_[p] ≃+* ℤ_[p] where
  toFun x := ⟨x.1, x.2⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl




section LtLog

variable {p : ℕ} [hp : Fact p.Prime]

open Classical in
theorem coeff_ltLog (n : ℕ) :
    coeff n (ltLog p) = if ∃ k : ℕ, p ^ k = n then ((n : ℚ_[p]))⁻¹ else 0 := by
  unfold ltLog
  exact coeff_mk _ _

theorem isPow_mul_iff (m : ℕ) : (∃ k : ℕ, p ^ k = p * m) ↔ ∃ k : ℕ, p ^ k = m := by
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero =>
      rw [pow_zero] at hk
      have h1 : p ∣ 1 := ⟨m, hk⟩
      exact absurd (Nat.le_of_dvd one_pos h1) (by have := hp.out.two_le; omega)
    | succ k =>
      exact ⟨k, Nat.eq_of_mul_eq_mul_left hp.out.pos (by rw [← pow_succ']; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k + 1, pow_succ' p k⟩

theorem isPow_iff_of_not_dvd (n : ℕ) (h : ¬ p ∣ n) : (∃ k : ℕ, p ^ k = n) ↔ n = 1 := by
  constructor
  · rintro ⟨k, rfl⟩
    cases k with
    | zero => exact pow_zero p
    | succ k => exact absurd (dvd_pow_self p (Nat.succ_ne_zero k)) h
  · rintro rfl
    exact ⟨0, pow_zero p⟩

theorem constantCoeff_ltLog : constantCoeff (ltLog p) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_ltLog, if_neg]
  rintro ⟨k, hk⟩
  exact absurd hk (pow_ne_zero k hp.out.ne_zero)


private theorem coeff_subst_X_pow_lemma (f : PowerSeries ℚ_[p]) (n : ℕ) :
    coeff n (f.subst ((X : PowerSeries ℚ_[p]) ^ p)) = if p ∣ n then coeff (n / p) f else 0 := by
  have ha : HasSubst ((X : PowerSeries ℚ_[p]) ^ p) :=
    HasSubst.of_constantCoeff_zero' (by simp [hp.out.ne_zero])
  change MvPowerSeries.coeff (Finsupp.single () n) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff n (((X : PowerSeries ℚ_[p]) ^ p) ^ d) = _
  simp_rw [← pow_mul, coeff_X_pow]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    rw [finsum_eq_single _ m]
    · rw [if_pos rfl, smul_eq_mul, mul_one, Nat.mul_div_cancel_left m hp.out.pos]
    · intro d hd
      rw [if_neg (fun h' => hd (Nat.eq_of_mul_eq_mul_left hp.out.pos h').symm), smul_zero]
  · refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
    rw [if_neg (fun h' => h ⟨d, h'⟩), smul_zero]

theorem ltLog_funEq :
    ltLog p - (p : ℚ_[p])⁻¹ • (ltLog p).subst ((X : PowerSeries ℚ_[p]) ^ p) = X := by
  ext n
  rw [map_sub, PowerSeries.coeff_smul, smul_eq_mul, coeff_subst_X_pow_lemma, coeff_X]
  simp only [coeff_ltLog]
  by_cases hd : p ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hne : p * m ≠ 1 := by
      intro h
      have h1 := Nat.le_of_dvd one_pos ⟨m, h.symm⟩
      have := hp.out.two_le
      omega
    rw [if_pos (dvd_mul_right p m), Nat.mul_div_cancel_left m hp.out.pos, if_neg hne]
    by_cases hk : ∃ k, p ^ k = m
    · rw [if_pos ((isPow_mul_iff m).mpr hk), if_pos hk, Nat.cast_mul, mul_inv, sub_self]
    · rw [if_neg (fun h => hk ((isPow_mul_iff m).mp h)), if_neg hk, mul_zero, sub_zero]
  · rw [if_neg hd, mul_zero, sub_zero]
    by_cases h1 : n = 1
    · subst h1
      rw [if_pos ⟨0, pow_zero p⟩, if_pos rfl, Nat.cast_one, inv_one]
    · rw [if_neg (fun h => h1 ((isPow_iff_of_not_dvd n hd).mp h)), if_neg h1]


end LtLog

theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
    · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]



end Formalism.LT.PadicP

namespace Formalism.LT


end Formalism.LT
