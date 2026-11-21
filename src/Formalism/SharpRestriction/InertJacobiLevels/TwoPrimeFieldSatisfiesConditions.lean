import Formalism.SharpRestriction.InertJacobiLevels.TwoPrimeFieldMemLevelOfCoprime

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition NumberField IsDedekindDomain
open scoped Pointwise

structure HostOk (x eps Cp : ℝ) {R : Ranks} (H : Host R) : Prop where
  good : QDGood x eps H.q H.d
  split_tie : ⌊x ^ (eps / 5)⌋₊ ≤ H.splitBound
  g_win : ∀ i, Yof R x eps ≤ (H.g i : ℝ) ∧ (H.g i : ℝ) ≤ 2 * Yof R x eps
  g_norm : ∀ i, ∃ π : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_norm1 : ∀ i, ∃ π ρ : 𝓞 H.E, (π : H.E) ∈ H.K ∧ (ρ : H.E) ∈ H.K ∧
    (π : H.E) - 1 = ((H.QS * H.q * H.d : ℕ) : H.E) * ρ ∧ (π : H.E) * H.conj (π : H.E) = (H.g i : H.E)
  g_mod : ∀ i, H.g i % (H.QS * H.q * H.d) = 1
  thyp : THyp H
  g_split : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E
  g_cls : ∀ i, H.cls (H.g i) = .splitK
  pde_split : (Ideal.primesOver (Ideal.span {(H.pde : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E ∧
    (Ideal.primesOver (Ideal.span {(H.pde' : ℤ)}) (𝓞 H.E)).ncard = Module.finrank ℚ H.E
  pde_cls : H.cls H.pde = .splitK ∧ H.cls H.pde' = .splitK
  pde_log : Real.log H.pde < x ^ (eps / 3) ∧ Real.log H.pde' < x ^ (eps / 3)
  ccK_norm : Ideal.absNorm H.ccK = 1
  secondSet_card_lower_bound : H.secondSet_card_lower_bound
  secondTorsion_card_pos : 0 < H.T2.card
  secondTorsion_card_le : H.T2.card ≤ R.n0
  o_tie : (R.o : ℝ) ≤ x ^ (eps / 1000)
  QS_tie : (H.QS : ℝ) ≤ 4 * R.n * x ^ (eps / 1000)


theorem norm_mod {R : Ranks} (H : Host R) {M T : ℕ} (hM : 0 < M) (π : 𝓞 H.E)
    (h2 : (π : H.E) * H.conj (π : H.E) = (T : H.E)) (h3 : (π - 1) ∈ Ideal.span {((M : ℕ) : 𝓞 H.E)}) :
    T ≡ 1 [MOD M] := by
  obtain ⟨ρ, hρ⟩ := Ideal.mem_span_singleton.1 h3
  have hπ : (π : H.E) = 1 + (M : H.E) * (ρ : H.E) := by
    have : ((π - 1 : 𝓞 H.E) : H.E) = (((M : ℕ) : 𝓞 H.E) * ρ : 𝓞 H.E) := by rw [hρ]
    push_cast at this
    linear_combination this
  have hint : IsIntegral ℤ (H.conj (ρ : H.E)) := map_isIntegral_int H.conj ρ.2
  set ρ' : 𝓞 H.E := ⟨H.conj (ρ : H.E), hint⟩ with hρ'
  have hρc : ((ρ' : 𝓞 H.E) : H.E) = H.conj (ρ : H.E) := rfl
  set w : 𝓞 H.E := ρ + ρ' + (M : 𝓞 H.E) * ρ * ρ' with hw
  have hwc : (w : H.E) = (ρ : H.E) + H.conj (ρ : H.E) + (M : H.E) * ρ * H.conj (ρ : H.E) := by
    rw [hw, ← hρc]; push_cast; rfl
  have key : (T : H.E) - 1 = (M : H.E) * (w : H.E) := by
    rw [← h2, hπ, hwc]
    simp only [map_add, map_mul, map_one, map_natCast]
    ring
  have hM0 : (M : H.E) ≠ 0 := by exact_mod_cast hM.ne'
  have hr : algebraMap ℚ H.E (((T : ℚ) - 1) / M) = (w : H.E) := by
    rw [map_div₀, map_sub, map_one, map_natCast, map_natCast, key, mul_div_cancel_left₀ _ hM0]
  have hi : IsIntegral ℤ (((T : ℚ) - 1) / M) := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ H.E).injective, hr]
    exact w.2
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hi
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast hM.ne'
  have hz' : (T : ℤ) - 1 = M * z := by
    have : (T : ℚ) - 1 = M * z := by
      have h5 : (z : ℚ) = ((T : ℚ) - 1) / M := by simpa using hz
      rw [h5]; field_simp
    exact_mod_cast this
  rw [← Int.natCast_modEq_iff]
  apply Int.ModEq.symm
  rw [Int.modEq_iff_dvd]
  exact ⟨z, by push_cast; exact hz'⟩



variable {R : Ranks} {x eps Cp CT : ℝ} (B : Base R x eps Cp CT)

namespace Base

theorem q_odd : Odd B.q := Nat.odd_iff.2 (by have := B.good.hyp.2.2.1; omega)

theorem one_lt_cond : 1 < B.condN :=
  lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd (Nat.pos_of_ne_zero B.condN_ne_zero) B.two_dvd_condN)


theorem first_prime_modEq_one : B.g0 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.first_prime_norm_form; exact form_mod h
theorem second_prime_modEq_one : B.g1 ≡ 1 [MOD B.condN] := by
  obtain ⟨u, v, h⟩ := B.second_prime_norm_form; exact form_mod h


end Base




def Base.MT : ℕ := B.condN * (B.g0 * B.g1) ^ 2


section Indep

variable (u0 u0' : R.A) (ex ex' : Finset ℕ)


end Indep

end Formalism.MainNotions.Inhab

end
