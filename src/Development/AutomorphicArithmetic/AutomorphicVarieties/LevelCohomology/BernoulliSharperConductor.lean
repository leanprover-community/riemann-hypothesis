module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliBoundaryUnit
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliLinearRange
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliRowSpecialization
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliTranslatedOrbits
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliUnitReduction

/-! # A halved dyadic conductor bound for the Bernoulli-unit lemma -/

@[expose] public section

namespace UpperTheory.V.X

open Finset

/-- The first Bernoulli number of an odd product character is an ℓ-adic unit once twice
the dyadic conductor is at least the odd conductor times the square of the dyadic part
of `ℓ^d - 1`. This includes odd conductors divisible by ℓ. -/
theorem norm_genB_prodX_of_halved_conductor {ℓ d f n : ℕ} [Fact ℓ.Prime]
    (hd : 0 < d) (hfour : 4 ∣ ℓ ^ d - 1) (hf : Odd f)
    (hbound : f * 4 ^ (ℓ ^ d - 1).factorization 2 ≤ 2 * 2 ^ n)
    (φ : DirichletCharacter (PadicAlgCl ℓ) f) (ξ : DirichletCharacter (PadicAlgCl ℓ) (2 ^ n))
    (hord : orderOf φ ∣ ℓ ^ d - 1) (hprim : ξ.IsPrimitive) (hodd : φ (-1) * ξ (-1) = -1) :
    ‖Bern.genB 1 (prodX φ ξ : ZMod (f * 2 ^ n) → PadicAlgCl ℓ)‖ = 1 := by
  by_cases heq : f * 4 ^ (ℓ ^ d - 1).factorization 2 = 2 * 2 ^ n
  · -- An odd divisor of the power of two on the right must be one.
    have hf₁ : f = 1 :=
      Nat.eq_one_of_dvd_coprimes (hf.coprime_two_right.pow_right (n + 1)) dvd_rfl
        ⟨_, by rw [pow_succ', ← heq]⟩
    subst f
    let e := (ℓ ^ d - 1).factorization 2
    have hp : 2 ^ (2 * e) = 2 ^ (n + 1) := by
      rw [pow_mul, pow_succ' 2 n]
      simpa only [show (2 : ℕ) ^ 2 = 4 by decide, e, one_mul] using heq
    have hexp := Nat.pow_right_injective (by decide : 2 ≤ 2) hp
    have hφ : φ (-1) = 1 := (congrArg φ (Subsingleton.elim _ 1)).trans (map_one φ)
    exact norm_genB_prodX_boundary hd hfour (by change n = 2 * e - 1; omega) φ ξ hprim
      (by simpa only [hφ, one_mul] using hodd)
  obtain ⟨t, j, c, rfl, hQ, hc, hdvd, hlt, hN⟩ :=
    exists_bernoulli_linear_range hd hfour hf (hbound.lt_of_ne heq)
  have hl : ℓ ≠ 2 := by
    rintro rfl
    have h := dvd_trans (by decide : 2 ∣ 4) hfour
    have := dvd_pow_self 2 hd.ne'
    omega
  apply norm_genB_prodX_of_residue hl hd hf (by omega) φ ξ hord hprim hodd
  intro K _ _ ψ χ h2 hfix hpar hhalf hsum
  let T := 2 ^ (t + 1)
  let h := 4 * 2 ^ j
  let N := h * (2 * T)
  -- The dyadic half-turn gives the minus sign used to isolate the Fourier row.
  have hpow : χ 5 ^ (2 ^ (j + t + 1)) = -1 :=
    (map_five_pow_half_turn (j + t + 1) χ.toMonoidHom).trans (by simpa using hhalf)
  have hlen : N / 8 = 2 ^ j * T := by
    rw [show N = (2 ^ j * T) * 8 by dsimp [N, h]; ring, Nat.mul_div_cancel _ (by decide)]
  have hz : χ 5 ^ (N / 8) = -1 := by
    rwa [hlen, show 2 ^ j * T = 2 ^ (j + t + 1) by dsimp [T]; rw [← pow_add, Nat.add_assoc]]
  have hβ : (χ 5 ^ (2 ^ j)) ^ T = -1 := by rwa [← pow_mul, ← hlen]
  have hψ : ψ 1 ≠ 0 ∧ ψ (-1) ≠ 0 :=
    ⟨by simp, (isUnit_one.neg.map ψ.toMonoidHom).ne_zero⟩
  -- Translation of a zero signed sum would force this particular nonzero row to vanish.
  obtain ⟨a, -, ha4, hnonzero⟩ :=
    exists_bernoulliFourierRow_ne_zero ψ hf hψ h2 t j (χ 5 ^ (2 ^ j)) hdvd hlt hβ
  apply hnonzero
  apply bernoulliFourierRow_eq_zero_of_sum_eq_zero d t j c a ψ (χ 5) hc h2 hfix hQ hz
  have haodd : Odd a := Nat.odd_iff.mpr (by omega)
  have htranslate := translated_signed_sum_eq_zero_of_odd h2 hf (j + t + 1) ψ χ hpar
    (by simpa using hhalf) a haodd hsum
  exact hN ▸ htranslate

/-- For odd primitive characters of dyadic conductor, halving the sufficient bound
preserves the Bernoulli unit conclusion at every conductor above the new cutoff. -/
theorem norm_genB_prodX_of_half_bound {ℓ d n : ℕ} [Fact ℓ.Prime] (hd : 0 < d)
    (hfour : 4 ∣ ℓ ^ d - 1) (hbound : 4 ^ (ℓ ^ d - 1).factorization 2 ≤ 2 * 2 ^ n)
    (φ : DirichletCharacter (PadicAlgCl ℓ) 1) (ξ : DirichletCharacter (PadicAlgCl ℓ) (2 ^ n))
    (hprim : ξ.IsPrimitive) (hodd : ξ (-1) = -1) :
    ‖Bern.genB 1 (prodX φ ξ : ZMod (1 * 2 ^ n) → PadicAlgCl ℓ)‖ = 1 := by
  have hφ : φ = 1 := Subsingleton.elim _ _
  have hone : φ (-1) = 1 := (congrArg φ (Subsingleton.elim _ 1)).trans (map_one φ)
  exact norm_genB_prodX_of_halved_conductor hd hfour odd_one (by simpa using hbound) φ ξ
    (by simp [hφ]) hprim (by simpa only [hone, one_mul] using hodd)

end UpperTheory.V.X
