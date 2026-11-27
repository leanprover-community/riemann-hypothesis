module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliDyadicOrbits
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliProductSignedSum

/-! # The pure dyadic Bernoulli unit at the equality conductor -/

@[expose] public section

namespace UpperTheory.V.X

open Finset

private def boundarySum {R : Type*} [CommRing R] (N : ℕ) (z : R) : R :=
  ∑ j ∈ range (N / 8), bernoulliSignedCoeff (fun _ : ZMod 1 ↦ (1 : R)) N (5 ^ j % N) * z ^ j

private lemma map_boundarySum {R S : Type*} [CommRing R] [CommRing S] (ρ : R →+* S)
    (N : ℕ) (z : R) : ρ (boundarySum N z) = boundarySum N (ρ z) := by
  simp [boundarySum, bernoulliSignedCoeff, apply_ite ρ]

/-- For the modulus-one factor and an odd primitive dyadic character, the first Bernoulli
number has norm one already at conductor `2^(2e - 1)`, where `e = v₂(ℓ^d - 1)`. -/
theorem norm_genB_prodX_boundary {ℓ d n : ℕ} [Fact ℓ.Prime] (hd : 0 < d)
    (hfour : 4 ∣ ℓ ^ d - 1) (hn : n = 2 * (ℓ ^ d - 1).factorization 2 - 1)
    (φ : DirichletCharacter (PadicAlgCl ℓ) 1)
    (ξ : DirichletCharacter (PadicAlgCl ℓ) (2 ^ n)) (hprim : ξ.IsPrimitive)
    (hodd : ξ (-1) = -1) :
    ‖Bern.genB 1 (prodX φ ξ : ZMod (1 * 2 ^ n) → PadicAlgCl ℓ)‖ = 1 := by
  let e := (ℓ ^ d - 1).factorization 2
  have hprime : ℓ.Prime := Fact.out
  have hpos := Nat.one_lt_pow hd.ne' hprime.one_lt
  have hne : ℓ ^ d - 1 ≠ 0 := by lia
  have he : 2 ≤ e := (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp hfour
  let c := (ℓ ^ d - 1) / 2 ^ e
  have hc : Odd c := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hne)
  have hQ : ℓ ^ d = 1 + 2 ^ e * c := by
    have h : 2 ^ e * c = ℓ ^ d - 1 := Nat.ordProj_mul_ordCompl_eq_self _ 2
    lia
  change n = 2 * e - 1 at hn
  obtain ⟨t, rfl⟩ : ∃ t, n = t + 3 := ⟨n - 3, by lia⟩
  let N := 2 ^ (t + 3)
  have hlen : N / 8 = 2 ^ t := by
    dsimp [N]
    rw [pow_add]
    exact Nat.mul_div_cancel _ (by decide : 0 < 8)
  have hhalf : ξ 5 ^ (N / 8) = -1 := by
    rw [hlen]
    exact (map_five_pow_half_turn t ξ.toMonoidHom).trans
      (UpperTheory.primitive_two_pow_character_one_add_half_eq_neg_one _ (t + 3) (by lia) ξ hprim)
  have hφ : (φ : ZMod 1 → PadicAlgCl ℓ) = fun _ ↦ 1 :=
    funext fun x ↦ (congrArg φ (Subsingleton.elim x 1)).trans (map_one φ)
  have hB : Bern.genB 1 (prodX φ ξ : ZMod (1 * N) → PadicAlgCl ℓ) = boundarySum N (ξ 5) := by
    rw [genB_prodX_eq_quarter_signed_sum odd_one (by lia) φ ξ hprim (by simpa [hφ] using hodd),
      hφ, pureDyadic_signed_sum_eq_four_mul t ξ hodd hprim, mul_div_cancel_left₀ _ (by norm_num)]
    rw [boundarySum, hlen]
  obtain ⟨k, _, _, A, red, hA, hred⟩ := UpperTheory.exists_residue_map_padicAlgCl_integers ℓ
  have h2 : (2 : k) ≠ 0 := by
    intro hz
    have hl := (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp
      ((CharP.cast_eq_zero_iff k ℓ 2).mp hz)
    subst ℓ
    have := dvd_pow_self 2 hd.ne'
    lia
  have hzNorm : ‖ξ 5‖ = 1 := by
    apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (n := N / 8) (by rw [hlen]; positivity)).mp
    rw [← norm_pow, hhalf, norm_neg, norm_one]
  let z : A := ⟨ξ 5, (hA _).mpr hzNorm.le⟩
  have hzA : z ^ (N / 8) = -1 := Subtype.ext hhalf
  have hzk : (red z) ^ (N / 8) = -1 := by rw [← map_pow, hzA, map_neg, map_one]
  have hunit : red (boundarySum N z) ≠ 0 := by
    rw [map_boundarySum]
    have h := bernoulliSignedSum_boundary_ne_zero d e c he hc hQ h2 (red z)
    dsimp only at h
    rw [← hn] at h
    exact h hzk
  rw [hB]
  change ‖boundarySum N (A.subtype z)‖ = 1
  rw [← map_boundarySum]
  exact le_antisymm ((hA _).mp (boundarySum N z).property)
    (not_lt.mp (mt (hred _).mpr hunit))

/-- For odd primitive characters of dyadic conductor, halving the sufficient bound
preserves the Bernoulli unit conclusion at every conductor above the new cutoff. -/
theorem norm_genB_prodX_of_half_bound {ℓ d n : ℕ} [Fact ℓ.Prime] (hd : 0 < d)
    (hfour : 4 ∣ ℓ ^ d - 1) (hbound : 4 ^ (ℓ ^ d - 1).factorization 2 ≤ 2 * 2 ^ n)
    (φ : DirichletCharacter (PadicAlgCl ℓ) 1) (ξ : DirichletCharacter (PadicAlgCl ℓ) (2 ^ n))
    (hprim : ξ.IsPrimitive) (hodd : ξ (-1) = -1) :
    ‖Bern.genB 1 (prodX φ ξ : ZMod (1 * 2 ^ n) → PadicAlgCl ℓ)‖ = 1 := by
  let e := (ℓ ^ d - 1).factorization 2
  by_cases hbig : 4 ^ e ≤ 2 ^ n
  · have hφ : φ = 1 := Subsingleton.elim _ _
    apply lemmaX ℓ d 1 n φ ξ
    refine ⟨hd, hfour, odd_one, Nat.eq_one_of_dvd_one φ.conductor_dvd_level, ?_, hprim,
      by simpa using hbig, ?_⟩
    · simp [hφ]
    · have hone : φ (-1) = 1 := (congrArg φ (Subsingleton.elim _ 1)).trans (map_one φ)
      simpa only [hone, one_mul] using hodd
  · have hp : (4 : ℕ) ^ e = 2 ^ (2 * e) := by rw [pow_mul]; rfl
    change 4 ^ e ≤ 2 * 2 ^ n at hbound
    rw [hp, ← pow_succ'] at hbound
    rw [hp, Nat.pow_le_pow_iff_right Nat.one_lt_two] at hbig
    have hle := (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hbound
    exact norm_genB_prodX_boundary hd hfour (by change n = 2 * e - 1; omega) φ ξ hprim hodd

end UpperTheory.V.X
