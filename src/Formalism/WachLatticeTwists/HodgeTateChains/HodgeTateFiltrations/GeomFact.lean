import Formalism.WachLatticeTwists.HodgeTateChains.StatCharSum
import Formalism.WindowSums.AnnihilatorPolynomials.ZpowVal

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

theorem kappa : StatKappa := by
  intro ℓ hℓ s ρ hs h2 hρ hρs j hj1 hjs
  have := Fact.mk hℓ
  have hv : padicValNat ℓ j ≤ s := by
    refine le_trans (padicValNat_le_nat_log j) ?_
    calc Nat.log ℓ j ≤ Nat.log ℓ (ℓ ^ s) := Nat.log_mono_right hjs
      _ = s := Nat.log_pow hℓ.one_lt s
  have hvq : (padicValNat ℓ j : ℚ) ≤ s := by exact_mod_cast hv
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · interval_cases j
    · simp only [padicValNat.one]; push_cast; linarith
    · have hv2 : padicValNat ℓ 2 + 1 ≤ s := by
        by_cases hl : ℓ = 2
        · subst hl
          have : padicValNat 2 2 = 1 := padicValNat.self (by norm_num)
          have := h2 rfl
          omega
        · have : padicValNat ℓ 2 = 0 := by
            apply padicValNat.eq_zero_of_not_dvd
            intro hd
            exact hl ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 hd)
          omega
      have hv2q : (padicValNat ℓ 2 : ℚ) + 1 ≤ s := by exact_mod_cast hv2
      push_cast
      linarith
  · have hj : (3 : ℚ) ≤ j := by exact_mod_cast h3
    nlinarith


lemma geom_fact {R : Type} [CommRing R] (x : R) (a b : ℕ) :
    ∑ k ∈ Finset.range (a * b), x ^ k
      = (∑ k ∈ Finset.range a, x ^ k) * ∑ k ∈ Finset.range b, (x ^ a) ^ k := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ, mul_add]
    congr 1
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, ← pow_mul, mul_comm]

theorem charSum : StatCharSum := by
  intro R _ ℓ ζ h0 hζ h1 s j i n hjs
  have hpow : ∀ t i, ζ (i + t) ^ (ℓ ^ t) = ζ i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      rw [pow_succ', pow_mul, ← add_assoc, hζ, ih]
  have hsplit : ∀ k, ζ i ^ (n + ℓ ^ j * k) = ζ i ^ n * (ζ i ^ (ℓ ^ j)) ^ k := by
    intro k; rw [pow_add, pow_mul]
  constructor
  · intro hij
    have hone : ζ i ^ (ℓ ^ j) = 1 := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le hij
      have := hpow i 0
      rw [zero_add, h0] at this
      rw [pow_add, pow_mul, this, one_pow]
    simp only [hsplit, hone, one_pow, mul_one, Finset.sum_const, Finset.card_range]
  · intro hji his
    obtain ⟨t, rfl⟩ : ∃ t, i = j + (t + 1) := ⟨i - j - 1, by omega⟩
    have hy : ζ (j + (t + 1)) ^ (ℓ ^ j) = ζ (t + 1) := by
      rw [add_comm j (t + 1)]; exact hpow j (t + 1)
    simp only [hsplit, hy]
    rw [← Finset.mul_sum]
    obtain ⟨p, hp⟩ : ∃ p, s - j = t + (1 + p) := ⟨s - j - t - 1, by omega⟩
    have hz : ζ (t + 1) ^ (ℓ ^ t) = ζ 1 := by rw [add_comm t 1]; exact hpow t 1
    rw [hp, pow_add, geom_fact, hz, pow_add, pow_one, geom_fact, h1, zero_mul, mul_zero, mul_zero]


end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
