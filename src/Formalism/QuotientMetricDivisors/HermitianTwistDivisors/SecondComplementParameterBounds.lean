import Mathlib
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ProdFormula

open Module NumberField IsDedekindDomain Finset

noncomputable section

namespace Formalism.DivisionValues

namespace PlaceSumConjugation

section Places

variable {K : Type} [Field K] [NumberField K]

theorem natCast_ne_zero' {g : ℕ} (hg : 0 < g) : (g : K) ≠ 0 := by
  exact_mod_cast hg.ne'

theorem vw_nat_nonneg (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : 0 ≤ vw w (g : K) := by
  unfold vw
  have h : (g : K) = algebraMap (𝓞 K) K (g : 𝓞 K) := by simp
  rw [h, ← FractionalIdeal.coeIdeal_span_singleton]
  apply FractionalIdeal.count_coe_nonneg


theorem lw_pos (w : HeightOneSpectrum (𝓞 K)) : 0 < lw w := by
  unfold lw
  have h0 : Ideal.absNorm w.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact w.ne_bot
  have h1 : Ideal.absNorm w.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact w.isPrime.ne_top
  have h2 : (1 : ℝ) < (Ideal.absNorm w.asIdeal : ℝ) := by
    exact_mod_cast (by omega : 1 < Ideal.absNorm w.asIdeal)
  apply div_pos (Real.log_pos h2)
  exact_mod_cast Module.finrank_pos


theorem plOver_mem {g : ℕ} (hg : 0 < g) (w : HeightOneSpectrum (𝓞 K)) (h : PlOver g w) :
    (g : 𝓞 K) ∈ w.asIdeal := by
  classical
  have hc : ((g : 𝓞 K) : K) = (g : K) := by simp
  have hg0 : (g : 𝓞 K) ≠ 0 := by exact_mod_cast hg.ne'
  have hJ : (Ideal.span {(g : 𝓞 K)} : Ideal (𝓞 K)) ≠ 0 := by
    rwa [ne_eq, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
  unfold PlOver vw at h
  rw [← hc, ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.count_coe K _ hJ] at h
  have h1 : 1 ≤ (Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(g : 𝓞 K)})).factors := by
    exact_mod_cast h
  have hm : Associates.mk (Ideal.span {(g : 𝓞 K)}) ≠ 0 := by rwa [ne_eq, Associates.mk_eq_zero]
  rw [← Associates.prime_pow_dvd_iff_le hm w.associates_irreducible, pow_one,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem] at h1
  exact h1

end Places

section Star

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem vw_conj_nat (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) :
    vw (conjPl w) (g : K) = vw w (g : K) := by
  rw [← ValuationRepresentative.vw_star, star_natCast]

theorem plOver_conj (g : ℕ) (w : HeightOneSpectrum (𝓞 K)) : PlOver g (conjPl w) ↔ PlOver g w := by
  unfold PlOver
  rw [vw_conj_nat]

private theorem conjPl_conjPl_lemma {K : Type} [Field K] [NumberField K] [StarRing K]
    (w : HeightOneSpectrum (𝓞 K)) : conjPl (conjPl w) = w := by
  have hinv : ∀ x : 𝓞 K, cO K (cO K x) = x := by
    intro x
    apply RingOfIntegers.ext
    first
      | (simp [cO]; done)
      | (change star (star (x : K)) = (x : K); exact star_star _)
      | (simp [cO, RingOfIntegers.mapRingEquiv]; done)
  have key : (w.asIdeal.map (cO K)).map (cO K) = w.asIdeal := by
    ext x
    simp only [Ideal.mem_map_of_equiv]
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      rw [hinv]; exact hz
    · intro hx
      exact ⟨cO K x, ⟨x, hx, rfl⟩, hinv x⟩
  exact HeightOneSpectrum.ext key

theorem sum_conj {g : ℕ} (hS : {w : HeightOneSpectrum (𝓞 K) | PlOver g w}.Finite)
    (f : HeightOneSpectrum (𝓞 K) → ℝ) :
    ∑ w ∈ hS.toFinset, f (conjPl w) = ∑ w ∈ hS.toFinset, f w := by
  apply Finset.sum_nbij' conjPl conjPl
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w hw
    simp only [Set.Finite.coe_toFinset, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hw ⊢
    exact (plOver_conj g w).2 hw
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; exact conjPl_conjPl_lemma w
  · intro w _; rfl

theorem vw_pow (w : HeightOneSpectrum (𝓞 K)) (a : K) (ha : a ≠ 0) (n : ℕ) :
    vw w (a ^ n) = (n : ℤ) * vw w a := by
  unfold vw
  rw [← FractionalIdeal.spanSingleton_pow, FractionalIdeal.count_pow]

end Star


end PlaceSumConjugation

open PlaceSumConjugation


theorem places_over_coprime : PlOverCoprime := by
  unfold PlOverCoprime
  intro K _ _ g g' hcop w ⟨h1, h2⟩
  have hpos : ∀ n : ℕ, PlOver n w → 0 < n := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0
      unfold PlOver vw at hn
      first | simp [FractionalIdeal.count_zero] at hn | (unfold FractionalIdeal.count at hn; simp at hn)
    · exact h0
  have m1 := plOver_mem (hpos g h1) w h1
  have m2 := plOver_mem (hpos g' h2) w h2
  have hab : (Nat.gcdA g g') * (g : ℤ) + (Nat.gcdB g g') * (g' : ℤ) = 1 := by
    have := Nat.gcd_eq_gcd_ab g g'
    rw [Nat.Coprime.gcd_eq_one hcop] at this
    push_cast at this
    linarith
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one]
  have e : (1 : 𝓞 K) = ((Nat.gcdA g g' : ℤ) : 𝓞 K) * (g : 𝓞 K) + ((Nat.gcdB g g' : ℤ) : 𝓞 K) * (g' : 𝓞 K) := by
    exact_mod_cast hab.symm
  rw [e]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ m1) (Ideal.mul_mem_left _ _ m2)





theorem sum_top {Pl : Type} [Fintype Pl] (TT : Finset Pl) [DecidablePred (· ∈ TT)] (f : Pl → ℝ) :
    ∑ t ∈ TT, f t = ∑ ρ, if ρ ∈ TT then f ρ else 0 := by
  symm
  rw [← Finset.sum_filter]
  congr 1
  ext ρ
  simp

















end Formalism.DivisionValues
