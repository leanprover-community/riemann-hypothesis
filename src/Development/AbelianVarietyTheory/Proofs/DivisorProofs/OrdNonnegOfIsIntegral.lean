import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeMapPrimeMap
open NumberField IsDedekindDomain GlobalTheory.FixNormCls
open scoped Classical nonZeroDivisors

noncomputable section

namespace GlobalTheory.LocalDivisor

variable {E : Type} [Field E] [NumberField E]

theorem ord_neg (P : HeightOneSpectrum (𝓞 E)) (x : E) : ord P (-x) = ord P x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have h1 : ord P (-1 : E) = 0 := by
    have := ord_mul P (x := (-1 : E)) (y := -1) (by norm_num) (by norm_num)
    rw [show (-1 : E) * -1 = 1 by ring, ord_one] at this
    linarith
  rw [show -x = (-1 : E) * x by ring, ord_mul P (by norm_num) hx, h1, zero_add]


theorem ord_algebraMap_eq_zero (P : HeightOneSpectrum (𝓞 E)) {r : 𝓞 E} (hr : r ∉ P.asIdeal) :
    ord P (algebraMap (𝓞 E) E r) = 0 := by
  have hr0 : r ≠ 0 := by rintro rfl; exact hr P.asIdeal.zero_mem
  unfold ord
  rw [← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe E P (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])]
  have hne : Ideal.span {r} ≠ ⊥ := by rwa [Ne, Ideal.span_singleton_eq_bot]
  rw [Nat.cast_eq_zero]
  by_contra hc
  exact hr (Ideal.dvd_span_singleton.1 ((Associates.count_ne_zero_iff_dvd hne P.irreducible).1 hc))

theorem natCast_not_mem (P : HeightOneSpectrum (𝓞 E)) {ℓ d : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) (hd : ¬ ℓ ∣ d) : (d : 𝓞 E) ∉ P.asIdeal := by
  intro h
  have hc : IsCoprime (ℓ : ℤ) (d : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hd)
  obtain ⟨u, v, huv⟩ := hc
  have : (1 : 𝓞 E) ∈ P.asIdeal := by
    have e : (((u * ℓ + v * d : ℤ)) : 𝓞 E) = 1 := by rw [huv]; simp
    rw [← e]; push_cast
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hP) (P.asIdeal.mul_mem_left _ h)
  exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)

theorem ord_natCast_coprime (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {d : ℕ} (hd : ¬ ℓ ∣ d) : ord P (d : E) = 0 := by
  rw [← map_natCast (algebraMap (𝓞 E) E) d]
  exact ord_algebraMap_eq_zero P (natCast_not_mem P hℓ hP hd)

theorem exists_prime_mem (P : HeightOneSpectrum (𝓞 E)) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ P.asIdeal := by
  have h0 : Ideal.absNorm P.asIdeal ≠ 0 := by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact P.ne_bot
  suffices ∀ n : ℕ, n ≠ 0 → (n : 𝓞 E) ∈ P.asIdeal → ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 E) ∈ P.asIdeal from
    this _ h0 (Ideal.absNorm_mem P.asIdeal)
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hmem
    have hn1 : n ≠ 1 := by
      rintro rfl
      simp only [Nat.cast_one] at hmem
      exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 hmem)
    have hp := Nat.minFac_prime hn1
    have e : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' (Nat.minFac_dvd n)).symm
    have hm0 : n / n.minFac ≠ 0 := by
      intro h; rw [h, mul_zero] at e; exact hn e
    rw [e] at hmem
    push_cast at hmem
    rcases P.isPrime.mem_or_mem hmem with h | h
    · exact ⟨_, hp, h⟩
    · refine ih _ ?_ hm0 h
      have := hp.two_le
      have : 0 < n / n.minFac := Nat.pos_of_ne_zero hm0
      conv_rhs => rw [e]
      nlinarith

theorem prime_eq_of_mem (P : HeightOneSpectrum (𝓞 E)) {ℓ ℓ' : ℕ} (h : ℓ.Prime) (h' : ℓ'.Prime)
    (hm : (ℓ : 𝓞 E) ∈ P.asIdeal) (hm' : (ℓ' : 𝓞 E) ∈ P.asIdeal) : ℓ = ℓ' := by
  by_contra hne
  exact natCast_not_mem P h hm (by rwa [Nat.prime_dvd_prime_iff_eq h h']) hm'

theorem ord_pow (P : HeightOneSpectrum (𝓞 E)) {x : E} (hx : x ≠ 0) (n : ℕ) :
    ord P (x ^ n) = n * ord P x := by
  induction n with
  | zero => simp [ord_one]
  | succ n ih => rw [pow_succ, ord_mul P (pow_ne_zero _ hx) hx, ih]; push_cast; ring

theorem ord_zpow (P : HeightOneSpectrum (𝓞 E)) {x : E} (hx : x ≠ 0) (n : ℤ) :
    ord P (x ^ n) = n * ord P x := by
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_coe, zpow_natCast]; exact ord_pow P hx n
  | negSucc n => rw [zpow_negSucc, ord_inv, ord_pow P hx, Int.negSucc_eq]; push_cast; ring

theorem ord_prod (P : HeightOneSpectrum (𝓞 E)) {ι : Type} (s : Finset ι) (g : ι → E)
    (hg : ∀ i ∈ s, g i ≠ 0) : ord P (∏ i ∈ s, g i) = ∑ i ∈ s, ord P (g i) := by
  induction s using Finset.induction_on with
  | empty => simp [ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      ord_mul P (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.2 fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem ord_natCast (P : HeightOneSpectrum (𝓞 E)) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hP : (ℓ : 𝓞 E) ∈ P.asIdeal) {n : ℕ} (hn : n ≠ 0) :
    ord P (n : E) = padicValNat ℓ n * ord P (ℓ : E) := by
  haveI := Fact.mk hℓ
  obtain ⟨m, hm⟩ := pow_padicValNat_dvd (p := ℓ) (n := n)
  have hmd : ¬ ℓ ∣ m := fun h =>
    (pow_succ_padicValNat_not_dvd (p := ℓ) hn) (by conv_rhs => rw [hm]
                                                   rw [pow_succ]; exact mul_dvd_mul_left _ h)
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hm; exact hn hm
  have hl0 : (ℓ : E) ≠ 0 := Nat.cast_ne_zero.2 hℓ.ne_zero
  conv_lhs => rw [hm, Nat.cast_mul, Nat.cast_pow]
  rw [ord_mul P (pow_ne_zero _ hl0) (Nat.cast_ne_zero.2 hm0), ord_pow P hl0,
    ord_natCast_coprime P hℓ hP hmd, add_zero]








end GlobalTheory.LocalDivisor
