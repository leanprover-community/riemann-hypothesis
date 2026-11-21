import Formalism.PeriodIntegrals.FinOrdRedOne
import Mathlib

section
noncomputable section

namespace PI.FinOrdRedOne.Core

open Matrix Finset

variable {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n]

def PDvd (q : R) (k : ℕ) (A : Matrix n n R) : Prop :=
  ∃ X : Matrix n n R, A = q ^ k • X

lemma pdvd_add {q : R} {k : ℕ} {A B : Matrix n n R} (hA : PDvd q k A) (hB : PDvd q k B) :
    PDvd q k (A + B) := by
  obtain ⟨X, rfl⟩ := hA
  obtain ⟨Y, rfl⟩ := hB
  exact ⟨X + Y, by rw [smul_add]⟩

lemma pdvd_zero (q : R) (k : ℕ) : PDvd q k (0 : Matrix n n R) := ⟨0, by rw [smul_zero]⟩

lemma pdvd_neg {q : R} {k : ℕ} {A : Matrix n n R} (hA : PDvd q k A) : PDvd q k (-A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨-X, by rw [smul_neg]⟩

lemma pdvd_mono {q : R} {k m : ℕ} (h : m ≤ k) {A : Matrix n n R} (hA : PDvd q k A) :
    PDvd q m A := by
  obtain ⟨X, rfl⟩ := hA
  refine ⟨q ^ (k - m) • X, ?_⟩
  rw [smul_smul, ← pow_add, Nat.add_sub_cancel' h]

lemma pdvd_smul {q : R} {k : ℕ} {A : Matrix n n R} (c : R) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  obtain ⟨X, rfl⟩ := hA
  exact ⟨c • X, by rw [smul_comm]⟩

lemma pdvd_nsmul {q : R} {k : ℕ} {A : Matrix n n R} (c : ℕ) (hA : PDvd q k A) :
    PDvd q k (c • A) := by
  rw [← Nat.cast_smul_eq_nsmul R]
  exact pdvd_smul _ hA

lemma pdvd_sum {q : R} {k : ℕ} {ι : Type*} (s : Finset ι) (f : ι → Matrix n n R)
    (h : ∀ i ∈ s, PDvd q k (f i)) : PDvd q k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PDvd q k) (fun _ _ ha hb => pdvd_add ha hb) (pdvd_zero q k) h

lemma pdvd_pow_smul (q : R) (a m : ℕ) (X : Matrix n n R) :
    PDvd q (a * m) ((q ^ a • X) ^ m) :=
  ⟨X ^ m, by rw [smul_pow, ← pow_mul]⟩

lemma one_add_pow_eq (D : Matrix n n R) (k : ℕ) :
    (1 + D) ^ (k + 2) = ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2)
      + (k + 2) • D + 1 := by
  rw [add_comm (1 : Matrix n n R) D, (Commute.one_right D).add_pow,
    Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [one_pow, mul_one, ← nsmul_eq_mul', Nat.choose_one_right, Nat.choose_zero_right,
    pow_zero, pow_one, one_smul, zero_add]

lemma smul_cancel [IsDomain R] {c : R} (hc : c ≠ 0) {X Y : Matrix n n R} (h : c • X = c • Y) :
    X = Y := by
  ext i j
  have := congrFun (congrFun h i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

theorem step [IsDomain R] (p : ℕ) (hp : p.Prime) (hp3 : 3 ≤ p) (hp0 : (p : R) ≠ 0)
    (hunit : ∀ l : ℕ, l.Prime → l ≠ p → IsUnit (l : R))
    (l : ℕ) (hl : l.Prime) (X : Matrix n n R) (a : ℕ) (ha : 1 ≤ a)
    (hpow : (1 + (p : R) ^ a • X) ^ l = 1) : PDvd (p : R) (a + 1) ((p : R) ^ a • X) := by
  set D : Matrix n n R := (p : R) ^ a • X with hD
  obtain ⟨k, rfl⟩ : ∃ k, l = k + 2 := ⟨l - 2, by have := hl.two_le; omega⟩
  rw [one_add_pow_eq] at hpow
  set S := ∑ i ∈ range (k + 1), (k + 2).choose (i + 2) • D ^ (i + 2) with hS
  have hlin : (k + 2) • D = -S := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    have := congrArg (· - (1 : Matrix n n R)) hpow
    simpa only [add_sub_cancel_right, sub_self] using this
  by_cases hlp : k + 2 = p
  ·
    have hS2 : PDvd (p : R) (a + 2) S := by
      refine pdvd_sum _ _ fun i hi => ?_
      have hi' : i + 2 ≤ p := by rw [Finset.mem_range] at hi; omega
      rcases lt_or_eq_of_le hi' with hlt | heq
      · obtain ⟨c, hc⟩ := hp.dvd_choose_self (by omega : i + 2 ≠ 0) hlt
        rw [hlp, hc, mul_nsmul]
        refine pdvd_nsmul _ ?_
        rw [← Nat.cast_smul_eq_nsmul R]
        obtain ⟨Y, hY⟩ := pdvd_pow_smul (p : R) a (i + 2) X
        refine pdvd_mono (k := 1 + a * (i + 2)) (by nlinarith) ⟨Y, ?_⟩
        rw [hD, hY, smul_smul, ← pow_succ', add_comm]
      · refine pdvd_nsmul _ ?_
        refine pdvd_mono (k := a * (i + 2)) ?_ (pdvd_pow_smul (p : R) a (i + 2) X)
        rw [heq]; nlinarith
    have hpD : PDvd (p : R) (a + 2) ((p : R) • D) := by
      rw [← hlp] at hS2 ⊢
      have := pdvd_neg hS2
      rw [← hlin, ← Nat.cast_smul_eq_nsmul R] at this
      push_cast at this ⊢
      exact this
    obtain ⟨Y, hY⟩ := hpD
    refine ⟨Y, ?_⟩
    have hne : (p : R) ^ (a + 1) ≠ 0 := pow_ne_zero _ hp0
    have hXY : X = (p : R) • Y := by
      apply smul_cancel hne
      rw [hD, smul_smul, ← pow_succ'] at hY
      rw [hY, smul_smul, ← pow_succ]
    rw [hD, hXY, smul_smul, ← pow_succ]
  ·
    have hS1 : PDvd (p : R) (a + 1) S := by
      refine pdvd_sum _ _ fun i _ => pdvd_nsmul _ ?_
      exact pdvd_mono (k := a * (i + 2)) (by nlinarith) (pdvd_pow_smul (p : R) a (i + 2) X)
    obtain ⟨u, hu⟩ := hunit (k + 2) hl hlp
    have h1 : PDvd (p : R) (a + 1) (((k + 2 : ℕ) : R) • D) := by
      rw [Nat.cast_smul_eq_nsmul, hlin]
      exact pdvd_neg hS1
    have h2 := pdvd_smul ((u⁻¹ : Rˣ) : R) h1
    rwa [← hu, smul_smul, Units.inv_mul, one_smul] at h2


theorem isUnit_natCast_of_ne [IsLocalRing R] (p : ℕ) (hp : p.Prime)
    (hpM : (p : R) ∈ IsLocalRing.maximalIdeal R) (l : ℕ) (hl : l.Prime) (hlp : l ≠ p) :
    IsUnit (l : R) := by
  by_contra h
  have hlM : (l : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; exact h
  have hcop : IsCoprime (l : ℤ) (p : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hl hp).mpr hlp)
  obtain ⟨u, v, huv⟩ := hcop
  have h1 : ((u : R) * l + (v : R) * p) = 1 := by
    have := congrArg (Int.cast : ℤ → R) huv
    push_cast at this
    exact this
  have : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
    rw [← h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hlM) (Ideal.mul_mem_left _ _ hpM)
  exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr this)



end PI.FinOrdRedOne.Core
end
end

section
noncomputable section

namespace PI.FinOrdRedOne.Bridge

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Ideal WithZero

variable {E : Type} [Field E] [NumberField E]

theorem natCast_not_mem_sq (p : ℕ) (hp : p.Prime) (hU : Unram E p) (P : HeightOneSpectrum (𝓞 E))
    (hpP : (p : 𝓞 E) ∈ P.asIdeal) : (p : 𝓞 E) ∉ P.asIdeal ^ 2 := by
  have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hspan : (span {(p : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible hprime.irreducible
  have hle : span {(p : ℤ)} ≤ P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact hpP
  have hne : P.asIdeal.comap (algebraMap ℤ (𝓞 E)) ≠ ⊤ := (P.isPrime.comap _).ne_top
  have heq : span {(p : ℤ)} = P.asIdeal.comap (algebraMap ℤ (𝓞 E)) := hspan.eq_of_le hne hle
  have hlo : P.asIdeal.LiesOver (span {(p : ℤ)}) := ⟨heq⟩
  have he : P.asIdeal.ramificationIdx ℤ = 1 := @hU P.asIdeal P.isPrime hlo
  have hbot : span {(p : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hp.ne_zero
  have := P.isPrime
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (span {(p : ℤ)}) P.asIdeal hbot] at he
  have hmap : (span {(p : ℤ)}).map (algebraMap ℤ (𝓞 E)) ≤ P.asIdeal :=
    Ideal.map_le_iff_le_comap.mpr hle
  have hiff := Ideal.ramificationIdx'_ne_one_iff (p := span {(p : ℤ)}) (P := P.asIdeal) hmap
  intro hsq
  apply hiff.mpr _ he
  rw [Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_le, Set.singleton_subset_iff]
  exact hsq

theorem intValuation_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    P.intValuation (p : 𝓞 E) = exp (-1 : ℤ) := by
  have h1 := (P.intValuation_le_pow_iff_mem (p : 𝓞 E) 1).mpr (by rw [pow_one]; exact hpP)
  have h2 : ¬ P.intValuation (p : 𝓞 E) ≤ exp (-((2 : ℕ) : ℤ)) := fun h =>
    natCast_not_mem_sq p hp hU P hpP ((P.intValuation_le_pow_iff_mem (p : 𝓞 E) 2).mp h)
  have hx0 : P.intValuation (p : 𝓞 E) ≠ 0 := by
    intro h; apply h2; rw [h]; exact zero_le
  rw [← exp_log hx0] at h1 h2 ⊢
  rw [exp_le_exp] at h1 h2
  rw [exp_inj]
  push_cast at h1 h2
  omega

theorem valued_natCast (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    Valued.v ((p : ℕ) : P.adicCompletion E) = exp (-1 : ℤ) := by
  have h1 := P.valuedAdicCompletion_eq_valuation (K := E) ((p : ℕ) : 𝓞 E)
  rw [valuation_of_algebraMap, intValuation_natCast p hp hU P hpP] at h1
  simp only [map_natCast] at h1
  exact h1

theorem natCast_ne_zero (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    ((p : ℕ) : OP E P) ≠ 0 := by
  intro h
  have h1 := valued_natCast p hp hU P hpP
  have h2 := congrArg (fun z : OP E P => (z : P.adicCompletion E)) h
  push_cast at h2
  rw [h2, map_zero] at h1
  exact exp_ne_zero h1.symm

theorem maximalIdeal_eq (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) :
    IsLocalRing.maximalIdeal (OP E P) = span {((p : ℕ) : OP E P)} := by
  have hint := HeightOneSpectrum.adicCompletionIntegers.integers (K := E) (v := P)
  have hvp := valued_natCast p hp hU P hpP
  have hp0 : ((p : ℕ) : P.adicCompletion E) ≠ 0 := by
    intro h; rw [h, map_zero] at hvp; exact exp_ne_zero hvp.symm
  apply le_antisymm
  · intro x hx
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one] at hx
    have hle : Valued.v (x : P.adicCompletion E) ≤ 1 := x.2
    have hlt : Valued.v (x : P.adicCompletion E) < 1 := lt_of_le_of_ne hle hx
    have hle1 : Valued.v (x : P.adicCompletion E) ≤ exp (-1 : ℤ) := by
      by_cases h0 : Valued.v (x : P.adicCompletion E) = 0
      · rw [h0]; exact zero_le
      rw [← exp_log h0] at hlt ⊢
      rw [← exp_zero, exp_lt_exp] at hlt
      rw [exp_le_exp]
      omega
    have hy : (x : P.adicCompletion E) / (p : P.adicCompletion E) ∈
        P.adicCompletionIntegers E := by
      rw [mem_adicCompletionIntegers, map_div₀, hvp, div_le_one₀ (zero_lt_iff.mpr exp_ne_zero)]
      exact hle1
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hy⟩, ?_⟩
    apply Subtype.ext
    push_cast
    exact div_mul_cancel₀ _ hp0
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff, hint.isUnit_iff_valuation_eq_one]
    change Valued.v (((p : ℕ) : OP E P) : P.adicCompletion E) ≠ 1
    push_cast
    rw [hvp, ← exp_zero, Ne, exp_inj]
    omega

theorem eq_zero_of_forall_dvd (p : ℕ) (hp : p.Prime) (hU : Unram E p)
    (P : HeightOneSpectrum (𝓞 E)) (hpP : (p : 𝓞 E) ∈ P.asIdeal) (x : OP E P)
    (hx : ∀ k : ℕ, ((p : ℕ) : OP E P) ^ k ∣ x) : x = 0 := by
  have hne : IsLocalRing.maximalIdeal (OP E P) ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal _).ne_top
  have hK := Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal (OP E P)) hne
  rw [← Ideal.mem_bot, ← hK, Ideal.mem_iInf]
  intro k
  rw [maximalIdeal_eq p hp hU P hpP, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact hx k

end PI.FinOrdRedOne.Bridge
end
end
