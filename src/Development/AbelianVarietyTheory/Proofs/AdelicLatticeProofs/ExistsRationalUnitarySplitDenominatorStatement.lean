import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryQuasiReflectionLaws
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsDenominatorPrimesPrescribed
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryMatrixEqProdQuasiReflectionsStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatricesStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitaryGroupWeakApproximationAtPrimesStatement

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem intValuation_map_le_of_map_le {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (P : HeightOneSpectrum R) (h : P.asIdeal.map σ ≤ P.asIdeal) (a : R) :
    P.intValuation (σ a) ≤ P.intValuation a := by
  by_cases ha : a = 0
  · simp [ha]
  have h1 : P.intValuation a = WithZero.exp (-((Associates.mk P.asIdeal).count
      (Associates.mk (Ideal.span {a} : Ideal R)).factors : ℕ) : ℤ) := P.intValuation_if_neg ha
  set k := (Associates.mk P.asIdeal).count (Associates.mk (Ideal.span {a} : Ideal R)).factors
  have h2 : a ∈ P.asIdeal ^ k := (P.intValuation_le_pow_iff_mem a k).1 h1.le
  rw [h1, P.intValuation_le_pow_iff_mem]
  have h3 : (P.asIdeal ^ k).map σ ≤ P.asIdeal ^ k := by
    rw [Ideal.map_pow]
    exact Ideal.pow_right_mono h k
  exact h3 (Ideal.mem_map_of_mem σ h2)

theorem valuation_eq_one_of_norm_one_of_not_moved :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E),
      (∀ x, c (c x) = x) → ∀ (u : E) (P : HeightOneSpectrum (𝓞 E)), u * c u = 1 →
        ¬ Moved c P.asIdeal → P.valuation E u = 1 := by
  intro F E _ _ _ _ _ c hc u P hu hP
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (c : E →+* E)
  have hσ : ∀ a : 𝓞 E, ((σ a : 𝓞 E) : E) = c (a : E) := fun a => rfl
  have hσσ : ∀ a, σ (σ a) = a := fun a => by
    apply RingOfIntegers.ext
    rw [hσ, hσ, hc]
  have hle : P.asIdeal.map σ ≤ P.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    by_contra hb
    exact hP ⟨a, ha, σ a, hσ a, hb⟩
  have hint : ∀ a, P.intValuation (σ a) = P.intValuation a := fun a => by
    apply le_antisymm (intValuation_map_le_of_map_le σ P hle a)
    have := intValuation_map_le_of_map_le σ P hle (σ a)
    rwa [hσσ] at this
  have hval : ∀ a : 𝓞 E, P.valuation E (c (a : E)) = P.valuation E (a : E) := fun a => by
    rw [← hσ]
    change P.valuation E (algebraMap (𝓞 E) E (σ a)) = P.valuation E (algebraMap (𝓞 E) E a)
    rw [P.valuation_of_algebraMap, P.valuation_of_algebraMap, hint]
  have hcu : P.valuation E (c u) = P.valuation E u := by
    obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) u
    rw [map_div₀, map_div₀, map_div₀]
    exact congrArg₂ (· / ·) (hval a) (hval b)
  have h2 : P.valuation E u ^ 2 = 1 := by
    have := congrArg (P.valuation E) hu
    rwa [map_mul, hcu, map_one, ← sq] at this
  exact (pow_eq_one_iff_of_nonneg zero_le' two_ne_zero).1 h2

end GlobalTheory.UnRep
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.NormOne

lemma exists_split (N : ℕ) : ∀ M : ℕ, 0 < M → ∃ D₁ D₂ k : ℕ, M = D₁ * D₂ ∧ D₁ ∣ N ^ k ∧ D₂.Coprime N := by
  intro M
  induction M using Nat.strong_induction_on with
  | _ M ih =>
    intro hM
    by_cases h : M.Coprime N
    · exact ⟨1, M, 0, by simp, by simp, h⟩
    · obtain ⟨M', hM'⟩ := Nat.gcd_dvd_left M N
      have hg : 0 < Nat.gcd M N := Nat.gcd_pos_of_pos_left N hM
      have hg1 : Nat.gcd M N ≠ 1 := h
      have hpos : 0 < M' := by
        rcases Nat.eq_zero_or_pos M' with h0 | h0
        · rw [h0, mul_zero] at hM'; omega
        · exact h0
      have hlt : M' < M := by
        have h2 : 2 ≤ Nat.gcd M N := by omega
        nlinarith
      obtain ⟨D₁, D₂, k, h1, h2, h3⟩ := ih M' hlt hpos
      refine ⟨Nat.gcd M N * D₁, D₂, k + 1, by rw [mul_assoc, ← h1]; exact hM', ?_, h3⟩
      rw [pow_succ']
      exact Nat.mul_dvd_mul (Nat.gcd_dvd_right M N) h2

variable {E : Type} [Field E] [NumberField E]

lemma exists_nat_multiple (α : 𝓞 E) (h : α ≠ 0) : ∃ n : ℕ, 0 < n ∧ ∃ γ : 𝓞 E, (n : 𝓞 E) = α * γ := by
  refine ⟨Ideal.absNorm (Ideal.span {α}), Nat.pos_of_ne_zero ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact h
  · exact Ideal.mem_span_singleton.mp (Ideal.absNorm_mem _)

lemma one_add_ne_zero (N : ℕ) (hN : N ≠ 1) (z : 𝓞 E) : 1 + (N : 𝓞 E) * z ≠ 0 := by
  intro h
  have hu : IsUnit (N : 𝓞 E) := IsUnit.of_mul_eq_one (-z) (by linear_combination -h)
  have h2 := hu.map (Algebra.norm ℤ)
  have h3 : (N : 𝓞 E) = algebraMap ℤ (𝓞 E) (N : ℤ) := by simp
  rw [h3, Algebra.norm_algebraMap, isUnit_pow_iff (Module.finrank_pos (R := ℤ) (M := 𝓞 E)).ne',
    Int.isUnit_iff] at h2
  omega

lemma exists_coprime_multiple (N : ℕ) (hN : 0 < N) (z : 𝓞 E) (hw : 1 + (N : 𝓞 E) * z ≠ 0) :
    ∃ t : ℕ, t.Coprime N ∧ ∃ γ : 𝓞 E, (t : 𝓞 E) = (1 + (N : 𝓞 E) * z) * γ := by
  set I : Ideal (𝓞 E) := Ideal.span {1 + (N : 𝓞 E) * z} with hI
  have hb : I ≠ ⊥ := by rw [hI, Ne, Ideal.span_singleton_eq_bot]; exact hw
  have : Finite (𝓞 E ⧸ I) := Ideal.finiteQuotientOfFreeOfNeBot I hb
  have h0 : Ideal.Quotient.mk I (1 + (N : 𝓞 E) * z) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
  have hu : IsUnit (Ideal.Quotient.mk I (N : 𝓞 E)) :=
    IsUnit.of_mul_eq_one (Ideal.Quotient.mk I (-z)) (by
      rw [map_add, map_one, map_mul] at h0
      rw [map_neg]; linear_combination -h0)
  obtain ⟨v, hv⟩ := hu
  obtain ⟨k, hk, hvk⟩ := isOfFinOrder_iff_pow_eq_one.mp (isOfFinOrder_of_finite v)
  have h1 : 1 ≤ N ^ k := Nat.one_le_pow _ _ hN
  refine ⟨N ^ k - 1, ?_, ?_⟩
  · have : (N ^ k - 1).Coprime (N ^ k) := by
      have := (Nat.coprime_self_sub_left h1).mpr (Nat.coprime_one_left _)
      exact this
    exact (Nat.coprime_pow_right_iff hk _ _).mp this
  · apply Ideal.mem_span_singleton.mp
    rw [← hI, ← Ideal.Quotient.eq_zero_iff_mem, Nat.cast_sub h1, Nat.cast_pow, Nat.cast_one, map_sub,
      map_pow, ← hv, ← Units.val_pow_eq_pow_val, hvk]
    simp

lemma val_eq_one (P : HeightOneSpectrum (𝓞 E)) (d : 𝓞 E) (hd : d ∉ P.asIdeal) :
    P.valuation E (d : E) = 1 := by
  have h1 : P.valuation E (algebraMap (𝓞 E) E d) ≤ 1 := P.valuation_le_one d
  have h2 : ¬ P.valuation E (algebraMap (𝓞 E) E d) < 1 := by
    rw [HeightOneSpectrum.valuation_lt_one_iff_mem]; exact hd
  exact le_antisymm h1 (not_lt.mp h2)

lemma val_le_of_mul (P : HeightOneSpectrum (𝓞 E)) (x y : E) (d : 𝓞 E) (hd : d ∉ P.asIdeal)
    (h : x * d = y) (hy : P.valuation E y ≤ 1) : P.valuation E x ≤ 1 := by
  rw [← h, map_mul, val_eq_one P d hd, mul_one] at hy
  exact hy

lemma val_le_of_unit (P : HeightOneSpectrum (𝓞 E)) (y : E) (D : ℕ) (hD : (D : 𝓞 E) ∉ P.asIdeal)
    (hy : P.valuation E y = 1) : P.valuation E ((y - 1) / D) ≤ 1 := by
  have hD0 : (D : E) ≠ 0 := by
    intro h
    have : D = 0 := by exact_mod_cast h
    apply hD; simp [this]
  refine val_le_of_mul P _ (y - 1) (D : 𝓞 E) hD (by simp [hD0]) ?_
  exact Valuation.map_sub_le _ hy.le (by simp)

lemma val_le_of_cong (P : HeightOneSpectrum (𝓞 E)) (N D D₁ D₂ k n : ℕ) (hD0 : 0 < D)
    (hM : D * n = D₁ * D₂) (h1 : D₁ ∣ N ^ k) (hN : (N : 𝓞 E) ∉ P.asIdeal) (hD : (D : 𝓞 E) ∈ P.asIdeal)
    (α β p b : 𝓞 E) (hab : p * D₂ + b = 1) :
    P.valuation E ((((p * D₂ * α + b : 𝓞 E) : E) / ((p * D₂ * β + b : 𝓞 E) : E) - 1) / D) ≤ 1 := by
  have hP := P.isPrime
  have hM' : (D : 𝓞 E) * n = D₁ * D₂ := by exact_mod_cast hM
  have hD₁ : (D₁ : 𝓞 E) ∉ P.asIdeal := by
    intro h
    obtain ⟨e, he⟩ := h1
    apply hN
    apply hP.mem_of_pow_mem k
    have : (N : 𝓞 E) ^ k = D₁ * e := by exact_mod_cast he
    rw [this]; exact Ideal.mul_mem_right _ _ h
  have hD₂ : (D₂ : 𝓞 E) ∈ P.asIdeal := by
    have : (D₁ : 𝓞 E) * D₂ ∈ P.asIdeal := hM' ▸ Ideal.mul_mem_right _ _ hD
    exact (hP.mem_or_mem this).resolve_left hD₁
  have hβ : p * D₂ * β + b ∉ P.asIdeal := by
    intro h
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (p * D₂ * β + b) + D₂ * (p * (1 - β)) := by linear_combination -hab
    rw [this]
    exact add_mem h (Ideal.mul_mem_right _ _ hD₂)
  have hβ0 : ((p * D₂ * β + b : 𝓞 E) : E) ≠ 0 := by
    intro h
    apply hβ
    have : (p * D₂ * β + b : 𝓞 E) = 0 := by exact_mod_cast h
    rw [this]; exact zero_mem _
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD0.ne'
  have hME : (D : E) * n = D₁ * D₂ := by exact_mod_cast hM
  refine val_le_of_mul P _ ((n * p * (α - β) : 𝓞 E) : E) (D₁ * (p * D₂ * β + b))
    (fun h => (hP.mem_or_mem h).elim hD₁ hβ) ?_ (P.valuation_le_one _)
  rw [RingOfIntegers.coe_eq_algebraMap] at hβ0
  simp only [RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_sub, map_natCast] at hβ0 ⊢
  field_simp
  linear_combination (-(algebraMap (𝓞 E) E p) * (algebraMap (𝓞 E) E α - algebraMap (𝓞 E) E β)) * hME

variable {F : Type} [Field F] [Algebra F E]

omit [NumberField E] in
lemma exists_conj (c : E ≃ₐ[F] E) (x : 𝓞 E) : ∃ y : 𝓞 E, (y : E) = c x :=
  ⟨⟨c x, (RingOfIntegers.isIntegral_coe x).map (c : E →+* E).toIntAlgHom⟩, rfl⟩

lemma hilbert90_matrix_subalgebra_norm_one (c : E ≃ₐ[F] E) (hc : ∀ x, c (c x) = x) (hc1 : c ≠ 1) (u : E) (hu : u * c u = 1) :
    ∃ α : 𝓞 E, α ≠ 0 ∧ u * c α = α := by
  have h0 : ∃ x : E, x ≠ 0 ∧ u * c x = x := by
    have key : ∀ θ : E, u * c (θ + u * c θ) = θ + u * c θ := by
      intro θ
      rw [map_add, map_mul, hc]
      linear_combination θ * hu
    by_cases h : 1 + u * c 1 = 0
    · have : ∃ θ, c θ ≠ θ := by
        by_contra hh
        push Not at hh
        exact hc1 (AlgEquiv.ext hh)
      obtain ⟨θ, hθ⟩ := this
      refine ⟨_, ?_, key θ⟩
      rw [map_one] at h
      intro h2
      apply hθ
      linear_combination c θ * h - h2
    · exact ⟨_, h, key 1⟩
  obtain ⟨x, hx, hux⟩ := h0
  obtain ⟨p, q, hq, hpq⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  obtain ⟨q', hq'⟩ := exists_conj c q
  have hq0 : (q : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero hq
    exact_mod_cast this
  have hp : (p : E) = x * q := by
    rw [← hpq]; exact (div_mul_cancel₀ _ hq0).symm
  have e : ((p * q' : 𝓞 E) : E) = x * q * c q := by
    rw [← hp, ← hq']; rfl
  refine ⟨p * q', ?_, ?_⟩
  · intro h
    rw [h] at e
    have hcq : c q ≠ 0 := by simpa using hq0
    exact mul_ne_zero (mul_ne_zero hx hq0) hcq (e.symm.trans rfl)
  · rw [e, map_mul, map_mul, hc]
    linear_combination (c q * q) * hux

end GlobalTheory.UnRep.NormOne

open GlobalTheory.UnRep.NormOne in

theorem GlobalTheory.UnRep.normOne_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  intro F E _ _ _ _ _ c hc hc1 u N D hu hN hD
  by_cases hN1 : N = 1
  · subst hN1
    refine ⟨1, by simp, ⟨0, by simp, 0, by simp⟩, 1, ⟨one_ne_zero, fun P hP h => Or.inr (by simpa using h)⟩,
      ⟨0, by simp⟩, 0, by simp⟩
  obtain ⟨α, hα, huα⟩ := hilbert90_matrix_subalgebra_norm_one c hc hc1 u hu
  obtain ⟨β, hβc⟩ := exists_conj c α
  have hαE : (α : E) ≠ 0 := by exact_mod_cast hα
  have hβE : (β : E) ≠ 0 := by rw [hβc]; simpa using hαE
  have hβ : β ≠ 0 := by intro h; apply hβE; rw [h]; rfl
  obtain ⟨n₁, hn₁, γ₁, hγ₁⟩ := exists_nat_multiple α hα
  obtain ⟨n₂, hn₂, γ₂, hγ₂⟩ := exists_nat_multiple β hβ
  obtain ⟨D₁, D₂, k, hM, h1, h2⟩ := exists_split N (D * (n₁ * n₂)) (by positivity)
  have hco : D₂.Coprime (D₁ * N) :=
    Nat.Coprime.mul_right (Nat.Coprime.coprime_dvd_right h1 (Nat.Coprime.pow_right k h2)) h2
  obtain ⟨p, q, hpq⟩ := Nat.isCoprime_iff_coprime.mpr hco
  have hpq' : (p : 𝓞 E) * D₂ + q * (D₁ * N) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hpq
  have hM' : (D : 𝓞 E) * (α * γ₁ * (β * γ₂)) = D₁ * D₂ := by
    rw [← hγ₁, ← hγ₂]; exact_mod_cast hM
  set b : 𝓞 E := q * (D₁ * N) with hb
  set α' : 𝓞 E := p * D₂ * α + b with hα'
  set β' : 𝓞 E := p * D₂ * β + b with hβ'
  have hcα' : c α' = β' := by
    simp only [hα', hβ', hb, RingOfIntegers.coe_eq_algebraMap, map_mul, map_add, map_natCast, map_intCast] at hβc ⊢
    rw [hβc]
  have hcβ' : c β' = α' := by rw [← hcα', hc]
  set z : 𝓞 E := -2 * q * D₁ + q * D₁ * b + p * q * (D * α * γ₁ * γ₂) with hz
  have hw := one_add_ne_zero N hN1 z
  obtain ⟨t, ht, γ, hγ⟩ := exists_coprime_multiple N hN z hw
  have e1 : p * D₂ * β' = β * (1 + N * z) := by
    rw [hβ', hz, hb]
    linear_combination (β * (p * D₂ + 1 - q * (D₁ * N))) * hpq' - (p * q * N : 𝓞 E) * hM'
  have hβ'0 : β' ≠ 0 := by
    intro h
    rw [h, mul_zero] at e1
    exact mul_ne_zero hβ hw e1.symm
  have hβ'E : (β' : E) ≠ 0 := by exact_mod_cast hβ'0
  have hα'E : (α' : E) ≠ 0 := by rw [← hcβ']; simpa using hβ'E
  have hu' : (α' : E) / β' * c ((α' : E) / β') = 1 := by
    rw [map_div₀, hcα', hcβ']; field_simp
  have hDE : (D : E) ≠ 0 := by exact_mod_cast hD.ne'
  refine ⟨(α' : E) / β', hu', ⟨t, ht, γ * p * q * N * γ₁ * γ₂ * (β - α), ?_⟩, ?_⟩
  · have hu2 : u = (α : E) / β := by rw [eq_div_iff hβE, hβc, huα]
    have e2 : (t : 𝓞 E) * (α' * β - β' * α) = D * (γ * p * q * N * γ₁ * γ₂ * (β - α)) * (β' * α) := by
      apply mul_left_cancel₀ hβ
      have e3 : α' * β - β' * α = b * (β - α) := by rw [hα', hβ']; ring
      rw [e3, hγ, hb]
      linear_combination (-(γ * q * D₁ * N * (β - α))) * e1 - (γ * p * q * N * (β - α) * β') * hM'
    generalize γ * p * q * N * γ₁ * γ₂ * (β - α) = g at e2 ⊢
    have e4 := congrArg (algebraMap (𝓞 E) E) e2
    simp only [map_mul, map_sub, map_natCast] at e4
    rw [hu2]
    field_simp
    simp only [RingOfIntegers.coe_eq_algebraMap] at e4 ⊢
    linear_combination e4
  · have hM2 : D * (n₁ * n₂) = D₁ * D₂ := hM
    obtain ⟨s, hs0, hsP, hs⟩ := GlobalTheory.UnRep.exists_denominator_primes_prescribed E (fun P => Moved c P ∨ (N : 𝓞 E) ∈ P) Bool
      (fun i => if i then ((α' : E) / β' - 1) / D else (((α' : E) / β')⁻¹ - 1) / D) (by
        intro i P hQ
        rw [not_or] at hQ
        have hv := GlobalTheory.UnRep.valuation_eq_one_of_norm_one_of_not_moved F E c hc _ P hu' hQ.1
        by_cases hDP : (D : 𝓞 E) ∈ P.asIdeal
        · cases i
          · simp only [Bool.false_eq_true, if_false, inv_div]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP β α p b hpq'
          · simp only [if_true]
            exact val_le_of_cong P N D D₁ D₂ k _ hD hM2 h1 hQ.2 hDP α β p b hpq'
        · cases i
          · simp only [Bool.false_eq_true, if_false]
            exact val_le_of_unit P _ D hDP (by rw [map_inv₀, hv, inv_one])
          · simp only [if_true]
            exact val_le_of_unit P _ D hDP hv)
    obtain ⟨b₁, hb₁⟩ := hs true
    obtain ⟨b₂, hb₂⟩ := hs false
    simp only [if_true] at hb₁
    simp only [Bool.false_eq_true, if_false] at hb₂
    refine ⟨s, ⟨hs0, hsP⟩, ⟨b₁, ?_⟩, b₂, ?_⟩
    · rw [← hb₁, mul_left_comm, mul_div_cancel₀ _ hDE]
    · rw [← hb₂, mul_left_comm, mul_div_cancel₀ _ hDE]
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normOne_approximation_at_level_primes : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E), (∀ x, c (c x) = x) → c ≠ 1 → ∀ (u : E) (N D : ℕ), u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ (∃ t : ℕ, t.Coprime N ∧ ∃ b : 𝓞 E, (t : E) * (u' / u - 1) = (D : E) * (b : E)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ (∃ b : 𝓞 E, (s : E) * (u' - 1) = (D : E) * (b : E)) ∧ ∃ b : 𝓞 E, (s : E) * (u'⁻¹ - 1) = (D : E) * (b : E) := by
  first | exact @GlobalTheory.UnRep.normOne_approx | exact GlobalTheory.UnRep.normOne_approx | (intros; apply GlobalTheory.UnRep.normOne_approx <;> assumption)
end

section
namespace GlobalTheory.NatMulIntegral

open NumberField

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hi⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hi
  have hc : ((y.natAbs : ℕ) : E) = ((y.natAbs : ℤ) : E) := (Int.cast_natCast _).symm
  rcases Int.natAbs_eq y with h | h
  · rw [hc, ← h]
    exact hi
  · have h' : (y.natAbs : ℤ) = -y := by omega
    rw [hc, h', Int.cast_neg, neg_mul]
    exact hi.neg

theorem nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (d : ℕ) {x : Fin n → E} (hx : x ∈ L) :
    (d : E) • x ∈ L := by
  rw [Nat.cast_smul_eq_nsmul]
  exact nsmul_mem hx d

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  have hy : y ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hez⟩ := hz
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have h1 := nat_smul_mem L e hdx
    have h2 := nat_smul_mem L d hez
    have : ((d * e : ℕ) : E) • (x + z) = (e : E) • (d : E) • x + (d : E) • (e : E) • z := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (e : E)]
    rw [this]
    exact L.add_mem h1 h2
  | smul a x _ hx =>
    obtain ⟨d, hd, hdx⟩ := hx
    obtain ⟨e, he, hea⟩ := exists_nat_mul_isIntegral a
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    let b : RingOfIntegers E := ⟨(e : E) * a, hea⟩
    have h1 : b • (d : E) • x ∈ L := L.smul_mem b hdx
    have : ((d * e : ℕ) : E) • a • x = b • (d : E) • x := by
      rw [← algebraMap_smul E b]
      change _ = ((e : E) * a) • (d : E) • x
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [this]
    exact h1

end GlobalTheory.NatMulIntegral
end

section
namespace GlobalTheory.NatMultipleRingOfIntegers

theorem exists_pos_nat_mul_mem_ringOfIntegers {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : NumberField.RingOfIntegers E, (b : E) = (m : E) * a := by
  have h1 : IsAlgebraic ℚ a := Algebra.IsAlgebraic.isAlgebraic a
  have h2 : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  have hint' : IsIntegral ℤ ((y : E) * a) := by
    simpa [zsmul_eq_mul] using hint
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  have hm : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h | h
    · have e : ((y.natAbs : ℕ) : E) = (y : E) := by
        conv_rhs => rw [h]
        exact (Int.cast_natCast _).symm
      rw [e]; exact hint'
    · have e : ((y.natAbs : ℕ) : E) = -(y : E) := by
        conv_rhs => rw [h]
        rw [Int.cast_neg, neg_neg, Int.cast_natCast]
      rw [e, neg_mul]; exact hint'.neg
  exact ⟨⟨_, hm⟩, rfl⟩

end GlobalTheory.NatMultipleRingOfIntegers
end

section
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ m : ℕ, 0 < m ∧ ∃ b : 𝓞 E, (b : E) = (m : E) * a := by
  first
  | exact @_root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers
  | exact _root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers
  | (apply _root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMultipleRingOfIntegers.exists_pos_nat_mul_mem_ringOfIntegers ..)

theorem exists_nat_smul_mem_of_span {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (y : Fin n → E) : ∃ d : ℕ, 0 < d ∧ (d : E) • y ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem
  | (apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulIntegral.exists_nat_smul_mem ..)

theorem exists_nat_smul_map_mem {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG) (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤)
    (φ : (Fin n → E) →ₗ[E] (Fin n → E)) : ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, (d : E) • φ v ∈ L := by
  classical
  choose d hd hdL using exists_nat_smul_mem_of_span L hL
  obtain ⟨S, hS⟩ := hfg
  refine ⟨∏ s ∈ S, d (φ s), Finset.prod_pos fun s _ => hd _, ?_⟩
  intro v hv
  rw [← hS] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul S _ (Finset.mem_coe.1 hx), Nat.cast_mul, mul_smul,
      Nat.cast_smul_eq_nsmul E (∏ s ∈ S.erase x, d (φ s))]
    exact L.toAddSubmonoid.nsmul_mem (hdL _) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    have h1 : φ (a • x) = (a : E) • φ x := φ.map_smul (a : E) x
    rw [h1, smul_comm]
    exact L.smul_mem a hx

theorem exists_refl_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL x u N D hx hu hN hD
  have hap := (GlobalTheory.UnRep.ReflLaws.refl_laws F E c n G hG x hx).1
  let φ : (Fin n → E) →ₗ[E] (Fin n → E) :=
    { toFun := fun v => (hermE c G v x / hermE c G x x) • x
      map_add' := by
        intro v w
        rw [← add_smul, ← add_div]
        congr 2
        simp [hermE, add_mul, Finset.sum_add_distrib]
      map_smul' := by
        intro a v
        rw [RingHom.id_apply, smul_smul, ← mul_div_assoc]
        congr 2
        simp [hermE, Finset.mul_sum, mul_assoc] }
  obtain ⟨d, hd, hdL⟩ := exists_nat_smul_map_mem L hfg hL φ
  have hap' : ∀ a v, refl c G x a *ᵥ v = v + (a - 1) • φ v := by
    intro a v
    rw [hap]
    show _ = v + (a - 1) • ((hermE c G v x / hermE c G x x) • x)
    rw [smul_smul, mul_div_assoc]
  obtain ⟨u', hu', ⟨t, ht, b, hb⟩, s, hs, ⟨b₁, hb₁⟩, b₂, hb₂⟩ :=
    GlobalTheory.T.normOne_approximation_at_level_primes F E c hG.1 hG.2.1 u N (D * d) hu hN (Nat.mul_pos hD hd)
  have key : ∀ (a : E) (b : 𝓞 E), (s : E) * (a - 1) = ((D * d : ℕ) : E) * (b : E) →
      ∀ v ∈ L, s • (refl c G x a *ᵥ v) ∈ L := by
    intro a b hb v hv
    rw [hap', smul_add]
    refine L.add_mem (L.smul_mem s hv) ?_
    have : s • ((a - 1) • φ v) = ((D : 𝓞 E) * b) • ((d : E) • φ v) := by
      show (s : E) • ((a - 1) • φ v) = (((D : 𝓞 E) * b : 𝓞 E) : E) • ((d : E) • φ v)
      rw [smul_smul, smul_smul, hb]
      congr 1
      push_cast
      ring
    rw [this]
    exact L.smul_mem _ (hdL v hv)
  refine ⟨u', hu', ⟨t, ht, fun v hv => ⟨b • ((d : E) • φ v), L.smul_mem b (hdL v hv), ?_⟩⟩,
    s, hs, fun v hv => ⟨key _ _ hb₁ v hv, key _ _ hb₂ v hv⟩⟩
  rw [hap', add_sub_cancel_left, ← Nat.cast_smul_eq_nsmul E t, ← Nat.cast_smul_eq_nsmul E D]
  show _ = (D : E) • ((b : E) • ((d : E) • φ v))
  rw [smul_smul, smul_smul, smul_smul, hb]
  congr 1
  push_cast
  ring

end GlobalTheory.UnRep
end

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_one_reflection_correction_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (x : Fin n → E) (u : E) (N D : ℕ), hermE c G x x ≠ 0 → u * c u = 1 → 0 < N → 0 < D → ∃ u' : E, u' * c u' = 1 ∧ CongAt L N D (refl c G x (u' / u)) ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (refl c G x u' *ᵥ v) ∈ L ∧ s • (refl c G x u'⁻¹ *ᵥ v) ∈ L := by
  atlas_forward_decl GlobalTheory.UnRep.exists_refl_correction
end

section
namespace GlobalTheory.NatMulMem

open NumberField

lemma exists_nat_mul_mem {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  obtain ⟨y, hy, hint⟩ :=
    IsAlgebraic.exists_integral_multiple (R := ℤ) (z := c)
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic c))
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = ((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -((y : ℤ) : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) :
    Submodule.span E (L : Set (Fin n → E)) = ⊤ →
      ∀ x : Fin n → E, ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  intro hspan
  let S : Submodule E (Fin n → E) :=
    { carrier := {x | ∃ d : ℕ, 0 < d ∧ d • x ∈ L}
      add_mem' := by
        rintro x y ⟨a, ha, hx⟩ ⟨b, hb, hy⟩
        refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
        rw [smul_add]
        refine L.add_mem ?_ ?_
        · rw [mul_comm, mul_smul]; exact L.toAddSubmonoid.nsmul_mem hx b
        · rw [mul_smul]; exact L.toAddSubmonoid.nsmul_mem hy a
      zero_mem' := ⟨1, one_pos, by simp⟩
      smul_mem' := by
        rintro c x ⟨a, ha, hx⟩
        obtain ⟨m, hm, hint⟩ := exists_nat_mul_mem c
        refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
        let r : RingOfIntegers E := ⟨(m : E) * c, hint⟩
        have key : (m * a) • (c • x) = r • (a • x) := by
          funext i
          have hr : algebraMap (RingOfIntegers E) E r = (m : E) * c := rfl
          rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Algebra.smul_def r, hr]
          simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_mul]
          ring
        rw [key]; exact L.smul_mem r hx }
  have hle : Submodule.span E (L : Set (Fin n → E)) ≤ S :=
    Submodule.span_le.mpr (fun y hy => ⟨1, one_pos, by simpa using hy⟩)
  intro x
  have hx : x ∈ S := hle (hspan ▸ Submodule.mem_top)
  exact hx

end GlobalTheory.NatMulMem
end

section
open NumberField

namespace GlobalTheory.IntegralMultipleOfVectors

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ (e : ℕ) (b : RingOfIntegers E), 0 < e ∧ (e : E) * a = algebraMap (RingOfIntegers E) E b := by
  have h : IsAlgebraic ℤ a :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hi⟩ := h.exists_integral_multiple
  have hi' : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rcases Int.natAbs_eq y with h1 | h1
    · have : (y.natAbs : E) * a = y • a := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi
    · have : (y.natAbs : E) * a = -(y • a) := by
        conv_rhs => rw [h1]
        simp
      rw [this]; exact hi.neg
  exact ⟨y.natAbs, ⟨_, hi'⟩, Int.natAbs_pos.mpr hy, rfl⟩

theorem exists_nsmul_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (w : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • w ∈ L := by
  have hw : w ∈ Submodule.span E (L : Set (Fin n → E)) := hL ▸ Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, he, hy⟩ := hy
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    rw [smul_add]
    refine L.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact nsmul_mem hx e
    · rw [mul_smul]; exact nsmul_mem hy d
  | smul a x _ hx =>
    obtain ⟨d, hd, hx⟩ := hx
    obtain ⟨e, b, he, hb⟩ := exists_nat_mul_integral a
    refine ⟨e * d, Nat.mul_pos he hd, ?_⟩
    have : (e * d) • a • x = b • d • x := by
      rw [← algebraMap_smul E b, ← hb]
      ext i
      simp
      ring
    rw [this]
    exact L.smul_mem b hx

theorem exists_nsmul_mulVec_mem {E : Type} [Field E] {n : ℕ} [NumberField E]
    (L : Submodule (RingOfIntegers E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • M.mulVec v ∈ L := by
  classical
  obtain ⟨s, hs⟩ := hfg
  choose f hf hmem using fun v => exists_nsmul_mem L hL (M.mulVec v)
  refine ⟨∏ v ∈ s, f v, Finset.prod_pos fun v _ => hf v, fun v hv => ?_⟩
  have hv' : v ∈ Submodule.span (RingOfIntegers E) (s : Set (Fin n → E)) := by
    rw [hs]; exact hv
  clear hv
  induction hv' using Submodule.span_induction with
  | mem x hx =>
    rw [← Finset.prod_erase_mul s f (Finset.mem_coe.mp hx), mul_smul]
    exact nsmul_mem (hmem x) _
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Matrix.mulVec_add, smul_add]
    exact L.add_mem hx hy
  | smul a x _ hx =>
    rw [← algebraMap_smul E a, Matrix.mulVec_smul, algebraMap_smul, smul_comm]
    exact L.smul_mem a hx

end GlobalTheory.IntegralMultipleOfVectors
end

section
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Correct

variable {E : Type} [Field E] {n : ℕ}

theorem exists_nat_smul_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by
  first
  | exact @_root_.GlobalTheory.NatMulMem.main
  | exact _root_.GlobalTheory.NatMulMem.main
  | (apply _root_.GlobalTheory.NatMulMem.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.NatMulMem.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NatMulMem.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NatMulMem.main ..)

theorem exists_nat_mulVec_mem [NumberField E] (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (M : Matrix (Fin n) (Fin n) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ v ∈ L, d • (M *ᵥ v) ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem
  | (apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegralMultipleOfVectors.exists_nsmul_mulVec_mem ..)

theorem congAt_mul {L : Submodule (𝓞 E) (Fin n → E)} {N D : ℕ} {A B : Matrix (Fin n) (Fin n) E}
    (hA : CongAt L N D A) (hB : CongAt L N D B) : CongAt L N D (A * B) := by
  obtain ⟨t₁, c₁, h₁⟩ := hA
  obtain ⟨t₂, c₂, h₂⟩ := hB
  refine ⟨t₁ * t₂, Nat.Coprime.mul_left c₁ c₂, fun v hv => ?_⟩
  obtain ⟨w₂, hw₂, e₂⟩ := h₂ v hv
  have hy : t₂ • (B *ᵥ v) ∈ L := by
    have : t₂ • (B *ᵥ v) = t₂ • v + D • w₂ := by rw [← e₂, smul_sub]; abel
    rw [this]
    exact L.add_mem (nsmul_mem hv _) (nsmul_mem hw₂ _)
  obtain ⟨w₁, hw₁, e₁⟩ := h₁ _ hy
  refine ⟨w₁ + t₁ • w₂, L.add_mem hw₁ (nsmul_mem hw₂ _), ?_⟩
  rw [smul_add, smul_comm D t₁, ← e₁, ← e₂, Matrix.mulVec_smul, Matrix.mulVec_mulVec]
  module

theorem congAt_conj [CharZero E] {L : Submodule (𝓞 E) (Fin n → E)} {N D d e : ℕ} (he : 0 < e)
    {A R R' : Matrix (Fin n) (Fin n) E} (hRR : R * R' = 1)
    (hR : ∀ v ∈ L, d • (R *ᵥ v) ∈ L) (hR' : ∀ v ∈ L, e • (R' *ᵥ v) ∈ L)
    (hA : CongAt L N (D * d * e) A) : CongAt L N D (R * A * R') := by
  obtain ⟨t, ct, h⟩ := hA
  refine ⟨t, ct, fun v hv => ?_⟩
  obtain ⟨w, hw, e₁⟩ := h _ (hR' v hv)
  refine ⟨_, hR w hw, ?_⟩
  have e₂ := congrArg (fun z => R *ᵥ z) e₁
  simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hRR, Matrix.one_mulVec] at e₂
  have he' : (e : E) ≠ 0 := Nat.cast_ne_zero.2 he.ne'
  apply smul_right_injective (Fin n → E) he'
  simp only [Nat.cast_smul_eq_nsmul]
  rw [Matrix.mul_assoc]
  linear_combination (exp := 1) e₂

theorem splitOr_mul {F : Type} [Field F] [Algebra F E] {c : E ≃ₐ[F] E} {N : ℕ} {s t : 𝓞 E}
    (hs : SplitOr c N s) (ht : SplitOr c N t) : SplitOr c N (s * t) :=
  ⟨mul_ne_zero hs.1 ht.1, fun P hP h => (hP.mem_or_mem h).elim (hs.2 P hP) (ht.2 P hP)⟩

theorem smul_mul_mem {L : Submodule (𝓞 E) (Fin n → E)} {s t : 𝓞 E} {A B : Matrix (Fin n) (Fin n) E}
    (hA : ∀ v ∈ L, s • (A *ᵥ v) ∈ L) (hB : ∀ v ∈ L, t • (B *ᵥ v) ∈ L) (v : Fin n → E) (hv : v ∈ L) :
    (s * t) • ((A * B) *ᵥ v) ∈ L := by
  have := hA _ (hB v hv)
  rwa [Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mul_smul] at this

theorem exists_unitary_correction : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  intro F E _ _ _ _ _ c n G hG L hfg hL γ₀ N D hγ₀ hN hD
  obtain ⟨l, hl, hprod⟩ := GlobalTheory.T.unitaryMatrix_eq_prod_quasiReflections F E c n G hG _ hγ₀
  clear hγ₀
  induction l generalizing γ₀ D with
  | nil =>
    have h1 : γ₀ = 1 := Units.ext (by simpa using hprod)
    subst h1
    refine ⟨1, fun x y => by simp, ⟨1, by simp, fun v _ => ⟨0, L.zero_mem, by simp⟩⟩, 1,
      ⟨one_ne_zero, fun P hP h => absurd ((Ideal.eq_top_iff_one P).2 h) hP.ne_top⟩, fun v hv => ?_⟩
    simpa using hv
  | cons p l ih =>
    obtain ⟨x, u⟩ := p
    obtain ⟨hx, hu⟩ := hl (x, u) List.mem_cons_self
    simp only at hx hu
    obtain ⟨-, r1, rmul, run⟩ := GlobalTheory.T.unitaryQuasiReflection_laws F E c n G hG x hx
    have hu0 : u ≠ 0 := left_ne_zero_of_mul_eq_one hu
    let R : (a : E) → a ≠ 0 → GL (Fin n) E := fun a ha =>
      ⟨refl c G x a, refl c G x a⁻¹, by rw [rmul, mul_inv_cancel₀ ha, r1],
        by rw [rmul, inv_mul_cancel₀ ha, r1]⟩
    obtain ⟨d, hd, hRd⟩ := exists_nat_mulVec_mem L hfg hL (R u hu0).1
    obtain ⟨e, he, hRe⟩ := exists_nat_mulVec_mem L hfg hL ((R u hu0)⁻¹).1
    obtain ⟨γ₁, hγ₁, hc₁, s₁, hs₁, hL₁⟩ := ih ((R u hu0)⁻¹ * γ₀) (D * d * e)
      (Nat.mul_pos (Nat.mul_pos hD hd) he) (fun p hp => hl p (List.mem_cons_of_mem _ hp)) (by
        rw [Units.val_mul, hprod, List.map_cons, List.prod_cons, ← mul_assoc]
        change _ = _
        have : ((R u hu0)⁻¹).1 * refl c G x u = 1 := (R u hu0).inv_mul
        rw [this, one_mul])
    obtain ⟨u', hu', hc', s', hs', hL'⟩ := GlobalTheory.T.exists_norm_one_reflection_correction_at_level F E c n G hG L hfg hL x u N D hx hu hN hD
    have hu'0 : u' ≠ 0 := left_ne_zero_of_mul_eq_one hu'
    refine ⟨R u' hu'0 * γ₁, ?_, ?_, s' * s₁, splitOr_mul hs' hs₁, fun v hv => ⟨?_, ?_⟩⟩
    · intro y z
      rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
      exact (run u' hu' _ _).trans (hγ₁ y z)
    · have hconj := congAt_conj he (R u hu0).mul_inv hRd hRe hc₁
      have h := congAt_mul hc' hconj
      have e1 : refl c G x (u' / u) = (R u' hu'0 * (R u hu0)⁻¹).1 := by
        rw [div_eq_mul_inv, ← rmul]; rfl
      rw [e1, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul] at h
      convert h using 2
      group
    · rw [Units.val_mul]
      exact smul_mul_mem (fun v hv => (hL' v hv).1) (fun v hv => (hL₁ v hv).1) v hv
    · rw [mul_inv_rev, Units.val_mul, mul_comm s']
      exact smul_mul_mem (fun v hv => (hL₁ v hv).2) (fun v hv => (hL' v hv).2) v hv

end GlobalTheory.UnRep.Correct
end

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_correction_congruent_one_at_level : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (γ₀ : GL (Fin n) E) (N D : ℕ), IsUnE c G γ₀.1 → 0 < N → 0 < D → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAt L N D (γ * γ₀⁻¹).1 ∧ ∃ s : 𝓞 E, SplitOr c N s ∧ ∀ v ∈ L, s • (γ.1 *ᵥ v) ∈ L ∧ s • ((γ⁻¹).1 *ᵥ v) ∈ L := by
  atlas_forward_decl GlobalTheory.UnRep.Correct.exists_unitary_correction
end

section
noncomputable section

namespace GlobalTheory.UnRep.LatForm

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix nonZeroDivisors

theorem exists_dvd_coprime_mul_pow (N : ℕ) (m : ℕ) (hm : 0 < m) :
    ∃ j u : ℕ, u.Coprime N ∧ m ∣ u * N ^ j := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases h : Nat.gcd m N = 1
    · exact ⟨0, m, h, by simp⟩
    · obtain ⟨m', hm'⟩ := Nat.gcd_dvd_left m N
      have hg : 0 < Nat.gcd m N := Nat.gcd_pos_of_pos_left _ hm
      have hm'0 : 0 < m' := Nat.pos_of_ne_zero (by rintro rfl; simp at hm'; omega)
      have hlt : m' < m := by
        have : 2 ≤ Nat.gcd m N := by omega
        nlinarith
      obtain ⟨j, u, hu, hd⟩ := ih m' hlt hm'0
      refine ⟨j + 1, u, hu, ?_⟩
      rw [hm', pow_succ, ← mul_assoc, mul_comm (Nat.gcd m N)]
      exact Nat.mul_dvd_mul hd (Nat.gcd_dvd_right m N)

theorem inv_integral {V : Type} [AddCommGroup V] (Λ : AddSubgroup V) (k k' : V →+ V)
    (hk : ∀ z, k' (k z) = z) (N t m : ℕ) (ht : t.Coprime N) (hm : 0 < m)
    (h1 : ∀ z ∈ Λ, ∃ w ∈ Λ, t • (k z - z) = N • w) (h2 : ∀ z ∈ Λ, m • k' z ∈ Λ) :
    ∃ t' : ℕ, t'.Coprime N ∧ ∀ z ∈ Λ, t' • k' z ∈ Λ := by
  have key : ∀ j : ℕ, ∀ z ∈ Λ, ∃ y ∈ Λ, ∃ w ∈ Λ, t ^ j • k' z = y + N ^ j • k' w := by
    intro j
    induction j with
    | zero => intro z hz; exact ⟨0, Λ.zero_mem, z, hz, by simp⟩
    | succ j ih =>
      intro z hz
      obtain ⟨y, hy, w, hw, e⟩ := ih z hz
      obtain ⟨w', hw', e'⟩ := h1 w hw
      have e2 : t • k' w = t • w + N • k' (-w') := by
        have := congrArg k' e'
        rw [map_nsmul, map_nsmul, map_sub, hk, smul_sub] at this
        rw [map_neg, smul_neg, ← this]; abel
      refine ⟨t • y + N ^ j • t • w, Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (Λ.nsmul_mem hw _) _),
        -w', Λ.neg_mem hw', ?_⟩
      rw [pow_succ', mul_smul, e, smul_add, smul_comm t (N ^ j), e2, smul_add, pow_succ, mul_smul, add_assoc]
  obtain ⟨j, u, hu, q, hq⟩ := exists_dvd_coprime_mul_pow N m hm
  refine ⟨u * t ^ j, Nat.Coprime.mul_left hu (Nat.Coprime.pow_left _ ht), fun z hz => ?_⟩
  obtain ⟨y, hy, w, hw, e⟩ := key j z hz
  rw [mul_smul, e, smul_add, ← mul_smul, hq, mul_comm, mul_smul]
  exact Λ.add_mem (Λ.nsmul_mem hy _) (Λ.nsmul_mem (h2 w hw) _)

theorem exists_mem_primes {E : Type} [Field E] [NumberField E] (I : Ideal (𝓞 E)) (hI : I ≠ ⊥) :
    ∃ s ∈ I, s ≠ 0 ∧ ∀ P : Ideal (𝓞 E), P.IsPrime → s ∈ P → I ≤ P := by
  classical
  have hI0 : I ∈ (Ideal (𝓞 E))⁰ := mem_nonZeroDivisors_of_ne_zero hI
  set h := Fintype.card (ClassGroup (𝓞 E)) with hh
  have hpos : h ≠ 0 := Fintype.card_ne_zero
  have h1 : ClassGroup.mk0 ((⟨I, hI0⟩ : (Ideal (𝓞 E))⁰) ^ h) = 1 := by
    rw [map_pow, pow_card_eq_one]
  have h2 : (I ^ h).IsPrincipal := (ClassGroup.mk0_eq_one_iff (pow_mem hI0 h)).1 h1
  obtain ⟨s, hs⟩ := h2
  have hs' : I ^ h = Ideal.span {s} := hs
  refine ⟨s, Ideal.pow_le_self hpos (hs' ▸ Ideal.mem_span_singleton_self s), ?_, fun P hP hsP => ?_⟩
  · rintro rfl
    exact pow_ne_zero h hI (by rw [hs']; simp)
  · exact (Ideal.IsPrime.pow_le_iff hpos).1 (by rw [hs']; exact (Ideal.span_singleton_le_iff_mem _).2 hsP)

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem fm_mul (A B : Matrix (Fin n) (Fin n) E) : fm F (A * B) = fm F A * fm F B :=
  Matrix.map_mul (f := (Algebra.TensorProduct.includeRight :
    E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E).toRingHom)

theorem fm_one : fm F (1 : Matrix (Fin n) (Fin n) E) = 1 :=
  Matrix.map_one _ (by simp) rfl

theorem fm_mulVec_pure (M : Matrix (Fin n) (Fin n) E) (a : FiniteAdeleRing (𝓞 F) F) (x : Fin n → E) :
    fm F M *ᵥ (fun i => a ⊗ₜ[F] x i) = fun i => a ⊗ₜ[F] (M *ᵥ x) i := by
  funext i
  simp [fm, Matrix.mulVec, dotProduct, TensorProduct.tmul_sum]

theorem congAtA_of_congAt (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (δ : Matrix (Fin n) (Fin n) E)
    (h : CongAt L N D δ) : CongAtA F L N D (fm F δ) := by
  obtain ⟨t, ht, h⟩ := h
  refine ⟨t, ht, fun z hz => ?_⟩
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    obtain ⟨w, hw, e⟩ := h x hx
    refine ⟨fun i => a ⊗ₜ[F] w i, AddSubgroup.subset_closure ⟨a, ha, w, hw, rfl⟩, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    have := congrArg (fun y : Fin n → E =>
      (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E a) (y i)) e
    simpa only [Pi.smul_apply, Pi.sub_apply, map_nsmul, map_sub, TensorProduct.mk_apply] using this
  | zero => exact ⟨0, AddSubgroup.zero_mem _, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨w, hw, e⟩ := ihx
    obtain ⟨w', hw', e'⟩ := ihy
    refine ⟨w + w', AddSubgroup.add_mem _ hw hw', ?_⟩
    rw [smul_add, ← e, ← e', Matrix.mulVec_add, ← smul_add]; congr 1; abel
  | neg x _ ih =>
    obtain ⟨w, hw, e⟩ := ih
    refine ⟨-w, AddSubgroup.neg_mem _ hw, ?_⟩
    rw [smul_neg, ← e, Matrix.mulVec_neg, ← smul_neg]; congr 1; abel

theorem smul_fm_mem (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) (M : Matrix (Fin n) (Fin n) E)
    (h : ∀ v ∈ L, s • (M *ᵥ v) ∈ L) : ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (fm F M *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a, ha, _, h x hx, ?_⟩
    rw [fm_mulVec_pure]
    funext i
    simp [Algebra.smul_def]
  | zero => simp
  | add x y _ _ ihx ihy => rw [Matrix.mulVec_add, smul_add]; exact AddSubgroup.add_mem _ ihx ihy
  | neg x _ ih => rw [Matrix.mulVec_neg, smul_neg]; exact AddSubgroup.neg_mem _ ih

theorem smul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (s : 𝓞 E) :
    ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z ∈ hat F (L : Set (Fin n → E)) := by
  intro z hz
  have := smul_fm_mem (F := F) L s 1 (fun v hv => by simpa using L.smul_mem s hv) z hz
  rwa [fm_one, Matrix.one_mulVec] at this

theorem congAtA_mul (L : Submodule (𝓞 E) (Fin n → E)) (N D : ℕ) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : CongAtA F L N D a) (hb : CongAtA F L N D b) : CongAtA F L N D (a * b) := by
  obtain ⟨t, ht, ha⟩ := ha
  obtain ⟨u, hu, hb⟩ := hb
  refine ⟨t * u, Nat.Coprime.mul_left ht hu, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := hb z hz
  obtain ⟨w', hw', e'⟩ := ha (u • z + D • w)
    (AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _))
  refine ⟨w' + t • w, AddSubgroup.add_mem _ hw' (AddSubgroup.nsmul_mem _ hw _), ?_⟩
  have e1 : u • z + D • w = u • (b *ᵥ z) := by rw [← e, smul_sub]; abel
  rw [e1, Matrix.mulVec_smul, Matrix.mulVec_mulVec] at e'
  rw [smul_add, ← e', smul_comm D t, ← e, ← smul_add, mul_smul]
  congr 1
  rw [smul_sub, smul_sub]; abel

def denIdeal (L : Submodule (𝓞 E) (Fin n → E)) (M : Matrix (Fin n) (Fin n) (RA F E)) : Ideal (𝓞 E) where
  carrier := {s | ∀ z ∈ hat F (L : Set (Fin n → E)),
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (M *ᵥ z) ∈ hat F (L : Set (Fin n → E))}
  add_mem' := by
    intro a b ha hb z hz
    have := AddSubgroup.add_mem _ (ha z hz) (hb z hz)
    rw [← add_smul, ← TensorProduct.tmul_add] at this
    exact this
  zero_mem' := by intro z hz; simp
  smul_mem' := by
    intro a b hb z hz
    have := smul_mem_hat L a _ (hb z hz)
    rw [← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul] at this
    exact this

theorem one_tmul_natCast_smul (m : ℕ) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) • z = m • z := by
  have : ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((m : 𝓞 E)) : E)) = (m : RA F E) := by
    have h : (((m : 𝓞 E)) : E) = (m : E) := by simp
    rw [h]
    exact map_natCast (Algebra.TensorProduct.includeRight :
      E →ₐ[F] FiniteAdeleRing (𝓞 F) F ⊗[F] E) m
  rw [this, Nat.cast_smul_eq_nsmul]

theorem one_tmul_natCast_mul_smul (m : ℕ) (s : 𝓞 E) (z : Fin n → RA F E) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] ((((m : 𝓞 E) * s : 𝓞 E)) : E)) • z =
      m • ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • z := by
  rw [← one_tmul_natCast_smul, ← mul_smul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  rfl

theorem exists_rep_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ c n G hG h2 L hL hL' g N hg hN
  obtain ⟨-, hden, -⟩ := GlobalTheory.T.idempotent_adeles_and_small_adelic_matrices F E n L hL hL'
  obtain ⟨d₁, hd₁, H₁⟩ := hden g.1
  obtain ⟨d₂, hd₂, H₂⟩ := hden (g⁻¹).1
  have hN' : 0 < N * (d₁ * d₂) := by positivity
  obtain ⟨γ₀, hγ₀, hc₀⟩ := GlobalTheory.T.unitaryGroup_weak_approximation_at_primes F E c n G hG h2 L hL hL' g _ _ hg hN' hN'
  obtain ⟨γ, hγ, hc₁, s₁, hs₁, hs⟩ := GlobalTheory.T.exists_unitary_correction_congruent_one_at_level F E c n G hG L hL hL' γ₀ _ _ hγ₀ hN' hN'
  have hc := congAtA_mul L _ _ _ _ (congAtA_of_congAt (F := F) L _ _ _ hc₁) hc₀
  have hγγ : fm F (γ * γ₀⁻¹).1 * (fm F γ₀.1 * g.1) = fm F γ.1 * g.1 := by
    rw [← mul_assoc, ← fm_mul, ← Units.val_mul, inv_mul_cancel_right]
  rw [hγγ] at hc
  obtain ⟨t, ht, hc⟩ := hc
  set k := fm F γ.1 * g.1 with hk
  set k' := (g⁻¹).1 * fm F (γ⁻¹).1 with hk'
  have hkk : k' * k = 1 := by
    rw [hk, hk', mul_assoc, ← mul_assoc (fm F _), ← fm_mul, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, fm_one, one_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  obtain ⟨m, hm, Hm⟩ := hden k'
  obtain ⟨t', ht', H'⟩ := inv_integral (hat F (L : Set (Fin n → E))) (Matrix.mulVecLin k).toAddMonoidHom
    (Matrix.mulVecLin k').toAddMonoidHom
    (fun z => by
      change k' *ᵥ (k *ᵥ z) = z
      rw [Matrix.mulVec_mulVec, hkk, Matrix.one_mulVec]) _ t m ht hm hc Hm
  refine ⟨γ, hγ, ⟨t, Nat.Coprime.coprime_mul_right_right ht, fun z hz => ?_⟩, ?_⟩
  · obtain ⟨w, hw, e⟩ := hc z hz
    exact ⟨(d₁ * d₂) • w, AddSubgroup.nsmul_mem _ hw _, by rw [e, mul_smul]⟩
  have a1 : ((t * t' : ℕ) : 𝓞 E) ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      obtain ⟨w, hw, e⟩ := hc z hz
      rw [one_tmul_natCast_smul, mul_comm, mul_smul]
      refine AddSubgroup.nsmul_mem _ ?_ _
      have : t • (k *ᵥ z) = t • z + (N * (d₁ * d₂)) • w := by rw [← e, smul_sub]; abel
      rw [this]
      exact AddSubgroup.add_mem _ (AddSubgroup.nsmul_mem _ hz _) (AddSubgroup.nsmul_mem _ hw _)
    · intro z hz
      rw [one_tmul_natCast_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ (H' z hz) _
  have a2 : ((d₁ * d₂ : ℕ) : 𝓞 E) * s₁ ∈ denIdeal L k ⊓ denIdeal L k' := by
    constructor
    · intro z hz
      have := smul_fm_mem (F := F) L s₁ γ.1 (fun v hv => (hs v hv).1) _ (H₁ z hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_comm] at this
      rw [one_tmul_natCast_mul_smul, mul_comm, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
    · intro z hz
      have := H₂ _ (smul_fm_mem (F := F) L s₁ (γ⁻¹).1 (fun v hv => (hs v hv).2) _ hz)
      rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec] at this
      rw [one_tmul_natCast_mul_smul, mul_smul]
      exact AddSubgroup.nsmul_mem _ this _
  have hne : denIdeal L k ⊓ denIdeal L k' ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at a2
    exact mul_ne_zero (Nat.cast_ne_zero.2 (by positivity)) hs₁.1 a2
  obtain ⟨s, hsI, hs0, hsP⟩ := exists_mem_primes _ hne
  refine ⟨s, ⟨hs0, fun P hP h => ?_⟩, fun z hz => ⟨hsI.1 z hz, hsI.2 z hz⟩⟩
  have b1 := hsP P hP h a1
  have b2 := hsP P hP h a2
  have hcop : IsCoprime ((t * t' : ℕ) : 𝓞 E) ((N * (d₁ * d₂) : ℕ) : 𝓞 E) :=
    Nat.Coprime.cast (Nat.Coprime.mul_left ht ht')
  have hnot : ((N * (d₁ * d₂) : ℕ) : 𝓞 E) ∉ P := by
    intro hh
    obtain ⟨x, y, e⟩ := hcop
    exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (e ▸ P.add_mem (P.mul_mem_left x b1) (P.mul_mem_left y hh)))
  refine ⟨?_, fun hh => hnot (by rw [Nat.cast_mul]; exact P.mul_mem_right _ hh)⟩
  rcases hP.mem_or_mem b2 with h1 | h1
  · exact (hnot (by rw [Nat.cast_mul]; exact P.mul_mem_left _ h1)).elim
  · exact (hs₁.2 P hP h1).resolve_right hnot

end GlobalTheory.UnRep.LatForm
end
end

section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_unitary_split_denominator : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G → Module.finrank F E = 2 → ∀ L : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (g : GL (Fin n) (RA F E)) (N : ℕ), IsUnA c G g.1 → 0 < N → ∃ γ : GL (Fin n) E, IsUnE c G γ.1 ∧ CongAtA F L N N (fm F γ.1 * g.1) ∧ ∃ s : 𝓞 E, SplitOff c N s ∧ ∀ z ∈ hat F (L : Set (Fin n → E)), ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • ((fm F γ.1 * g.1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) ∧ ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (s : E)) • (((g⁻¹).1 * fm F (γ⁻¹).1) *ᵥ z) ∈ hat F (L : Set (Fin n → E)) := by
  first | exact @GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | exact GlobalTheory.UnRep.LatForm.exists_rep_split_denominator | (intros; apply GlobalTheory.UnRep.LatForm.exists_rep_split_denominator <;> assumption)
end
