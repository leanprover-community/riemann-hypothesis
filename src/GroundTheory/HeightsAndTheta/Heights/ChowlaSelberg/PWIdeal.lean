import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ChowlaSelberg.Statements
import GroundTheory.GlobalFields.AnalyticClassNumber.QuadraticLegendre

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField

noncomputable section

theorem isIntegral_of_map {F F' : Type*} [Field F] [Field F'] (j : F →+* F') {x : F}
    (h : IsIntegral ℤ (j x)) : IsIntegral ℤ x :=
  (isIntegral_algHom_iff j.toIntAlgHom j.injective).1 h

theorem le_of_map_le {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) ≤ B.map (RingOfIntegers.mapRingHom j)) : A ≤ B := by
  obtain ⟨b, hbB, hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hB
  obtain ⟨B', hB'⟩ : B ∣ Ideal.span {b} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hbB)
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    rw [mul_zero, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot] at hB'
    exact hb0 hB'
  have key : A * B' ≤ B * B' := by
    rw [← hB', Ideal.mul_le]
    intro x hx y hy
    have hm : RingOfIntegers.mapRingHom j (x * y) ∈
        (Ideal.span {b}).map (RingOfIntegers.mapRingHom j) := by
      rw [hB', Ideal.map_mul, map_mul]
      exact Ideal.mul_mem_mul (h (Ideal.mem_map_of_mem _ hx)) (Ideal.mem_map_of_mem _ hy)
    rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton'] at hm
    obtain ⟨z, hz⟩ := hm
    have hbF : (b : F) ≠ 0 := by
      intro h0
      exact hb0 (RingOfIntegers.ext (by simpa using h0))
    have hz' : (z : F') * j (b : F) = j ((x * y : 𝓞 F) : F) := by
      have := congrArg (fun t : 𝓞 F' ↦ (t : F')) hz
      simpa using this
    have himg : j (((x * y : 𝓞 F) : F) / (b : F)) = (z : F') := by
      rw [map_div₀, ← hz', mul_div_assoc, div_self ((map_ne_zero j).2 hbF), mul_one]
    have hq : IsIntegral ℤ (((x * y : 𝓞 F) : F) / (b : F)) := by
      apply isIntegral_of_map j
      rw [himg]
      exact RingOfIntegers.isIntegral_coe z
    rw [Ideal.mem_span_singleton']
    refine ⟨⟨_, hq⟩, RingOfIntegers.ext ?_⟩
    show ((x * y : 𝓞 F) : F) / (b : F) * (b : F) = ((x * y : 𝓞 F) : F)
    rw [div_mul_cancel₀ _ hbF]
  have hdvd : B * B' ∣ A * B' := Ideal.dvd_iff_le.2 key
  exact Ideal.dvd_iff_le.1 ((mul_dvd_mul_iff_right hB'0).1 hdvd)

theorem eq_of_map_eq {F F' : Type*} [Field F] [NumberField F] [Field F'] [NumberField F']
    (j : F →+* F') {A B : Ideal (𝓞 F)} (hB : B ≠ ⊥)
    (h : A.map (RingOfIntegers.mapRingHom j) = B.map (RingOfIntegers.mapRingHom j)) : A = B := by
  have hA : A ≠ ⊥ := by
    rintro rfl
    rw [Ideal.map_bot, eq_comm, Ideal.map_eq_bot_iff_of_injective] at h
    · exact hB h
    · intro x y hxy
      exact RingOfIntegers.ext (j.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) hxy))
  exact le_antisymm (le_of_map_le j hB h.le) (le_of_map_le j hA h.ge)

theorem exists_extension_mem_range {F : Type} [Field F] [NumberField F] (τ : F →+* ℂ) {z₁ z₂ : ℂ}
    (h₁ : IsAlgebraic ℚ z₁) (h₂ : IsAlgebraic ℚ z₂) :
    ∃ (F' : Type) (_ : Field F') (_ : NumberField F') (j : F →+* F') (τ' : F' →+* ℂ),
      τ'.comp j = τ ∧ z₁ ∈ Set.range τ' ∧ z₂ ∈ Set.range τ' := by
  let e := AlgEquiv.ofInjectiveField τ.toRatAlgHom
  let E₁ : IntermediateField ℚ ℂ := τ.toRatAlgHom.fieldRange
  let E₂ : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {z₁, z₂}
  have : FiniteDimensional ℚ E₁ := LinearEquiv.finiteDimensional e.toLinearEquiv
  have : FiniteDimensional ℚ E₂ :=
    IntermediateField.finiteDimensional_adjoin_pair h₁.isIntegral h₂.isIntegral
  have : FiniteDimensional ℚ ↥(E₁ ⊔ E₂) := IntermediateField.finiteDimensional_sup E₁ E₂
  have : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite ℚ _
  refine ⟨↥(E₁ ⊔ E₂), inferInstance, inferInstance,
    ((IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).toRingHom.comp e.toRingEquiv.toRingHom),
    (E₁ ⊔ E₂).val.toRingHom, ?_, ?_, ?_⟩
  · ext x
    rfl
  · exact ⟨⟨z₁, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩
  · exact ⟨⟨z₂, (le_sup_right : E₂ ≤ E₁ ⊔ E₂)
      (IntermediateField.subset_adjoin ℚ _ (by simp))⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global.Quadratic

variable {K : Type} [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem absNorm_span_natCast_quadratic (n : ℕ) :
    Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) = n ^ 2 := by
  rw [Ideal.absNorm_span_natCast, RingOfIntegers.rank, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem ramified_eq_span_sqrtDiscr {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (hN : (Ideal.absNorm 𝔭).Prime)
    (h2 : 𝔭 ^ 2 = Ideal.span {((Ideal.absNorm 𝔭 : ℕ) : 𝓞 K)}) :
    𝔭 = Ideal.span {sqrtDiscr K} := by
  set p := Ideal.absNorm 𝔭 with hp
  have h𝔭top : 𝔭 ≠ ⊤ := h𝔭.ne_top
  have hconj : ∀ x ∈ 𝔭, conjRing K x ∈ 𝔭 := by
    intro x hx
    have hx2 : x ^ 2 ∈ Ideal.span {(p : 𝓞 K)} := by
      rw [← h2]
      exact Ideal.pow_mem_pow hx 2
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hx2
    have hp𝔭 : (p : 𝓞 K) ∈ 𝔭 := by
      have : (p : 𝓞 K) ∈ 𝔭 ^ 2 := by
        rw [h2]
        exact Ideal.mem_span_singleton_self _
      exact Ideal.pow_le_self two_ne_zero this
    have hsq : (conjRing K x) ^ 2 ∈ 𝔭 := by
      have e : (conjRing K x) ^ 2 = conjRing K y * (p : 𝓞 K) := by
        rw [← map_pow, ← hy, map_mul, map_natCast]
      rw [e]
      exact Ideal.mul_mem_left _ _ hp𝔭
    exact h𝔭.mem_of_pow_mem 2 hsq
  have hres : ∀ x : 𝓞 K, ∃ n : ℤ, x - n ∈ 𝔭 := by
    intro x
    have hcard : Nat.card (𝓞 K ⧸ 𝔭) = p := by
      rw [hp, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    have : Fact (Nat.card (𝓞 K ⧸ 𝔭)).Prime := ⟨hcard ▸ hN⟩
    have h1 : (1 : 𝓞 K ⧸ 𝔭) ≠ 0 := by
      rw [ne_eq, ← map_one (Ideal.Quotient.mk 𝔭), Ideal.Quotient.eq_zero_iff_mem]
      exact fun h ↦ h𝔭top ((Ideal.eq_top_iff_one _).2 h)
    have htop : AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) = ⊤ := by
      rcases AddSubgroup.eq_bot_or_eq_top_of_prime_card
          (AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭)) with h | h
      · exfalso
        apply h1
        have : (1 : 𝓞 K ⧸ 𝔭) ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) :=
          AddSubgroup.mem_zmultiples 1
        rw [h] at this
        exact (AddSubgroup.mem_bot).1 this
      · exact h
    have hx : Ideal.Quotient.mk 𝔭 x ∈ AddSubgroup.zmultiples (1 : 𝓞 K ⧸ 𝔭) := by
      rw [htop]
      trivial
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 hx
    refine ⟨n, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← hn, map_intCast, zsmul_one, sub_self]
  have hsub : ∀ x : 𝓞 K, conjRing K x - x ∈ 𝔭 := by
    intro x
    obtain ⟨n, hn⟩ := hres x
    have hc := hconj _ hn
    rw [map_sub, map_intCast] at hc
    have := 𝔭.sub_mem hc hn
    rwa [sub_sub_sub_cancel_right] at this
  have hδ : sqrtDiscr K ∈ 𝔭 := by
    have e : sqrtDiscr K = intBasis K 0 * (conjRing K (intBasis K 1) - intBasis K 1) -
        intBasis K 1 * (conjRing K (intBasis K 0) - intBasis K 0) := by
      rw [sqrtDiscr]
      ring
    rw [e]
    exact 𝔭.sub_mem (𝔭.mul_mem_left _ (hsub _)) (𝔭.mul_mem_left _ (hsub _))
  have hnormsq : Ideal.absNorm (Ideal.span {sqrtDiscr K}) ^ 2 = d ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, sqrtDiscr_sq', hdisc, Int.cast_neg, Int.cast_natCast,
      Ideal.span_singleton_neg, absNorm_span_natCast_quadratic]
  have hnorm : Ideal.absNorm (Ideal.span {sqrtDiscr K}) = d :=
    Nat.pow_left_injective two_ne_zero hnormsq
  have hmax : (Ideal.span {sqrtDiscr K}).IsMaximal :=
    (Ideal.isPrime_of_irreducible_absNorm (hnorm ▸ hd)).isMaximal
      (by rw [ne_eq, Ideal.span_singleton_eq_bot]; exact sqrtDiscr_ne_zero K)
  exact (hmax.eq_of_le h𝔭top ((Ideal.span_singleton_le_iff_mem _).2 hδ)).symm

theorem prime_cases {d : ℕ} (hd : d.Prime) (hdisc : discr K = -(d : ℤ))
    (𝔭 : Ideal (𝓞 K)) [h𝔭 : 𝔭.IsPrime] (h0 : 𝔭 ≠ ⊥) :
    (∃ a : 𝓞 K, 𝔭 = Ideal.span {a}) ∨
      ∃ p : ℕ, p.Prime ∧ Ideal.absNorm 𝔭 = p ∧ ∃ 𝔮 : Ideal (𝓞 K), 𝔮.IsPrime ∧
        Ideal.absNorm 𝔮 = p ∧ 𝔭 * 𝔮 = Ideal.span {(p : 𝓞 K)} ∧ 𝔮 ≠ 𝔭 := by
  have : 𝔭.IsMaximal := h𝔭.isMaximal h0
  obtain ⟨p, k, hk, hpmem, hpp, hNk⟩ := Ideal.exists_prime_and_absNorm_eq_pow 𝔭
  have hle : Ideal.span {(p : 𝓞 K)} ≤ 𝔭 := (Ideal.span_singleton_le_iff_mem _).2 hpmem
  have hdvdN : p ^ k ∣ p ^ 2 := by
    rw [← hNk, ← absNorm_span_natCast_quadratic (K := K)]
    exact Ideal.absNorm_dvd_absNorm_of_le hle
  have hk2 : k ≤ 2 := (Nat.pow_dvd_pow_iff_le_right hpp.one_lt).1 hdvdN
  obtain ⟨𝔮, h𝔮⟩ : 𝔭 ∣ Ideal.span {(p : 𝓞 K)} := Ideal.dvd_iff_le.2 hle
  have hN𝔮 : Ideal.absNorm 𝔭 * Ideal.absNorm 𝔮 = p ^ 2 := by
    rw [← map_mul, ← h𝔮, absNorm_span_natCast_quadratic]
  have hp0 : 0 < p := hpp.pos
  interval_cases k
  · rw [hNk, pow_one, sq] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = p := Nat.eq_of_mul_eq_mul_left hp0 hN𝔮
    have h𝔮p : 𝔮.IsPrime := Ideal.isPrime_of_irreducible_absNorm (hq ▸ hpp)
    by_cases he : 𝔮 = 𝔭
    · left
      refine ⟨sqrtDiscr K, ramified_eq_span_sqrtDiscr hd hdisc 𝔭 (by rw [hNk, pow_one]; exact hpp) ?_⟩
      rw [hNk, pow_one, sq, h𝔮, he]
    · right
      exact ⟨p, hpp, by rw [hNk, pow_one], 𝔮, h𝔮p, hq, h𝔮.symm, he⟩
  · rw [hNk] at hN𝔮
    have hq : Ideal.absNorm 𝔮 = 1 := by
      have h' : p ^ 2 * Ideal.absNorm 𝔮 = p ^ 2 * 1 := by rw [mul_one]; exact hN𝔮
      exact Nat.eq_of_mul_eq_mul_left (pow_pos hp0 2) h'
    rw [Ideal.absNorm_eq_one_iff] at hq
    left
    exact ⟨p, by rw [h𝔮, hq, Ideal.mul_top]⟩

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

theorem eisensteinSum_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) (n : ℕ) :
    eisensteinSum (scaleLattice c Λ) n = (c ^ n)⁻¹ * eisensteinSum Λ n := by
  let e : Λ ≃ₗ[ℤ] scaleLattice c Λ :=
    Submodule.equivMapOfInjective (LinearMap.mulLeft ℤ c) (mul_right_injective₀ hc) Λ
  rw [eisensteinSum, eisensteinSum, ← e.toEquiv.tsum_eq, ← tsum_mul_left]
  refine tsum_congr fun l ↦ ?_
  show ((c * (l : ℂ)) ^ n)⁻¹ = (c ^ n)⁻¹ * ((l : ℂ) ^ n)⁻¹
  rw [mul_pow, mul_inv]

theorem latticeDiscr_scale_of_ne_zero (Λ : Submodule ℤ ℂ) {c : ℂ} (hc : c ≠ 0) :
    latticeDiscr (scaleLattice c Λ) = (c ^ 12)⁻¹ * latticeDiscr Λ := by
  simp only [latticeDiscr, latticeG₂, latticeG₃, eisensteinSum_scale_of_ne_zero Λ hc]
  field_simp

variable {K : Type} [Field K] [NumberField K]

theorem idealLattice_spanSingleton_mul (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (x : K) :
    idealLattice σ (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) * L.lattice =
      scaleLattice (σ x) L.lattice := by
  apply le_antisymm
  · rw [Submodule.mul_le]
    intro m hm l hl
    obtain ⟨y, hy, rfl⟩ := (mem_idealLattice σ).1 hm
    obtain ⟨b, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hy
    have hb : σ (algebraMap (𝓞 K) K b) ∈ latticeEnd L := by
      rw [hL]
      exact (mem_cmRing σ).2 ⟨b, rfl⟩
    refine Submodule.mem_map.2 ⟨σ (algebraMap (𝓞 K) K b) * l, hb l hl, ?_⟩
    simp only [LinearMap.mulLeft_apply, Algebra.smul_def, map_mul]
    ring
  · rw [scaleLattice, Submodule.map_le_iff_le_comap]
    intro l hl
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    exact Submodule.mul_mem_mul
      (map_mem_idealLattice σ (FractionalIdeal.mem_spanSingleton_self _ x)) hl

def spanNZ (a : 𝓞 K) (ha : a ≠ 0) : (Ideal (𝓞 K))⁰ :=
  ⟨Ideal.span {a}, mem_nonZeroDivisors_of_ne_zero (by rwa [ne_eq, Ideal.zero_eq_bot,
    Ideal.span_singleton_eq_bot])⟩

theorem discrRatio_span_singleton (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (a : 𝓞 K) (ha : a ≠ 0) :
    discrRatio σ L.lattice (FractionalIdeal.mk0 K (spanNZ a ha)) = σ (algebraMap (𝓞 K) K a) ^ 12 := by
  have haK : algebraMap (𝓞 K) K a ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 ha
  have hσ : σ (algebraMap (𝓞 K) K a) ≠ 0 := (map_ne_zero σ).2 haK
  rw [discrRatio, Units.val_inv_eq_inv_val, FractionalIdeal.coe_mk0, spanNZ,
    FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv,
    idealLattice_spanSingleton_mul σ L hL, latticeDiscr_scale_of_ne_zero _ ((map_ne_zero σ).2 (inv_ne_zero haK)),
    map_inv₀, inv_pow, inv_inv, latticeDiscr_lattice, mul_div_assoc, div_self (discr_ne_zero L), mul_one]

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.ChowlaSelberg

open NumberField GroundTheory.Global GroundTheory.Global.Elliptic
open scoped nonZeroDivisors

noncomputable section

variable {K : Type} [Field K] [NumberField K]

def WIdealAt (σ : K →+* ℂ) (L : PeriodPair) (𝔞 : (Ideal (𝓞 K))⁰) : Prop :=
  IsAlgebraic ℚ (discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞)) ∧
    ∀ (F : Type) [Field F] [NumberField F] (ι : K →+* F) (τ : F →+* ℂ), τ.comp ι = σ →
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∈ Set.range τ →
        ∃ w : 𝓞 F, τ (w : F) = discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) ∧
          Ideal.span {w} = Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ^ 12

theorem mapRingHom_injective {F F' : Type*} [Field F] [Field F'] (ι : F →+* F') :
    Function.Injective (RingOfIntegers.mapRingHom ι) := fun x y h ↦
  RingOfIntegers.ext (ι.injective (by simpa using congrArg (fun t : 𝓞 F' ↦ (t : F')) h))

omit [NumberField K] in
theorem map_ne_bot {F : Type} [Field F] [NumberField F] (ι : K →+* F) (𝔞 : (Ideal (𝓞 K))⁰) (n : ℕ) :
    Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ^ n ≠ ⊥ := by
  have h0 : Ideal.map (RingOfIntegers.mapRingHom ι) (𝔞 : Ideal (𝓞 K)) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective (mapRingHom_injective ι)]
    exact nonZeroDivisors.coe_ne_zero 𝔞
  rw [← Ideal.zero_eq_bot] at h0 ⊢
  exact pow_ne_zero n h0

theorem wIdealAt_span (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (a : 𝓞 K)
    (ha : a ≠ 0) : WIdealAt σ L (spanNZ a ha) := by
  rw [WIdealAt, discrRatio_span_singleton σ L hL a ha]
  refine ⟨?_, fun F _ _ ι τ hτ _ ↦ ?_⟩
  · have hi : IsIntegral ℤ (σ (algebraMap (𝓞 K) K a)) :=
      (RingOfIntegers.isIntegral_coe a).map σ.toIntAlgHom
    exact (hi.pow 12).tower_top.isAlgebraic
  · refine ⟨RingOfIntegers.mapRingHom ι a ^ 12, ?_, ?_⟩
    · rw [← hτ]
      simp
    · rw [← Ideal.span_singleton_pow]
      congr 1
      show Ideal.span {RingOfIntegers.mapRingHom ι a} =
        Ideal.map (RingOfIntegers.mapRingHom ι) (Ideal.span {a})
      rw [Ideal.map_span, Set.image_singleton]

theorem wIdealAt_mul [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    (hC : WCocycle.Statement S) (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ)
    (𝔞 𝔭 : (Ideal (𝓞 K))⁰) (L' : PeriodPair)
    (hL' : L'.lattice = idealLattice σ ↑(FractionalIdeal.mk0 K 𝔞)⁻¹ * L.lattice)
    (h₁ : WIdealAt σ L 𝔞) (h₂ : WIdealAt σ L' 𝔭) : WIdealAt σ L (𝔞 * 𝔭) := by
  have hw : discrRatio σ L.lattice (FractionalIdeal.mk0 K (𝔞 * 𝔭)) =
      discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔞) *
        discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔭) := by
    rw [map_mul, hC σ L hL, hL']
  obtain ⟨a₁, i₁⟩ := h₁
  obtain ⟨a₂, i₂⟩ := h₂
  refine ⟨hw ▸ a₁.mul a₂, fun F _ _ ι τ hτ hmem ↦ ?_⟩
  obtain ⟨F', _, _, j, τ', hτ', ⟨v₁, hv₁⟩, ⟨v₂, hv₂⟩⟩ := exists_extension_mem_range τ a₁ a₂
  have hτ'σ : τ'.comp (j.comp ι) = σ := by rw [← RingHom.comp_assoc, hτ', hτ]
  obtain ⟨u₁, hu₁, s₁⟩ := i₁ F' (j.comp ι) τ' hτ'σ ⟨v₁, hv₁⟩
  obtain ⟨u₂, hu₂, s₂⟩ := i₂ F' (j.comp ι) τ' hτ'σ ⟨v₂, hv₂⟩
  obtain ⟨v, hv⟩ := hmem
  have hjv : j v = ((u₁ * u₂ : 𝓞 F') : F') := by
    apply τ'.injective
    rw [← RingHom.comp_apply, hτ', hv, hw, ← hu₁, ← hu₂]
    simp
  have hvint : IsIntegral ℤ v :=
    isIntegral_of_map j (by rw [hjv]; exact RingOfIntegers.isIntegral_coe _)
  obtain ⟨v', hv'⟩ : ∃ v' : 𝓞 F, (v' : F) = v := ⟨⟨v, (mem_integralClosure_iff ℤ F).2 hvint⟩, rfl⟩
  refine ⟨v', by rw [hv']; exact hv, ?_⟩
  apply eq_of_map_eq j (map_ne_bot ι (𝔞 * 𝔭) 12)
  have hcomp : RingOfIntegers.mapRingHom (j.comp ι) =
      (RingOfIntegers.mapRingHom j).comp (RingOfIntegers.mapRingHom ι) := by
    ext x
    rfl
  have hj : RingOfIntegers.mapRingHom j v' = u₁ * u₂ :=
    RingOfIntegers.ext (by rw [RingOfIntegers.mapRingHom_apply, hv', hjv])
  rw [Ideal.map_span, Set.image_singleton, Ideal.map_pow, Ideal.map_map, ← hcomp, hj,
    ← Ideal.span_singleton_mul_span_singleton, s₁, s₂, ← mul_pow, ← Ideal.map_mul]
  rfl

theorem wIdealAt_split [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    [IsTotallyComplex K] (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S)
    (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (p : ℕ) (hp : p.Prime)
    (𝔭 𝔮 : (Ideal (𝓞 K))⁰) (h𝔭 : (𝔭 : Ideal (𝓞 K)).IsPrime) (h𝔮 : (𝔮 : Ideal (𝓞 K)).IsPrime)
    (hN𝔭 : Ideal.absNorm (𝔭 : Ideal (𝓞 K)) = p) (hN𝔮 : Ideal.absNorm (𝔮 : Ideal (𝓞 K)) = p)
    (hpq : (𝔭 : Ideal (𝓞 K)) * 𝔮 = Ideal.span {(p : 𝓞 K)})
    (hne : (𝔮 : Ideal (𝓞 K)) ≠ 𝔭) : WIdealAt σ L 𝔭 := by
  obtain ⟨L', hL'lat, hL'⟩ :=
    exists_lattice_mul σ (Algebra.IsQuadraticExtension.finrank_eq_two ℚ K) L hL (FractionalIdeal.mk0 K 𝔭)
  have hp0 : (p : 𝓞 K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have hprod : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) *
      discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔮) = (p : ℂ) ^ 12 := by
    have e : 𝔭 * 𝔮 = spanNZ (p : 𝓞 K) hp0 := Subtype.ext hpq
    have h := hC σ L hL (FractionalIdeal.mk0 K 𝔭) (FractionalIdeal.mk0 K 𝔮)
    rw [← map_mul, e, discrRatio_span_singleton σ L hL, ← hL'lat] at h
    rw [← h]
    simp
  have U₁ := hU σ L hL 𝔭 h𝔭 (hN𝔭 ▸ hp)
  have U₂ := hU σ L' hL' 𝔮 h𝔮 (hN𝔮 ▸ hp)
  have hw₁ : discrRatio σ L.lattice (FractionalIdeal.mk0 K 𝔭) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hprod
    exact pow_ne_zero 12 (Nat.cast_ne_zero.2 hp.ne_zero) hprod.symm
  refine ⟨U₁.1, fun F _ _ ι τ hτ hmem ↦ ?_⟩
  have hmem₂ : discrRatio σ L'.lattice (FractionalIdeal.mk0 K 𝔮) ∈ Set.range τ := by
    obtain ⟨v, hv⟩ := hmem
    refine ⟨(p : F) ^ 12 / v, ?_⟩
    rw [map_div₀, map_pow, map_natCast, hv, ← hprod]
    field_simp
  obtain ⟨u₁, hu₁, hQ₁⟩ := U₁.2 F ι τ hτ hmem
  obtain ⟨u₂, hu₂, hQ₂⟩ := U₂.2 F ι τ hτ hmem₂
  refine ⟨u₁, hu₁, ?_⟩
  set f := RingOfIntegers.mapRingHom ι
  set P := Ideal.map f (𝔭 : Ideal (𝓞 K))
  set Q := Ideal.map f (𝔮 : Ideal (𝓞 K))
  have hu : u₁ * u₂ = (p : 𝓞 F) ^ 12 := by
    apply RingOfIntegers.ext
    apply τ.injective
    simp [hu₁, hu₂, hprod]
  have hAB : Ideal.span {u₁} * Ideal.span {u₂} = P ^ 12 * Q ^ 12 := by
    rw [Ideal.span_singleton_mul_span_singleton, hu, ← Ideal.span_singleton_pow, ← mul_pow,
      ← Ideal.map_mul, hpq, Ideal.map_span, Set.image_singleton, map_natCast]
  have h𝔭0 : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔭
  have h𝔮0 : (𝔮 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔮
  have hPQ : P ⊔ Q = ⊤ := by
    rw [← Ideal.map_sup, Ideal.IsMaximal.coprime_of_ne (h𝔭.isMaximal h𝔭0) (h𝔮.isMaximal h𝔮0)
      (Ne.symm hne), Ideal.map_top]
  have hcop : ∀ (u : 𝓞 F) (R T : Ideal (𝓞 F)), R ⊔ T = ⊤ →
      (∀ M : Ideal (𝓞 F), M.IsMaximal → ¬ R ≤ M → u ∉ M) → Ideal.span {u} ⊔ T = ⊤ := by
    intro u R T hRT hu
    by_contra h
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ h
    have huM : u ∈ M := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
    have hRM : R ≤ M := by
      by_contra hR
      exact hu M hM hR huM
    have hTM : T ≤ M := le_trans le_sup_right hle
    exact hM.ne_top (top_le_iff.1 (hRT ▸ sup_le hRM hTM))
  have hAQ : IsCoprime (Ideal.span {u₁}) (Q ^ 12) :=
    (Ideal.isCoprime_iff_sup_eq.2 (hcop u₁ P Q hPQ hQ₁)).pow_right
  have hBP : IsCoprime (Ideal.span {u₂}) (P ^ 12) :=
    (Ideal.isCoprime_iff_sup_eq.2 (hcop u₂ Q P (by rw [sup_comm]; exact hPQ) hQ₂)).pow_right
  obtain ⟨X, hX⟩ : Ideal.span {u₁} ∣ P ^ 12 :=
    hAQ.dvd_of_dvd_mul_right (hAB ▸ dvd_mul_right _ _)
  obtain ⟨Y, hY⟩ : Ideal.span {u₂} ∣ Q ^ 12 :=
    hBP.dvd_of_dvd_mul_left (hAB ▸ dvd_mul_left _ _)
  have hne0 : Ideal.span {u₁} * Ideal.span {u₂} ≠ 0 := by
    rw [hAB, Ideal.zero_eq_bot]
    have := map_ne_bot ι (𝔭 * 𝔮) 12
    rwa [Submonoid.coe_mul, Ideal.map_mul, mul_pow] at this
  have hXY : X * Y = 1 := by
    have e : Ideal.span {u₁} * Ideal.span {u₂} * (X * Y) = Ideal.span {u₁} * Ideal.span {u₂} * 1 := by
      rw [mul_one]
      conv_rhs => rw [hAB, hX, hY]
      ring
    exact mul_left_cancel₀ hne0 e
  have hX1 : X = ⊤ := by
    apply top_le_iff.1
    rw [← Ideal.one_eq_top, ← hXY, mul_comm]
    exact Ideal.mul_le_right
  rw [hX, hX1, Ideal.mul_top]

theorem wIdealAt_prime [Algebra.IsQuadraticExtension ℚ K] {S : PrimeDiscriminant K}
    [IsTotallyComplex K] (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S)
    (σ : K →+* ℂ) (L : PeriodPair) (hL : latticeEnd L = cmRing σ) (𝔭 : (Ideal (𝓞 K))⁰)
    (h𝔭 : (𝔭 : Ideal (𝓞 K)).IsPrime) : WIdealAt σ L 𝔭 := by
  have h𝔭0 : (𝔭 : Ideal (𝓞 K)) ≠ ⊥ := by rw [← Ideal.zero_eq_bot]; exact nonZeroDivisors.coe_ne_zero 𝔭
  rcases prime_cases S.prime S.discr_eq (𝔭 : Ideal (𝓞 K)) h𝔭0 with ⟨a, ha⟩ | ⟨p, hp, hN𝔭, 𝔮, h𝔮, hN𝔮, hpq, hne⟩
  · have ha0 : a ≠ 0 := by
      rintro rfl
      rw [Ideal.span_singleton_eq_bot.2 rfl] at ha
      exact h𝔭0 ha
    have e : 𝔭 = spanNZ a ha0 := Subtype.ext ha
    rw [e]
    exact wIdealAt_span σ L hL a ha0
  · have h𝔮0 : 𝔮 ≠ 0 := by
      rintro rfl
      rw [Ideal.zero_eq_bot, Ideal.absNorm_bot] at hN𝔮
      exact hp.ne_zero hN𝔮.symm
    exact wIdealAt_split hC hU σ L hL p hp 𝔭 ⟨𝔮, mem_nonZeroDivisors_of_ne_zero h𝔮0⟩ h𝔭 h𝔮 hN𝔭
      hN𝔮 hpq hne

theorem WIdeal.proof [Algebra.IsQuadraticExtension ℚ K] (S : PrimeDiscriminant K)
    (hC : WCocycle.Statement S) (hU : WUnitOffPrime.Statement S) : WIdeal.Statement S := by
  have : IsTotallyComplex K := by
    have hd : discr K < 0 := by
      rw [S.discr_eq]
      exact neg_neg_of_pos (by exact_mod_cast S.prime.pos)
    exact nrRealPlaces_eq_zero_iff.1 (Quadratic.places_of_discr_neg K hd).1
  intro σ L hL 𝔞
  suffices H : ∀ I : Ideal (𝓞 K), ∀ hI : I ≠ 0, ∀ L : PeriodPair, latticeEnd L = cmRing σ →
      WIdealAt σ L ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ from
    H 𝔞 (nonZeroDivisors.coe_ne_zero 𝔞) L hL
  intro I
  refine UniqueFactorizationMonoid.induction_on_prime I ?_ ?_ ?_
  · intro h
    exact absurd rfl h
  · intro x hx hI L hL
    have e : (⟨x, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰) = spanNZ 1 one_ne_zero :=
      Subtype.ext (by show x = Ideal.span {1}; rw [Ideal.isUnit_iff.1 hx, Ideal.span_singleton_one])
    rw [e]
    exact wIdealAt_span σ L hL 1 one_ne_zero
  · intro a 𝔭 ha h𝔭 ih hI L hL
    have h𝔭0 : 𝔭 ≠ 0 := h𝔭.ne_zero
    let A : (Ideal (𝓞 K))⁰ := ⟨a, mem_nonZeroDivisors_of_ne_zero ha⟩
    let P : (Ideal (𝓞 K))⁰ := ⟨𝔭, mem_nonZeroDivisors_of_ne_zero h𝔭0⟩
    have e : (⟨𝔭 * a, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 K))⁰) = A * P :=
      Subtype.ext (mul_comm 𝔭 a)
    obtain ⟨L', hL'lat, hL'⟩ :=
      exists_lattice_mul σ (Algebra.IsQuadraticExtension.finrank_eq_two ℚ K) L hL (FractionalIdeal.mk0 K A)
    rw [e]
    exact wIdealAt_mul hC σ L hL A P L' hL'lat (ih ha L hL)
      (wIdealAt_prime hC hU σ L' hL' P (Ideal.isPrime_of_prime h𝔭))

end

end GroundTheory.Heights₂.Heights.ChowlaSelberg
end
