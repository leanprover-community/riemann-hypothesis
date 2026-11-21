import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IdealValuations.ResidueUnit
import Mathlib

section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

private theorem count_coe_map_conj (v : HeightOneSpectrum (𝓞 K)) (J : Ideal (𝓞 K)) :
    FractionalIdeal.count K v
        ((J.map (ringOfIntegersComplexConj K).toRingEquiv : Ideal (𝓞 K)) :
          FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (J : FractionalIdeal (𝓞 K)⁰ K) := by
  classical
  set c := (ringOfIntegersComplexConj K).toRingEquiv with hc
  rcases eq_or_ne J 0 with rfl | hJ
  · simp [FractionalIdeal.count_zero]
  have hJ' : J.map c ≠ 0 := by
    intro h
    exact hJ ((Ideal.map_eq_bot_iff_of_injective c.injective).mp h)
  rw [FractionalIdeal.count_coe K v hJ', FractionalIdeal.count_coe K _ hJ]
  congr 1
  refine eq_of_forall_le_iff fun n => ?_
  rw [← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ') v.associates_irreducible,
    ← Associates.prime_pow_dvd_iff_le (Associates.mk_ne_zero.mpr hJ)
      (conjPrime v).associates_irreducible,
    ← Associates.mk_pow, ← Associates.mk_pow, Associates.mk_le_mk_iff_dvd,
    Associates.mk_le_mk_iff_dvd, Ideal.dvd_iff_le, Ideal.dvd_iff_le, Ideal.map_le_iff_le_comap]
  have h1 : (conjPrime v).asIdeal = v.asIdeal.comap c := rfl
  rw [h1, ← Ideal.map_symm, ← Ideal.map_symm, Ideal.map_pow]

private theorem count_spanSingleton_conj_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K (a : K))) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)) := by
  have h := count_coe_map_conj v (Ideal.span {a})
  rw [Ideal.map_span, Set.image_singleton, FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.coeIdeal_span_singleton] at h
  exact h

theorem count_spanSingleton_conj (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    FractionalIdeal.count K v (FractionalIdeal.spanSingleton (𝓞 K)⁰ (complexConj K x)) =
      FractionalIdeal.count K (conjPrime v) (FractionalIdeal.spanSingleton (𝓞 K)⁰ x) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [FractionalIdeal.count_zero]
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) x
  have ha0 : algebraMap (𝓞 K) K a ≠ 0 := fun h => hx (by simp [h])
  have hb0 : algebraMap (𝓞 K) K b ≠ 0 := fun h => hx (by simp [h])
  have key : ∀ (w : HeightOneSpectrum (𝓞 K)) (y z : K), y ≠ 0 → z ≠ 0 →
      FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ (y / z)) =
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ y) -
        FractionalIdeal.count K w (FractionalIdeal.spanSingleton (𝓞 K)⁰ z) := by
    intro w y z hy hz
    rw [div_eq_mul_inv, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
      FractionalIdeal.count_mul K w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hy)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (inv_ne_zero hz)),
      ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv, sub_eq_add_neg]
  rw [map_div₀, key _ _ _ (by simpa using ha0) (by simpa using hb0), key _ _ _ ha0 hb0]
  congr 1
  · exact count_spanSingleton_conj_int v a
  · exact count_spanSingleton_conj_int v b

theorem count_fromBase (v : HeightOneSpectrum (𝓞 K)) {b : IdealGroup K} (hb : b ∈ fromBase K) :
    FractionalIdeal.count K v (b : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) (b : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨I, hI⟩ := hb
  obtain ⟨d, J, hd, hIJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul
    (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))
  have hbI : (b : FractionalIdeal (𝓞 K)⁰ K) = FractionalIdeal.extendedHom K (𝓞 K)
      (I : FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K)) := by
    rw [← hI]; rfl
  have hd1 : (FractionalIdeal.spanSingleton (𝓞 (maximalRealSubfield K))⁰
      (algebraMap _ (maximalRealSubfield K) d)⁻¹) =
      ((Ideal.span {d} : Ideal (𝓞 (maximalRealSubfield K))) :
        FractionalIdeal (𝓞 (maximalRealSubfield K))⁰ (maximalRealSubfield K))⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_inv]
  have key : ∀ A : Ideal (𝓞 (maximalRealSubfield K)),
      FractionalIdeal.count K v ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.count K (conjPrime v) ((A.map (algebraMap _ (𝓞 K)) : Ideal (𝓞 K)) :
        FractionalIdeal (𝓞 K)⁰ K) := by
    intro A
    rw [← count_coe_map_conj]
    congr 2
    have : ((ringOfIntegersComplexConj K).toRingEquiv : 𝓞 K →+* 𝓞 K).comp
        (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K)) = algebraMap _ _ := by
      ext1 x
      exact (ringOfIntegersComplexConj K).commutes x
    conv_lhs => rw [← this, ← Ideal.map_map]
    rfl
  rw [hIJ, hd1, map_mul, map_inv₀, FractionalIdeal.extendedHom_coeIdeal_eq_map,
    FractionalIdeal.extendedHom_coeIdeal_eq_map] at hbI
  have hb0 := b.ne_zero
  rw [hbI] at hb0 ⊢
  rw [FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_mul K _ (left_ne_zero_of_mul hb0) (right_ne_zero_of_mul hb0),
    FractionalIdeal.count_inv, FractionalIdeal.count_inv, key, key]

end KStar.IdealValuations
end

section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K]

private theorem residueHom_algebraMap (P : Ideal (𝓞 K)) [P.IsMaximal] (a : 𝓞 K) :
    residueHom P (algebraMap (𝓞 K) (locAt P) a) = Ideal.Quotient.mk P a := by
  unfold residueHom
  exact IsLocalization.lift_eq _ a

theorem isResidue_iff (P : Ideal (𝓞 K)) [P.IsMaximal] (x : K) (r : 𝓞 K ⧸ P) :
    IsResidue P x r ↔ ∃ y : locAt P, (y : K) = x ∧ residueHom P y = r := by
  constructor
  · rintro ⟨a, b, hb, h1, h2⟩
    have hb0 : (b : K) ≠ 0 := by
      intro h
      have : b = 0 := by exact_mod_cast h
      exact hb (this ▸ P.zero_mem)
    have hx : x ∈ locAt P := ⟨a, b, hb, by
      have : x = (a : K) * (b : K)⁻¹ := by rw [← h1]; field_simp
      exact this⟩
    refine ⟨⟨x, hx⟩, rfl, ?_⟩
    have e : (⟨x, hx⟩ : locAt P) * algebraMap (𝓞 K) (locAt P) b
        = algebraMap (𝓞 K) (locAt P) a := Subtype.ext h1
    have e2 := congrArg (residueHom P) e
    rw [map_mul, residueHom_algebraMap, residueHom_algebraMap, ← h2] at e2
    have hb' : Ideal.Quotient.mk P b ≠ 0 := fun h => hb (Ideal.Quotient.eq_zero_iff_mem.mp h)
    exact mul_right_cancel₀ hb' e2
  · rintro ⟨y, rfl, rfl⟩
    obtain ⟨⟨a, b⟩, e⟩ := IsLocalization.surj P.primeCompl y
    refine ⟨a, b, b.2, congrArg Subtype.val e, ?_⟩
    have e2 := congrArg (residueHom P) e
    rwa [map_mul, residueHom_algebraMap, residueHom_algebraMap] at e2

private theorem valuation_eq_exp_count_int (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (ha : a ≠ 0) :
    v.valuation K (a : K) = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K))) := by
  have h1 : v.valuation K (a : K) = v.intValuation a := v.valuation_of_algebraMap a
  have h2 : FractionalIdeal.spanSingleton (𝓞 K)⁰ (a : K)
      = ((Ideal.span {a} : Ideal (𝓞 K)) : FractionalIdeal (𝓞 K)⁰ K) :=
    (FractionalIdeal.coeIdeal_span_singleton a).symm
  rw [h1, h2, v.intValuation_if_neg ha, FractionalIdeal.count_coe K v (by simpa using ha)]

private theorem valuation_eq_exp_count (v : HeightOneSpectrum (𝓞 K)) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ x)) := by
  obtain ⟨a, b, hb, e⟩ := IsFractionRing.div_surjective (𝓞 K) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : (b : K) ≠ 0 := by exact_mod_cast hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hx
    simp [← e]
  have e' : x * (b : K) = (a : K) := by
    rw [← e]; exact div_mul_cancel₀ _ hbK
  have h1 := valuation_eq_exp_count_int v a ha0
  have h2 := valuation_eq_exp_count_int v b hb0
  rw [← e', map_mul, h2, ← FractionalIdeal.spanSingleton_mul_spanSingleton,
    FractionalIdeal.count_mul K v (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hbK), neg_add, WithZero.exp_add] at h1
  exact mul_right_cancel₀ WithZero.exp_ne_zero h1

private theorem mem_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : K) :
    x ∈ locAt v.asIdeal ↔ v.valuation K x ≤ 1 := by
  have h : x ∈ locAt v.asIdeal ↔ x ∈ v.valuationSubringAtPrime K := Iff.rfl
  rw [h, HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring,
    Valuation.mem_valuationSubring_iff]

theorem exists_unit_locAt_iff (v : HeightOneSpectrum (𝓞 K)) (x : Kˣ) :
    (∃ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (x : K)) ↔
      FractionalIdeal.count K v
        ((toPrincipalIdeal (𝓞 K) K x : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
          FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  have key : v.valuation K (x : K) = 1 ↔ FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton (𝓞 K)⁰ (x : K)) = 0 := by
    rw [valuation_eq_exp_count v _ x.ne_zero, ← WithZero.exp_zero, WithZero.exp_inj, neg_eq_zero]
  rw [coe_toPrincipalIdeal, ← key]
  constructor
  · rintro ⟨u, hu⟩
    have h1 := (mem_locAt_iff v _).mp (u : locAt v.asIdeal).2
    have h2 := (mem_locAt_iff v _).mp ((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal).2
    have h3 : ((u : locAt v.asIdeal) : K) * (((u⁻¹ : (locAt v.asIdeal)ˣ) : locAt v.asIdeal) : K)
        = 1 := congrArg Subtype.val u.mul_inv
    have h4 := congrArg (v.valuation K) h3
    rw [map_mul, map_one] at h4
    rw [← hu]
    exact eq_one_of_one_le_mul_left h1 h2 h4.ge
  · intro h
    have h1 : (x : K) ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr h.le
    have h2 : (x : K)⁻¹ ∈ locAt v.asIdeal := (mem_locAt_iff v _).mpr (by rw [map_inv₀, h]; simp)
    exact ⟨⟨⟨_, h1⟩, ⟨_, h2⟩, Subtype.ext (mul_inv_cancel₀ x.ne_zero),
      Subtype.ext (inv_mul_cancel₀ x.ne_zero)⟩, rfl⟩

end KStar.IdealValuations
end

section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

theorem exists_unit_div_conj (v : HeightOneSpectrum (𝓞 K)) {A b : IdealGroup K}
    (hA : A ∈ primeTo v) (hb : b ∈ fromBase K) {α : Kˣ}
    (h : A = toPrincipalIdeal (𝓞 K) K α * b) :
    ∃ u : (locAt v.asIdeal)ˣ, ((u : locAt v.asIdeal) : K) = (α : K) / complexConj K (α : K) := by
  have hc : complexConj K (α : K) ≠ 0 := by
    simp
  have key := (exists_unit_locAt_iff v (α / Units.mk0 _ hc)).mpr ?_
  · simpa using key
  obtain ⟨h1, h2⟩ := hA
  subst h
  have hb' := count_fromBase v hb
  have hα := count_spanSingleton_conj v (α : K)
  rw [Units.val_mul, FractionalIdeal.count_mul K _ (Units.ne_zero _) (Units.ne_zero _),
    coe_toPrincipalIdeal] at h1 h2
  rw [div_eq_mul_inv, map_mul, map_inv, Units.val_mul,
    FractionalIdeal.count_mul K _ (Units.ne_zero _) (Units.ne_zero _), Units.val_inv_eq_inv_val,
    FractionalIdeal.count_inv, coe_toPrincipalIdeal, coe_toPrincipalIdeal, Units.val_mk0, hα]
  omega

end KStar.IdealValuations
end

section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

private theorem pow_bijective_zmod {l M h : ℕ} (hh : h.Coprime l) :
    Function.Bijective (fun x : Multiplicative (ZMod (l ^ M)) => x ^ h) := by
  have hc : (Nat.card (Multiplicative (ZMod (l ^ M)))).Coprime h := by
    have : Nat.card (Multiplicative (ZMod (l ^ M))) = l ^ M := by
      rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod (l ^ M))), Nat.card_zmod]
    rw [this]
    exact Nat.Coprime.pow_left _ hh.symm
  exact (powCoprime hc).bijective

theorem IsDel.values {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)}
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))}
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del) :
    (∀ (α : Kˣ) (hα : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v) (u : (locAt v.asIdeal)ˣ),
      ((u : locAt v.asIdeal) : K) = (α : K) / complexConj K (α : K) →
        del ⟨_, hα⟩ = om (residueUnit v.asIdeal u)) ∧
    (∀ A : primeTo v, (A : IdealGroup K) ∈ fromBase K → del A = 1) ∧
    (∀ (i : ι) (hi : B.aa i ∈ primeTo v), del ⟨_, hi⟩ = 1) := by
  classical
  have hbij := pow_bijective_zmod (M := M) B.h_coprime
  have hone : ∀ A : primeTo v, IsDecomp B.h B.aa (A : IdealGroup K) 1 → del A = 1 := by
    intro A hA
    apply hbij.1
    change del A ^ B.h = 1 ^ B.h
    rw [hdel A 1 hA 1 (by simp), map_one, map_one, one_pow]
  refine ⟨?_, ?_, ?_⟩
  · intro α hα u hu
    apply hbij.1
    change del ⟨_, hα⟩ ^ B.h = om (residueUnit v.asIdeal u) ^ B.h
    rw [← map_pow om, ← map_pow (residueUnit v.asIdeal)]
    refine hdel ⟨_, hα⟩ (α ^ B.h) ⟨0, 1, one_mem _, by simp⟩ _ ?_
    rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, hu, Units.val_pow_eq_pow_val, map_pow,
      div_pow]
  · intro A hA
    exact hone A ⟨0, (A : IdealGroup K) ^ B.h, pow_mem hA _, by simp⟩
  · intro i hi
    refine hone _ ⟨Pi.single i (B.h : ℤ), 1, one_mem _, ?_⟩
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp

end KStar.IdealValuations
end

section
open NumberField NumberField.IsCMField NumberField.Units IsDedekindDomain
open scoped nonZeroDivisors

namespace KStar.IdealValuations

variable {K : Type*} [Field K] [NumberField K] [IsCMField K]

omit [IsCMField K] in
private theorem delRay_count_eq_zero (w : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) (α : Kˣ)
    (hα : (α : K) = (a : K)) (ha : a ∉ w.asIdeal) :
    FractionalIdeal.count K w
      ((toPrincipalIdeal (𝓞 K) K α : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
        FractionalIdeal (𝓞 K)⁰ K) = 0 := by
  rw [← exists_unit_locAt_iff]
  have hu : IsUnit (algebraMap (𝓞 K) (locAt w.asIdeal) a) :=
    IsLocalization.map_units (M := w.asIdeal.primeCompl) (locAt w.asIdeal) ⟨a, ha⟩
  exact ⟨hu.unit, by rw [hα, hu.unit_spec]; rfl⟩

theorem IsDel.apply_of_congr {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)}
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))}
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del)
    (a : 𝓞 K) (α : Kˣ) (hα : (α : K) = (a : K)) (r : (𝓞 K ⧸ v.asIdeal)ˣ)
    (hr : Ideal.Quotient.mk v.asIdeal a = r) (h1 : a - 1 ∈ (conjPrime v).asIdeal) :
    ∃ h : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v, del ⟨_, h⟩ = om r := by
  have hav : a ∉ v.asIdeal := by
    intro h
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    rw [hr] at h0
    exact r.ne_zero h0
  have hac : a ∉ (conjPrime v).asIdeal := by
    intro h
    apply (conjPrime v).isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    simpa using (conjPrime v).asIdeal.sub_mem h h1
  have hmem : toPrincipalIdeal (𝓞 K) K α ∈ primeTo v :=
    ⟨delRay_count_eq_zero v a α hα hav, delRay_count_eq_zero _ a α hα hac⟩
  refine ⟨hmem, ?_⟩
  set b : 𝓞 K := ringOfIntegersComplexConj K a with hb
  have hb1 : b - 1 ∈ v.asIdeal := by
    have h2 : ringOfIntegersComplexConj K (a - 1) ∈ v.asIdeal := h1
    rwa [map_sub, map_one] at h2
  have hbq : Ideal.Quotient.mk v.asIdeal b = 1 := by
    rw [← map_one (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq.mpr hb1
  have hbv : b ∉ v.asIdeal := by
    intro h
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr h] at hbq
    exact zero_ne_one hbq
  have hbK : (b : K) = complexConj K (α : K) := by rw [hα]; rfl
  have hb0 : complexConj K (α : K) ≠ 0 := by simp
  obtain ⟨u, hu⟩ := exists_unit_div_conj v (α := α) hmem (one_mem _) (by simp)
  rw [(hdel.values hl).1 α hmem u hu]
  congr 1
  have hres : IsResidue v.asIdeal ((α : K) / complexConj K (α : K)) r :=
    ⟨a, b, hbv, by rw [hbK, div_mul_cancel₀ _ hb0, hα], by rw [hbq, mul_one, hr]⟩
  obtain ⟨y, hy, hy2⟩ := (isResidue_iff _ _ _).mp hres
  have hyu : y = (u : locAt v.asIdeal) := Subtype.ext (hy.trans hu.symm)
  rw [hyu] at hy2
  exact Units.ext hy2

theorem IsDel.surjective {l M : ℕ} (hl : l.Prime) {ι : Type*} [Fintype ι]
    {B : MinusBasis K l ι} {v : HeightOneSpectrum (𝓞 K)} (hv : conjPrime v ≠ v)
    {om : (𝓞 K ⧸ v.asIdeal)ˣ →* Multiplicative (ZMod (l ^ M))} (hom : Function.Surjective om)
    {del : primeTo v →* Multiplicative (ZMod (l ^ M))} (hdel : IsDel B v om del) :
    Function.Surjective del := by
  intro t
  obtain ⟨r, rfl⟩ := hom t
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (r : 𝓞 K ⧸ v.asIdeal)
  have hco : v.asIdeal ⊔ (conjPrime v).asIdeal = ⊤ :=
    Ideal.IsMaximal.coprime_of_ne v.isMaximal (conjPrime v).isMaximal
      (fun h => hv (HeightOneSpectrum.ext h.symm))
  have h1 : (1 : 𝓞 K) ∈ v.asIdeal ⊔ (conjPrime v).asIdeal := by rw [hco]; trivial
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.mp h1
  have hr : Ideal.Quotient.mk v.asIdeal (x + s * y) = r := by
    rw [← hs]
    refine Ideal.Quotient.eq.mpr ?_
    have e : x + s * y - s = (1 - s) * x := by linear_combination s * hxy
    rw [e]
    exact v.asIdeal.mul_mem_left _ hx
  have ha1 : x + s * y - 1 ∈ (conjPrime v).asIdeal := by
    have e : x + s * y - 1 = (s - 1) * y := by linear_combination hxy
    rw [e]
    exact (conjPrime v).asIdeal.mul_mem_left _ hy
  have ha0 : ((x + s * y : 𝓞 K) : K) ≠ 0 := by
    intro h
    rw [RingOfIntegers.coe_eq_zero_iff.mp h, map_zero] at hr
    exact r.ne_zero hr.symm
  obtain ⟨h, hh⟩ := hdel.apply_of_congr hl (x + s * y) (Units.mk0 _ ha0) rfl r hr ha1
  exact ⟨_, hh⟩

end KStar.IdealValuations
end
