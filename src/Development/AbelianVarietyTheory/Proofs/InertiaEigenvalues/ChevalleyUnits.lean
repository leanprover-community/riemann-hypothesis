import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChevalleyUnits
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import BuildAid.ForwardExisting
import ReciprocityTheory.GaloisValuations.Global

section
open NumberField

namespace GlobalTheory

namespace CyclotomicKummerDescent

theorem geom_sum_valuation {l : ℕ} (hl : l.Prime) {t : ℕ} (ht1 : 1 < t)
    (ht : (l : ℤ) ^ 2 ∣ (t : ℤ) - 1) (r : ℕ) :
    l ^ r ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i ∧
      ¬ l ^ (r + 1) ∣ ∑ i ∈ Finset.range (l ^ r), t ^ i := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl
  have h1 : (l : ℤ) ∣ (t : ℤ) - 1 := (dvd_pow_self _ two_ne_zero).trans ht
  have h2 : ¬ (l : ℤ) ∣ (t : ℤ) := fun h => hp.not_dvd_one (by simpa using dvd_sub h h1)
  have hlte : emultiplicity (l : ℤ) ((t : ℤ) ^ (l ^ r) - 1 ^ (l ^ r)) =
      emultiplicity (l : ℤ) ((t : ℤ) - 1) + r := by
    rcases hl.eq_two_or_odd' with rfl | hodd
    · have h := Int.two_pow_sub_pow' (x := t) (y := 1) (2 ^ r) (by simpa using ht)
        (by simpa using h2)
      have h3 : emultiplicity (2 : ℤ) ((2 ^ r : ℕ) : ℤ) = r := by
        push_cast
        exact emultiplicity_pow_self_of_prime Int.prime_two r
      rw [h3] at h
      simpa using h
    · rw [Int.emultiplicity_pow_sub_pow hl hodd h1 h2,
        emultiplicity_pow_self_of_prime hl.prime]
  rw [one_pow, ← geom_sum_mul, emultiplicity_mul hp, add_comm] at hlte
  have hfin : emultiplicity (l : ℤ) ((t : ℤ) - 1) ≠ ⊤ := by
    rw [← finiteMultiplicity_iff_emultiplicity_ne_top, Int.finiteMultiplicity_iff]
    refine ⟨by simpa using hl.ne_one, ?_⟩
    have : (1 : ℤ) < t := by exact_mod_cast ht1
    omega
  have h4 : emultiplicity (l : ℤ) (∑ i ∈ Finset.range (l ^ r), (t : ℤ) ^ i) = (r : ℕ∞) :=
    WithTop.add_left_cancel hfin hlte
  rw [emultiplicity_eq_coe] at h4
  exact_mod_cast h4

theorem exists_aut {E K : Type} [Field E] [NumberField E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {g : ℕ}
    (hg : g.Coprime M) :
    ∃ τ : K ≃ₐ[E] K, τ ζ = ζ ^ (g ^ (Module.finrank ℚ E).factorial) := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  haveI : NumberField K := NumberField.of_module_finite E K
  set H := (hζ.autToPow E).range with hH
  have hcard : Nat.card H = Module.finrank E K := by
    rw [← IsGalois.card_aut_eq_finrank]
    exact (Nat.card_congr (MonoidHom.ofInjective (hζ.autToPow_injective E)).toEquiv).symm
  have htot : M.totient ≤ Module.finrank ℚ E * Module.finrank E K := by
    rw [Module.finrank_mul_finrank, ← Polynomial.natDegree_cyclotomic M ℚ,
      Polynomial.cyclotomic_eq_minpoly_rat hζ (NeZero.pos M)]
    exact minpoly.natDegree_le ζ
  have hidx : H.index * Nat.card H = M.totient := by
    rw [Subgroup.index_mul_card, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
  have hle : H.index ≤ Module.finrank ℚ E := by
    rw [← hidx, hcard] at htot
    exact Nat.le_of_mul_le_mul_right htot Module.finrank_pos
  have hdvd : H.index ∣ (Module.finrank ℚ E).factorial :=
    Nat.dvd_factorial (Nat.pos_of_ne_zero H.index_ne_zero_of_finite) hle
  have hmem : ZMod.unitOfCoprime g hg ^ (Module.finrank ℚ E).factorial ∈ H := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, pow_mul]
    exact H.pow_mem (H.pow_index_mem _) c
  obtain ⟨τ, hτ⟩ := hmem
  refine ⟨τ, ?_⟩
  rw [← hζ.autToPow_spec E τ, hτ, Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime,
    ← Nat.cast_pow, ZMod.val_natCast]
  exact (pow_eq_pow_mod _ hζ.pow_eq_one).symm

theorem descent {E K : Type} [Field E] [Field K] [Algebra E K] {M : ℕ}
    [NeZero M] [IsCyclotomicExtension {M} E K] {ζ : K} (hζ : IsPrimitiveRoot ζ M) {k n : ℕ}
    (τ : K ≃ₐ[E] K) (hτ : τ ζ = ζ ^ (k + 1))
    (hN : M ∣ (∑ i ∈ Finset.range n, (k + 1) ^ i) * k) {u : E} {w : K} (hw0 : w ≠ 0)
    (hw : w ^ M = algebraMap E K u) :
    ∃ (α : K) (v : E), α ^ M = 1 ∧ α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 ∧
      algebraMap E K v * α = w ^ k := by
  haveI := IsCyclotomicExtension.finiteDimensional {M} E K
  haveI := IsCyclotomicExtension.isGalois {M} E K
  have hext : ∀ σ σ' : K ≃ₐ[E] K, σ ζ = σ' ζ → σ = σ' := by
    intro σ σ' h
    apply hζ.autToPow_injective E
    rw [← hζ.autToPow_spec E σ, ← hζ.autToPow_spec E σ'] at h
    exact Units.ext (ZMod.val_injective M (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) h))
  have hcomm : ∀ σ : K ≃ₐ[E] K, σ * τ = τ * σ := fun σ =>
    hζ.autToPow_injective E (by rw [map_mul, map_mul, mul_comm])
  have hroot : ∀ η : K, η ^ M = 1 → τ η = η ^ (k + 1) := by
    intro η hη
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
    rw [map_pow, hτ, ← pow_mul, ← pow_mul, mul_comm]
  have hcoc : ∀ σ : K ≃ₐ[E] K, ∃ a : K, a ^ M = 1 ∧ σ w = a * w := by
    intro σ
    refine ⟨σ w / w, ?_, by field_simp⟩
    rw [div_pow, ← map_pow, hw, AlgEquiv.commutes, ← hw, div_self (pow_ne_zero _ hw0)]
  have hne : ∀ a : K, a ^ M = 1 → a ≠ 0 := by
    rintro a ha rfl
    rw [zero_pow (NeZero.ne M)] at ha
    exact zero_ne_one ha
  obtain ⟨α, hαM, hα⟩ := hcoc τ
  have hα0 := hne α hαM
  have hiter : ∀ m : ℕ, (τ ^ m) w = α ^ (∑ i ∈ Finset.range m, (k + 1) ^ i) * w ∧
      (τ ^ m) ζ = ζ ^ ((k + 1) ^ m) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', AlgEquiv.mul_apply, AlgEquiv.mul_apply, ih.1, ih.2, map_mul, map_pow,
        map_pow, hτ, hα, hroot α hαM, geom_sum_succ]
      constructor <;> ring
  have hgeom : ∀ m : ℕ, (k + 1) ^ m = (∑ i ∈ Finset.range m, (k + 1) ^ i) * k + 1 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, pow_succ, add_mul, mul_add, mul_one]; omega
  have hτn : τ ^ n = 1 := by
    apply hext
    obtain ⟨c, hc⟩ := hN
    rw [(hiter n).2, hgeom, hc, pow_succ, pow_mul, hζ.pow_eq_one]
    simp
  have hαN : α ^ (∑ i ∈ Finset.range n, (k + 1) ^ i) = 1 := by
    have h := (hiter n).1
    rw [hτn, AlgEquiv.one_apply] at h
    exact mul_right_cancel₀ hw0 (by rw [← h, one_mul])
  have hfix : ∀ σ : K ≃ₐ[E] K, σ (w ^ k / α) = w ^ k / α := by
    intro σ
    obtain ⟨a, haM, ha⟩ := hcoc σ
    have ha0 := hne a haM
    have h := congrArg (fun f : K ≃ₐ[E] K => f w) (hcomm σ)
    simp only [AlgEquiv.mul_apply] at h
    rw [hα, ha, map_mul, map_mul, ha, hα, hroot a haM] at h
    have hσα : σ α = a ^ k * α :=
      mul_right_cancel₀ (mul_ne_zero ha0 hw0) (by rw [h]; ring)
    rw [map_div₀, map_pow, hσα, ha, mul_pow]
    field_simp
  obtain ⟨v, hv⟩ := (IsGalois.mem_range_algebraMap_iff_fixed _).mpr hfix
  exact ⟨α, v, hαM, hαN, by rw [hv]; field_simp⟩

end CyclotomicKummerDescent

open CyclotomicKummerDescent in

theorem exists_pow_descent_cyclotomic :
    ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u →
        ∃ v : E, v ^ (l ^ r) = u := by
  intro E _ _ l r hl
  set m := (Module.finrank ℚ E).factorial with hm
  have ht1 : 1 < (1 + l ^ 2) ^ m :=
    Nat.one_lt_pow (Nat.factorial_ne_zero _) (by have := pow_pos hl.pos 2; omega)
  obtain ⟨k, hk⟩ : ∃ k, (1 + l ^ 2) ^ m = k + 1 := ⟨_, (Nat.sub_add_cancel ht1.le).symm⟩
  have hk0 : k ≠ 0 := by omega
  obtain ⟨s, e, he, hke⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk0 l hl.ne_one
  have hdiv : (l : ℤ) ^ 2 ∣ (((1 + l ^ 2) ^ m : ℕ) : ℤ) - 1 := by
    have := sub_dvd_pow_sub_pow (1 + (l : ℤ) ^ 2) 1 m
    simpa using this
  obtain ⟨hN1, hN2⟩ := geom_sum_valuation hl ht1 hdiv r
  rw [hk] at hN1 hN2
  refine ⟨l ^ (r + s), pow_pos hl.pos _, pow_dvd_pow _ (by omega), ?_⟩
  intro Ω _ _ ζ hζ u w hwK hw
  haveI : NeZero (l ^ (r + s)) := ⟨pow_ne_zero _ hl.ne_zero⟩
  have hint : IsIntegral E ζ := (hζ.isIntegral (NeZero.pos _)).tower_top
  set K := IntermediateField.adjoin E {ζ} with hK
  haveI : IsCyclotomicExtension {l ^ (r + s)} E K := by
    change IsCyclotomicExtension {l ^ (r + s)} E K.toSubalgebra
    rw [hK, IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hζ.adjoin_isCyclotomicExtension E
  let ζ' : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζ' : IsPrimitiveRoot ζ' (l ^ (r + s)) :=
    IsPrimitiveRoot.of_map_of_injective (f := K.val) hζ K.val.injective
  let w' : K := ⟨w, hwK⟩
  have hw' : w' ^ (l ^ (r + s)) = algebraMap E K u := Subtype.ext hw
  rcases eq_or_ne u 0 with rfl | hu
  · exact ⟨0, zero_pow (pow_ne_zero _ hl.ne_zero)⟩
  have hw0 : w' ≠ 0 := by
    intro h
    rw [h, zero_pow (NeZero.ne _), eq_comm, map_eq_zero] at hw'
    exact hu hw'
  have hg : (1 + l ^ 2).Coprime (l ^ (r + s)) := by
    apply Nat.Coprime.pow_right
    rw [sq, Nat.coprime_add_mul_left_left]
    exact Nat.coprime_one_left l
  obtain ⟨τ, hτ⟩ := exists_aut (E := E) hζ' hg
  rw [← hm, hk] at hτ
  obtain ⟨α, v, hαM, hαN, hv⟩ := descent hζ' (n := l ^ r) τ hτ
    (by rw [pow_add]; exact mul_dvd_mul hN1 ⟨e, hke⟩) hw0 hw'
  have hαr : α ^ (l ^ r) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hl).mp (orderOf_dvd_of_pow_eq_one hαM)
    have h1 := orderOf_dvd_of_pow_eq_one hαN
    rw [hj] at h1
    have hjr : j ≤ r := by
      by_contra hc
      exact hN2 ((pow_dvd_pow l (by omega)).trans h1)
    exact orderOf_dvd_iff_pow_eq_one.mp (hj ▸ pow_dvd_pow l hjr)
  have hvu : v ^ (l ^ r) = u ^ e := by
    apply (algebraMap E K).injective
    have h := congrArg (· ^ (l ^ r)) hv
    simp only [mul_pow, hαr, mul_one] at h
    rw [map_pow, map_pow, h, ← hw', hke, ← pow_mul, ← pow_mul]
    congr 1
    ring
  have hco : IsCoprime (e : ℤ) ((l ^ r : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr
      (Nat.Coprime.pow_right r ((Nat.Prime.coprime_iff_not_dvd hl).mpr he).symm)
  obtain ⟨a, b, hab⟩ := hco
  refine ⟨v ^ a * u ^ b, ?_⟩
  rw [mul_pow, ← zpow_natCast (v ^ a), ← zpow_natCast (u ^ b), ← zpow_mul, ← zpow_mul, mul_comm a,
    zpow_mul, zpow_natCast, hvu, ← zpow_natCast, ← zpow_mul, ← zpow_add₀ hu, mul_comm _ a, hab,
    zpow_one]

end GlobalTheory
end

section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_descent_cyclotomic' : ∀ (E : Type) [Field E] [NumberField E] (l r : ℕ), l.Prime → ∃ M : ℕ, 0 < M ∧ l ^ r ∣ M ∧
    ∀ (Ω : Type) [Field Ω] [Algebra E Ω] (ζ : Ω), IsPrimitiveRoot ζ M → ∀ (u : E) (w : Ω),
      w ∈ IntermediateField.adjoin E {ζ} → w ^ M = algebraMap E Ω u → ∃ v : E, v ^ (l ^ r) = u := by
  first | exact @GlobalTheory.exists_pow_descent_cyclotomic | exact GlobalTheory.exists_pow_descent_cyclotomic | (intros; apply GlobalTheory.exists_pow_descent_cyclotomic <;> assumption)
end

section
section
open NumberField Polynomial

namespace GlobalTheory.KummerUnits

theorem exists_finite_galois_mem_of_pow_eq_unit : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  intro E F Ω _ _ _ _ _ _ _ _ _ M hM ⟨ζ, hζ⟩
  haveI : NeZero M := ⟨hM.ne'⟩
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  obtain ⟨S, hS⟩ := Monoid.fg_def.1 (inferInstance : Monoid.FG (𝓞 E)ˣ)
  let c : (𝓞 E)ˣ → F := fun u => algebraMap E F ((u : 𝓞 E) : E)
  let p : F[X] := ∏ s ∈ S, (X ^ M - C (c s))
  have hp : p ≠ 0 := Finset.prod_ne_zero_iff.2 fun s _ => X_pow_sub_C_ne_zero hM _
  let L := IntermediateField.adjoin F (p.rootSet Ω)
  have hsp : p.IsSplittingField F L :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  haveI := Polynomial.IsSplittingField.finiteDimensional L p
  haveI := Normal.of_isSplittingField (F := F) (E := L) p
  refine ⟨L, inferInstance, ⟨⟩, ?_⟩
  have hζΩ : IsPrimitiveRoot (algebraMap F Ω ζ) M := hζ.map_of_injective (algebraMap F Ω).injective
  have hroot : ∀ ξ : Ω, ξ ^ M = 1 → ξ ∈ L := by
    intro ξ hξ
    obtain ⟨i, -, rfl⟩ := hζΩ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (L.algebraMap_mem ζ) i
  let φ : (𝓞 E)ˣ →* Ω :=
    ((algebraMap E Ω).toMonoidHom.comp (algebraMap (𝓞 E) E).toMonoidHom).comp (Units.coeHom _)
  have hφ : ∀ u, φ u = algebraMap E Ω ((u : 𝓞 E) : E) := fun u => rfl
  have hφc : ∀ u, φ u = algebraMap F Ω (c u) := fun u => IsScalarTower.algebraMap_apply E F Ω _
  have hφ0 : ∀ u, φ u ≠ 0 := fun u => ((Group.isUnit u).map φ).ne_zero
  intro u
  simp only [← hφ]
  have hall : u ∈ Submonoid.closure (S : Set (𝓞 E)ˣ) := by rw [hS]; trivial
  induction hall using Submonoid.closure_induction with
  | mem s hs =>
    intro w hw
    apply IntermediateField.subset_adjoin
    rw [Polynomial.mem_rootSet]
    refine ⟨hp, ?_⟩
    simp only [p, map_prod]
    refine Finset.prod_eq_zero hs ?_
    simp [hw, hφc]
  | one =>
    intro w hw
    exact hroot w (by rw [hw, map_one])
  | mul a b _ _ ha hb =>
    intro w hw
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (φ a) hM
    obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (φ b) hM
    have hxy : x * y ≠ 0 := by
      refine mul_ne_zero ?_ ?_
      · rintro rfl; exact hφ0 a (by rw [← hx, zero_pow hM.ne'])
      · rintro rfl; exact hφ0 b (by rw [← hy, zero_pow hM.ne'])
    rw [← div_mul_cancel₀ w hxy]
    refine mul_mem (hroot _ ?_) (mul_mem (ha x hx) (hb y hy))
    rw [div_pow, mul_pow, hx, hy, hw, map_mul, div_self (mul_ne_zero (hφ0 a) (hφ0 b))]

end GlobalTheory.KummerUnits
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_galois_contains_roots_of_units : ∀ (E F Ω : Type) [Field E] [NumberField E] [Field F] [Field Ω] [IsAlgClosed Ω]
    [Algebra E F] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω] (M : ℕ), 0 < M →
    (∃ ζ : F, IsPrimitiveRoot ζ M) → ∃ L : IntermediateField F Ω, FiniteDimensional F L ∧ IsGalois F L ∧
      ∀ (u : (𝓞 E)ˣ) (w : Ω), w ^ M = algebraMap E Ω ((u : 𝓞 E) : E) → w ∈ L := by
  atlas_forward_decl GlobalTheory.KummerUnits.exists_finite_galois_mem_of_pow_eq_unit
end

section
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

theorem frob_fixes_root_of_one_mod (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (M : ℕ) (ζ : F) (hζ : IsPrimitiveRoot ζ M) (v : HeightOneSpectrum (𝓞 F))
    (hMv : ((M : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (A : ValuationSubring Ω) (hA : Formalism.ConjugateSelfDual.IsPlaceOver A v) (σ : Formalism.ConjugateSelfDual.G F Ω)
    (hσ : Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ)
    (x : 𝓞 F) (hx : x - 1 ∈ v.asIdeal) (w : Ω) (hw : w ^ M = algebraMap F Ω (x : F)) :
    σ w = w := by
  set q := Formalism.ConjugateSelfDual.normV v
  set x' := algebraMap F Ω (x : F) with hx'
  have hM0 : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; simp at hMv
    · exact h
  haveI : NeZero M := ⟨hM0.ne'⟩
  have hx1 : A.valuation (x' - 1) < 1 := by
    have := (hA (x - 1)).2 hx
    simpa [hx'] using this
  have hMk : ¬ A.valuation (M : Ω) < 1 := by
    intro h; apply hMv; apply (hA (M : 𝓞 F)).1; simpa using h
  have hpow : ∀ y : Ω, y ^ M ∈ A → y ∈ A := by
    intro y hy
    rw [← A.valuation_le_one_iff] at hy ⊢
    rwa [map_pow, pow_le_one_iff hM0.ne'] at hy
  have hx'A : x' ∈ A := by
    have h1 : x' - 1 ∈ A := (A.valuation_le_one_iff _).1 hx1.le
    simpa using add_mem h1 A.one_mem
  have hwA : w ∈ A := hpow w (hw ▸ hx'A)
  set ζ' := algebraMap F Ω ζ with hζ'
  have hζ'p : IsPrimitiveRoot ζ' M := hζ.map_of_injective (algebraMap F Ω).injective
  have hσζ : ∀ n : ℕ, σ (ζ' ^ n) = ζ' ^ n := by
    intro n; rw [map_pow, hζ', AlgEquiv.commutes]
  have hσx : σ x' = x' := AlgEquiv.commutes σ _
  have hroot : ∀ μ : Ω, μ ^ M = 1 → μ ∈ A := fun μ h => hpow μ (h ▸ A.one_mem)
  let res := IsLocalRing.residue A
  have key : ∀ a b : A, res a = res b ↔ A.valuation ((a : Ω) - b) < 1 := by
    intro a b
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, A.valuation_lt_one_iff]
    simp
  have hfrob : ∀ a : A, ∃ b : A, (b : Ω) = σ a ∧ res b = res a ^ q := by
    intro a
    have h := hσ.2 a ((A.valuation_le_one_iff _).2 a.2)
    have hb : σ (a : Ω) ∈ A := by
      have h1 : σ (a:Ω) - (a:Ω) ^ q ∈ A := (A.valuation_le_one_iff _).1 h.le
      have h2 : (a : Ω) ^ q ∈ A := A.pow_mem a.2 q
      simpa using add_mem h1 h2
    refine ⟨⟨_, hb⟩, rfl, ?_⟩
    rw [← map_pow, key]; simpa using h

  obtain ⟨μ, hμM, hμ⟩ : ∃ μ : Ω, μ ^ M = 1 ∧ A.valuation (w - μ) < 1 := by
    have hprod := congrArg (Polynomial.eval w) (X_pow_sub_one_eq_prod hM0 hζ'p)
    simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at hprod
    by_contra hcon
    push_neg at hcon
    have h1 : A.valuation (w ^ M - 1) = 1 := by
      rw [hprod, map_prod]
      apply Finset.prod_eq_one
      intro μ hμ
      have hμM : μ ^ M = 1 := (mem_nthRootsFinset hM0 (1 : Ω)).1 hμ
      apply le_antisymm
      · exact (A.valuation_le_one_iff _).2 (A.sub_mem hwA (hroot μ hμM))
      · exact hcon μ hμM
    rw [hw] at h1
    rw [h1] at hx1
    exact lt_irrefl _ hx1
  obtain ⟨j, -, hj⟩ := hζ'p.eq_pow_of_pow_eq_one hμM

  let aw : A := ⟨w, hwA⟩
  let aμ : A := ⟨μ, hroot μ hμM⟩
  have hwμ : res aw = res aμ := (key aw aμ).2 hμ
  obtain ⟨bw, hbw, hbw'⟩ := hfrob aw
  obtain ⟨bμ, hbμ, hbμ'⟩ := hfrob aμ
  have hbμe : bμ = aμ := by
    apply Subtype.ext
    rw [hbμ]; show σ μ = μ
    rw [← hj, hσζ]
  rw [hbμe] at hbμ'
  have hB : res bw = res aw := by
    rw [hbw', hwμ, ← hbμ']

  have hw0 : w ≠ 0 := by
    rintro rfl
    rw [zero_pow hM0.ne'] at hw
    rw [← hw] at hx1
    simp at hx1
  have hx'0 : x' ≠ 0 := by rw [← hw]; exact pow_ne_zero _ hw0
  set ξ := σ w / w with hξ
  have hξM : ξ ^ M = 1 := by
    rw [hξ, div_pow, ← map_pow, hw, hσx, div_self hx'0]
  let aξ : A := ⟨ξ, hroot ξ hξM⟩
  have hbw_eq : bw = aξ * aw := by
    apply Subtype.ext
    show (bw : Ω) = ξ * w
    rw [hbw, hξ, div_mul_cancel₀ _ hw0]
  have hresw : res aw ≠ 0 := by
    intro h0
    have h1 : res (aw ^ M) = 0 := by rw [map_pow, h0, zero_pow hM0.ne']
    have h2 : res (aw ^ M) = res 1 := by
      rw [key]
      have : ((aw ^ M : A) : Ω) = x' := by simp [aw, hw]
      rw [this]; simpa using hx1
    rw [h1, map_one] at h2
    exact zero_ne_one h2
  have hresξ : res aξ = 1 := by
    have h := hB
    rw [hbw_eq, map_mul] at h
    exact mul_right_cancel₀ hresw (h.trans (one_mul _).symm)
  by_contra hne
  have hξ1 : ξ ≠ 1 := by
    intro h; apply hne
    rw [hξ] at h
    exact (div_eq_one_iff_eq hw0).1 h
  have hsum : ∑ l ∈ Finset.range M, ξ ^ l = 0 := by
    rw [geom_sum_eq hξ1, hξM, sub_self, zero_div]
  have hsumA : ∑ l ∈ Finset.range M, aξ ^ l = 0 := by
    apply Subtype.ext
    simpa [aξ] using hsum
  have hres : res ((M : ℕ) : A) = res 0 := by
    have := congrArg res hsumA
    rw [map_sum] at this
    simp only [map_pow, hresξ, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    rw [map_natCast, this]
  rw [key] at hres
  apply hMk
  simpa using hres

end GlobalTheory
end

section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFrob_fixes_root_of_one_mod_place : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (M : ℕ) (ζ : F),
    IsPrimitiveRoot ζ M → ∀ v : HeightOneSpectrum (𝓞 F), ((M : ℕ) : 𝓞 F) ∉ v.asIdeal →
    ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A v → ∀ σ : Formalism.ConjugateSelfDual.G F Ω, Formalism.ConjugateSelfDual.IsFrob A (Formalism.ConjugateSelfDual.normV v) σ →
    ∀ x : 𝓞 F, x - 1 ∈ v.asIdeal → ∀ w : Ω, w ^ M = algebraMap F Ω (x : F) → σ w = w := by
  first | exact @GlobalTheory.frob_fixes_root_of_one_mod | exact GlobalTheory.frob_fixes_root_of_one_mod | (intros; apply GlobalTheory.frob_fixes_root_of_one_mod <;> assumption)
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.ChevalleyUnitsProof

theorem normFacts (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (b : ℕ)
    (hb : ((b : ℕ) : 𝓞 F) ∉ v.asIdeal) :
    0 < normV v ∧ ((normV v : ℕ) : 𝓞 F) ∈ v.asIdeal ∧ (normV v).Coprime b := by
  classical
  have hN : normV v = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl
  have hne : v.asIdeal ≠ ⊥ := v.ne_bot
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; exact Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hne)
  · rw [hN]; exact Ideal.absNorm_mem _
  · haveI : v.asIdeal.IsMaximal := v.isMaximal
    letI : Field (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.field _
    haveI : Finite (𝓞 F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ hne
    letI : Fintype (𝓞 F ⧸ v.asIdeal) := Fintype.ofFinite _
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 F ⧸ v.asIdeal)
    haveI := hp
    haveI : Fact p.Prime := ⟨CharP.char_is_prime (𝓞 F ⧸ v.asIdeal) p⟩
    obtain ⟨n, hp', hcard⟩ := FiniteField.card (𝓞 F ⧸ v.asIdeal) p
    have hNv : normV v = p ^ (n : ℕ) := by
      unfold normV; rw [Nat.card_eq_fintype_card, hcard]
    apply Nat.coprime_of_dvd
    intro q hq hqN hqb
    rw [hNv] at hqN
    have hqp : q = p := (Nat.prime_dvd_prime_iff_eq hq hp').1 (hq.dvd_of_dvd_pow hqN)
    subst hqp
    apply hb
    obtain ⟨e, rfl⟩ := hqb
    rw [Nat.cast_mul]
    apply Ideal.mul_mem_right
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _

theorem core (E : Type) [Field E] [NumberField E] (l r b : ℕ) (hl : l.Prime) (hb : 0 < b) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ (l ^ r) := by
  classical
  have hm : 0 < l ^ r := pow_pos hl.pos r
  set m := l ^ r with hmdef
  obtain ⟨M, hM0, hmM, hD⟩ := GlobalTheory.T.exists_pow_descent_cyclotomic' E l r hl
  let Ω := AlgebraicClosure E
  haveI : NeZero (M : Ω) := ⟨by exact_mod_cast hM0.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  let K : IntermediateField E Ω := IntermediateField.adjoin E {ζ}
  haveI : FiniteDimensional E K :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  haveI : NumberField K := NumberField.of_module_finite E K
  haveI : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := E) K
  haveI : IsAlgClosure K Ω := ⟨inferInstance, inferInstance⟩
  let ζK : K := ⟨ζ, IntermediateField.mem_adjoin_simple_self E ζ⟩
  have hζK : IsPrimitiveRoot ζK M :=
    (show IsPrimitiveRoot (algebraMap K Ω ζK) M from hζ).of_map_of_injective (algebraMap K Ω).injective
  obtain ⟨L, hLfin, hLgal, hLroots⟩ := GlobalTheory.T.exists_finite_galois_contains_roots_of_units E K Ω M hM0 ⟨ζK, hζK⟩
  let S : Set (HeightOneSpectrum (𝓞 K)) := {v | ((M * b : ℕ) : 𝓞 K) ∈ v.asIdeal}
  have hS : S.Finite := by
    have hne : Ideal.span {((M * b : ℕ) : 𝓞 K)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast (Nat.mul_pos hM0 hb).ne'
    refine (Ideal.finite_factors hne).subset ?_
    intro v hv
    exact Ideal.dvd_span_singleton.2 hv
  have hchoice : ∀ g : L ≃ₐ[K] L, ∃ v : HeightOneSpectrum (𝓞 K), v ∉ S ∧ ∃ B : ValuationSubring Ω,
      IsPlaceOver B v ∧ ∃ σ : G K Ω, IsFrob B (normV v) σ ∧ AlgEquiv.restrictNormalHom L σ = g := by
    intro g
    obtain ⟨v, hv, -, B, hB, -, σ, hσ, hg⟩ := GlobalTheory.Published.chebotarevDegreeOne' K Ω L g S hS
    exact ⟨v, hv, B, hB, σ, hσ, hg⟩
  choose v hvS B hB σ hσ hg using hchoice
  have hvb : ∀ g, ((b : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_left _ _ h)
  have hvM : ∀ g, ((M : ℕ) : 𝓞 K) ∉ (v g).asIdeal := fun g h =>
    hvS g (by simp only [S, Set.mem_setOf_eq, Nat.cast_mul]; exact Ideal.mul_mem_right _ _ h)
  have hnf := fun g => normFacts K (v g) b (hvb g)
  let a : ℕ := ∏ g : L ≃ₐ[K] L, normV (v g)
  refine ⟨a, Finset.prod_pos fun g _ => (hnf g).1, Nat.Coprime.prod_left fun g _ => (hnf g).2.2, ?_⟩
  intro u hu
  obtain ⟨c, hc⟩ := hu
  obtain ⟨w, hw⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω ((u : 𝓞 E) : E)) hM0
  have hwL := hLroots u w hw
  let x : 𝓞 K := ⟨algebraMap E K ((u : 𝓞 E) : E), ((u : 𝓞 E).2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  let c' : 𝓞 K := ⟨algebraMap E K (c : E), (c.2).map (IsScalarTower.toAlgHom ℤ E K)⟩
  have hx1 : ∀ g, x - 1 ∈ (v g).asIdeal := by
    intro g
    have hxc : x - 1 = ((a : ℕ) : 𝓞 K) * c' := by
      apply RingOfIntegers.ext
      change algebraMap E K ((u : 𝓞 E) : E) - 1 = ((a : ℕ) : K) * algebraMap E K ((c : 𝓞 E) : E)
      have h2 := congrArg (fun t : 𝓞 E => algebraMap E K (t : E)) hc
      simpa using h2
    rw [hxc]
    apply Ideal.mul_mem_right
    have hdvd : normV (v g) ∣ a := Finset.dvd_prod_of_mem _ (Finset.mem_univ g)
    obtain ⟨e, he⟩ := hdvd
    rw [he, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (hnf g).2.1
  have hwx : w ^ M = algebraMap K Ω (x : K) := by
    rw [hw]; rfl
  have hfix : ∀ g : L ≃ₐ[K] L, g ⟨w, hwL⟩ = ⟨w, hwL⟩ := by
    intro g
    have h1 := GlobalTheory.T.isFrob_fixes_root_of_one_mod_place K Ω M ζK hζK (v g) (hvM g) (B g) (hB g) (σ g) (hσ g) x (hx1 g) w hwx
    rw [← hg g]
    apply Subtype.ext
    rw [AlgEquiv.restrictNormalHom_apply]
    exact h1
  have hwK : (⟨w, hwL⟩ : L) ∈ (⊥ : IntermediateField K L) := (IsGalois.mem_bot_iff_fixed _).2 hfix
  obtain ⟨k, hk⟩ := IntermediateField.mem_bot.1 hwK
  have hwK' : w ∈ K := by
    have : algebraMap K Ω k = w := congrArg Subtype.val hk
    rw [← this]; exact k.2
  obtain ⟨y, hy⟩ := hD Ω ζ hζ _ w hwK' hw
  have hu0 : ((u : 𝓞 E) : E) ≠ 0 := by
    intro h0
    have : ((u : 𝓞 E)) = 0 := RingOfIntegers.ext (by simpa using h0)
    exact u.ne_zero this
  have hy0 : y ≠ 0 := by
    rintro rfl; exact hu0 (by rw [← hy, zero_pow hm.ne'])
  have hyi : IsIntegral ℤ y := IsIntegral.of_pow hm (by rw [hy]; exact (u : 𝓞 E).2)
  have hyi' : IsIntegral ℤ y⁻¹ := IsIntegral.of_pow hm (by
    rw [inv_pow, hy]
    have : (((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E) : E) = ((u : 𝓞 E) : E)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      have h3 := congrArg (fun t : 𝓞 E => (t : E)) u.inv_mul
      simpa using h3
    rw [← this]; exact ((u⁻¹ : (𝓞 E)ˣ) : 𝓞 E).2)
  refine ⟨⟨⟨y, hyi⟩, ⟨y⁻¹, hyi'⟩, RingOfIntegers.ext (by change y * y⁻¹ = 1; exact mul_inv_cancel₀ hy0), RingOfIntegers.ext (by change y⁻¹ * y = 1; exact inv_mul_cancel₀ hy0)⟩, ?_⟩
  apply Units.ext
  apply RingOfIntegers.ext
  rw [Units.val_pow_eq_pow_val]
  change ((u : 𝓞 E) : E) = y ^ m
  rw [hy]

theorem combine (E : Type) [Field E] [NumberField E] (b m₁ m₂ : ℕ) (hcop : m₁.Coprime m₂)
    (h₁ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₁)
    (h₂ : ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 → ∃ v : (𝓞 E)ˣ, u = v ^ m₂) :
    ∃ a : ℕ, 0 < a ∧ a.Coprime b ∧ ∀ u : (𝓞 E)ˣ, (a : 𝓞 E) ∣ (u : 𝓞 E) - 1 →
      ∃ v : (𝓞 E)ˣ, u = v ^ (m₁ * m₂) := by
  obtain ⟨a₁, ha₁, hc₁, hu₁⟩ := h₁
  obtain ⟨a₂, ha₂, hc₂, hu₂⟩ := h₂
  refine ⟨a₁ * a₂, Nat.mul_pos ha₁ ha₂, Nat.Coprime.mul hc₁ hc₂, ?_⟩
  intro u hu
  have hd₁ : (a₁ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₂ : 𝓞 E), by push_cast; ring⟩ hu
  have hd₂ : (a₂ : 𝓞 E) ∣ (u : 𝓞 E) - 1 := dvd_trans ⟨(a₁ : 𝓞 E), by push_cast; ring⟩ hu
  obtain ⟨v₁, hv₁⟩ := hu₁ u hd₁
  obtain ⟨v₂, hv₂⟩ := hu₂ u hd₂
  set s := Nat.gcdA m₁ m₂
  set t := Nat.gcdB m₁ m₂
  have hg : ((1 : ℕ) : ℤ) = (m₁ : ℤ) * s + (m₂ : ℤ) * t := by
    rw [← hcop.gcd_eq_one]; exact Nat.gcd_eq_gcd_ab m₁ m₂
  have key : u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := by
    rw [← hg]; simp
  have e1 : u ^ ((m₁ : ℤ) * s) = v₂ ^ (s * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₂]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  have e2 : u ^ ((m₂ : ℤ) * t) = v₁ ^ (t * ((m₁ * m₂ : ℕ) : ℤ)) := by
    conv_lhs => rw [hv₁]
    rw [← zpow_natCast, ← zpow_mul]; congr 1; push_cast; ring
  refine ⟨v₂ ^ s * v₁ ^ t, ?_⟩
  calc u = u ^ ((m₁ : ℤ) * s + (m₂ : ℤ) * t) := key
    _ = u ^ ((m₁ : ℤ) * s) * u ^ ((m₂ : ℤ) * t) := zpow_add _ _ _
    _ = (v₂ ^ s * v₁ ^ t) ^ (m₁ * m₂) := by
      rw [e1, e2, zpow_mul, zpow_mul, ← mul_zpow, zpow_natCast]

end GlobalTheory.ChevalleyUnitsProof

theorem GlobalTheory.Published.chevalleyUnits' : GlobalTheory.Published.ChevalleyUnits := by
  intro E _ _ m b hm hb
  induction m using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn => exact GlobalTheory.ChevalleyUnitsProof.core E p n b hp hb
  | zero => exact absurd hm (lt_irrefl 0)
  | one => exact ⟨1, one_pos, Nat.coprime_one_left b, fun u _ => ⟨u, (pow_one u).symm⟩⟩
  | coprime a b' ha hb' hab iha ihb => exact GlobalTheory.ChevalleyUnitsProof.combine E b a b' hab (iha (by omega)) (ihb (by omega))

end
end
