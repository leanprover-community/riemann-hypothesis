import Mathlib
import ReciprocityTheory.Chebotarev.CycStatement
import ReciprocityTheory.Chebotarev.CyclotomicIrreducibleOfForallIsUnramifiedAt
import ReciprocityTheory.Chebotarev.TendstoLogOneDivSubOne

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem cxgal_exists_sf (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] :
    ∃ p : ℚ[X], p ≠ 0 ∧ IsSplittingField ℚ K p := by
  obtain ⟨p, hp⟩ := Normal.exists_isSplittingField ℚ K
  by_cases h0 : p = 0
  · subst h0
    refine ⟨X, X_ne_zero, ?_⟩
    constructor
    · simp
    · have h := hp.adjoin_rootSet
      simp only [rootSet_zero, Algebra.adjoin_empty] at h
      rw [eq_top_iff, ← h]
      exact bot_le
  · exact ⟨p, h0, hp⟩

theorem isGalois_cyclotomicField (K : Type) [Field K] [NumberField K] [IsGalois ℚ K] (l : ℕ) [NeZero l] :
    IsGalois ℚ (CyclotomicField l K) := by
  obtain ⟨p, hp0, hp⟩ := cxgal_exists_sf K
  have : IsSplittingField K (CyclotomicField l K) ((X ^ l - 1 : ℚ[X]).map (algebraMap ℚ K)) := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, Polynomial.map_one]
    exact IsCyclotomicExtension.isSplittingField_X_pow_sub_one l K (CyclotomicField l K)
  have := IsSplittingField.mul (K := K) (L := CyclotomicField l K) p (X ^ l - 1) hp0
    (X_pow_sub_C_ne_zero (NeZero.pos l) 1)
  have : Normal ℚ (CyclotomicField l K) := Normal.of_isSplittingField (p * (X ^ l - 1))
  exact IsGalois.mk

end ReciprocityTheory.Cheb
end

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_lift_pow {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M] (l : ℕ) [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    (hirr : Irreducible (cyclotomic l K)) {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (τ : (ZMod l)ˣ) :
    ∃ g : Gal(M/ℚ), AlgEquiv.restrictNormal g K = σ ∧ g ζ = ζ ^ (τ : ZMod l).val := by
  have hl : 0 < l := (Fact.out : l.Prime).pos
  have : NeZero l := ⟨hl.ne'⟩
  obtain ⟨g₀, hg₀⟩ := AlgEquiv.restrictNormalHom_surjective (F := ℚ) (K₁ := K) M σ
  have hg₀ζ : IsPrimitiveRoot (g₀ ζ) l := hζ.map_of_injective g₀.injective
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hg₀ζ.pow_eq_one
  have hcop : i.Coprime l := (hζ.pow_iff_coprime hl i).mp (hi ▸ hg₀ζ)
  set u : (ZMod l)ˣ := ZMod.unitOfCoprime i hcop with hu
  set t : (ZMod l)ˣ := τ * u⁻¹ with ht
  set h : M ≃ₐ[K] M := (IsCyclotomicExtension.autEquivPow M hirr).symm t with hh
  have hz := IsCyclotomicExtension.zeta_spec l K M
  have hhz : h (IsCyclotomicExtension.zeta l K M) = (IsCyclotomicExtension.zeta l K M) ^ (t : ZMod l).val := by
    have h1 := hz.autToPow_spec K h
    have h2 : hz.autToPow K h = t := by
      have := (IsCyclotomicExtension.autEquivPow M hirr).apply_symm_apply t
      exact this
    rw [← h1, h2]
  obtain ⟨a, -, ha⟩ := hz.eq_pow_of_pow_eq_one hζ.pow_eq_one
  have hhζ : h ζ = ζ ^ (t : ZMod l).val := by
    rw [← ha, map_pow, hhz, ← pow_mul, ← pow_mul, mul_comm]
  refine ⟨h.restrictScalars ℚ * g₀, ?_, ?_⟩
  · have h1 : AlgEquiv.restrictNormal (h.restrictScalars ℚ) K = 1 := by
      ext x
      have e := AlgEquiv.restrictNormal_commutes (h.restrictScalars ℚ : M ≃ₐ[ℚ] M) K x
      have e2 : (h.restrictScalars ℚ) (algebraMap K M x) = algebraMap K M x := h.commutes x
      rw [e2] at e
      exact (algebraMap K M).injective e
    have h2 : AlgEquiv.restrictNormal (h.restrictScalars ℚ * g₀) K =
        AlgEquiv.restrictNormal (h.restrictScalars ℚ) K * AlgEquiv.restrictNormal g₀ K :=
      map_mul (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := M) K) _ _
    rw [h2, h1, one_mul]
    exact hg₀
  · show h (g₀ ζ) = _
    rw [← hi, map_pow, hhζ, ← pow_mul]
    rw [← pow_mod_orderOf, ← hζ.eq_orderOf, ← pow_mod_orderOf ζ (τ : ZMod l).val, ← hζ.eq_orderOf]
    congr 1
    rw [← ZMod.natCast_eq_natCast_iff']
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    have : ((u : (ZMod l)ˣ) : ZMod l) = (i : ZMod l) := rfl
    rw [← this]
    rw [← Units.val_mul, ht, inv_mul_cancel_right]

end ReciprocityTheory.Cheb
end

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois ℚ K] [IsGalois ℚ M]

theorem eq_one_of_restrict_eq_one {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (h : Gal(M/ℚ)) (hK : AlgEquiv.restrictNormal h K = 1) (h1 : h ζ = ζ) : h = 1 := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := K) hζ
  refine AlgEquiv.ext fun x => ?_
  rw [AlgEquiv.one_apply]
  have hx : x ∈ Algebra.adjoin K ({ζ} : Set M) := htop ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h1
  | algebraMap r =>
    have := AlgEquiv.restrictNormal_commutes h K r
    rw [hK, AlgEquiv.one_apply] at this
    exact this.symm
  | add y z _ _ hy hz => rw [map_add, hy, hz]
  | mul y z _ _ hy hz => rw [map_mul, hy, hz]

theorem pow_apply_zeta_of_apply_eq_pow {ζ : M} (g : Gal(M/ℚ)) (t : ℕ) (hg : g ζ = ζ ^ t) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (t ^ m) := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, hg, map_pow, ih, ← pow_mul, ← pow_succ]

theorem zeta_pow_eq_pow_iff_natCast {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (a b : ℕ) :
    ζ ^ a = ζ ^ b ↔ (a : ZMod l) = b := by
  have hfin : IsOfFinOrder ζ := isOfFinOrder_iff_pow_eq_one.2 ⟨l, NeZero.pos l, hζ.pow_eq_one⟩
  rw [ZMod.natCast_eq_natCast_iff, hζ.eq_orderOf]
  exact hfin.pow_eq_pow_iff_modEq

theorem pow_apply_zeta_eq_units_pow {l : ℕ} [NeZero l] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (τ : (ZMod l)ˣ)
    (g : Gal(M/ℚ)) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) (m : ℕ) :
    (g ^ m) ζ = ζ ^ (((τ ^ m : (ZMod l)ˣ) : ZMod l).val) := by
  rw [pow_apply_zeta_of_apply_eq_pow g _ hgζ m, zeta_pow_eq_pow_iff_natCast hζ]
  simp

theorem restrictNormal_pow_of_gal (g : Gal(M/ℚ)) (m : ℕ) :
    AlgEquiv.restrictNormal (g ^ m) K = (AlgEquiv.restrictNormal g K) ^ m :=
  map_pow (AlgEquiv.restrictNormalHom K) g m

theorem eq_of_apply_eq_pow {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val)
    (φ : M ≃ₐ[IntermediateField.fixedField (Subgroup.zpowers g)] M) (n : ℕ) (hφ : φ ζ = ζ ^ n) (hn : (n : ZMod l) = τ) :
    φ.restrictScalars ℚ = g := by
  have hl : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  have hmem' : φ.restrictScalars ℚ ∈
      IntermediateField.fixingSubgroup (IntermediateField.fixedField (Subgroup.zpowers g)) := by
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    exact φ.commutes ⟨x, hx⟩
  have hmem : φ.restrictScalars ℚ ∈ Subgroup.zpowers g := by
    rwa [IntermediateField.fixingSubgroup_fixedField] at hmem'
  obtain ⟨k, hk : g ^ k = _⟩ := mem_powers_iff_mem_zpowers.mpr hmem
  have hpos := orderOf_pos g
  set m := k + orderOf g - 1 with hm
  have hkm : g ^ (m + 1) = g ^ k := by
    rw [show m + 1 = k + orderOf g by omega, pow_add, pow_orderOf_eq_one, mul_one]
  have hφ' : (g ^ (m + 1)) ζ = ζ ^ n := by rw [hkm, hk]; exact hφ
  rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, zeta_pow_eq_pow_iff_natCast hζ, ZMod.natCast_zmod_val, hn] at hφ'
  have hτm : τ ^ m = 1 := by
    have h2 : τ ^ (m + 1) = τ := Units.ext hφ'
    rw [pow_succ] at h2
    exact mul_eq_right.mp h2
  have hdiv : l - 1 ∣ m := hτ ▸ orderOf_dvd_of_pow_eq_one hτm
  have hσm : σ ^ m = 1 := orderOf_dvd_iff_pow_eq_one.mp (hσ.trans hdiv)
  have hgm : g ^ m = 1 := by
    refine eq_one_of_restrict_eq_one (K := K) hζ (g ^ m) ?_ ?_
    · rw [restrictNormal_pow_of_gal, hg, hσm]
    · rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hτm, Units.val_one, ZMod.val_one_eq_one_mod,
        Nat.mod_eq_of_lt (Fact.out : l.Prime).one_lt, pow_one]
  rw [← hk, ← hkm, pow_succ, hgm, one_mul]

theorem irreducible_cyclotomic_fixedField {l : ℕ} [Fact l.Prime] [IsCyclotomicExtension {l} K M]
    {ζ : M} (hζ : IsPrimitiveRoot ζ l) (σ : Gal(K/ℚ)) (hσ : orderOf σ ∣ l - 1) (τ : (ZMod l)ˣ) (hτ : orderOf τ = l - 1)
    (g : Gal(M/ℚ)) (hg : AlgEquiv.restrictNormal g K = σ) (hgζ : g ζ = ζ ^ (τ : ZMod l).val) :
    Irreducible (cyclotomic l (IntermediateField.fixedField (Subgroup.zpowers g))) := by
  have hlp := (Fact.out : l.Prime)
  have hl : NeZero l := ⟨hlp.ne_zero⟩
  set E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hint : IsIntegral E ζ := Algebra.IsIntegral.isIntegral ζ
  set p := minpoly E ζ with hp
  have hcard : Fintype.card (ZMod l)ˣ = l - 1 := by
    rw [ZMod.card_units_eq_totient, Nat.totient_prime hlp]

  have htop : Subgroup.zpowers τ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hτ, Nat.card_eq_fintype_card, hcard]

  have hroot : ∀ u : (ZMod l)ˣ, aeval (ζ ^ (u : ZMod l).val) p = 0 := by
    intro u
    have hu : u ∈ Subgroup.zpowers τ := htop ▸ Subgroup.mem_top u
    obtain ⟨k, hk : τ ^ k = u⟩ := mem_powers_iff_mem_zpowers.mpr hu
    have hgk : g ^ k ∈ IntermediateField.fixingSubgroup E := by
      rw [IntermediateField.fixingSubgroup_fixedField]
      exact Subgroup.npow_mem_zpowers g k
    set ψ := IntermediateField.fixingSubgroupEquiv E ⟨g ^ k, hgk⟩
    have hψ : ψ ζ = ζ ^ (u : ZMod l).val := by
      change (g ^ k) ζ = _
      rw [pow_apply_zeta_eq_units_pow hζ τ g hgζ, hk]
    rw [← hψ, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hp, minpoly.aeval, map_zero]
  have hdvd : p ∣ cyclotomic l E := by
    apply minpoly.dvd
    rw [← Polynomial.eval_map_algebraMap, Polynomial.map_cyclotomic]
    exact (hζ.isRoot_cyclotomic (NeZero.pos l))
  have hp0 : p.map (algebraMap E M) ≠ 0 := Polynomial.map_ne_zero (minpoly.ne_zero hint)
  classical
  let Z : Finset M := Finset.univ.image (fun u : (ZMod l)ˣ => ζ ^ (u : ZMod l).val)
  have hZcard : Z.card = l - 1 := by
    rw [Finset.card_image_of_injective _ ?_, Finset.card_univ, hcard]
    intro u v huv
    have := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) huv
    exact Units.ext (ZMod.val_injective l this)
  have hZ : Z.val ⊆ (p.map (algebraMap E M)).roots := by
    intro z hz
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp hz
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact hroot u
  have hdeg := Polynomial.card_le_degree_of_subset_roots hZ
  rw [hZcard, Polynomial.natDegree_map] at hdeg
  have heq : cyclotomic l E = p := by
    refine Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint)
      (Polynomial.cyclotomic.monic l E) hdvd ?_
    rw [Polynomial.natDegree_cyclotomic, Nat.totient_prime hlp]
    exact hdeg
  rw [heq]
  exact minpoly.irreducible hint

end ReciprocityTheory.Cheb
end

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_frob_above {M : Type} [Field M] [NumberField M] (E : IntermediateField ℚ M) [IsGalois E M]
    (l : ℕ) [Fact l.Prime] {ζ : M} (hζ : IsPrimitiveRoot ζ l) (q : Ideal (𝓞 E)) (hq : q.IsPrime)
    (hqp : (Ideal.absNorm q).Prime) (hql : Ideal.absNorm q ≠ l) :
    ∃ (P : Ideal (𝓞 M)) (_ : P.IsPrime) (φ : M ≃ₐ[E] M),
      P.LiesOver (Ideal.span {((Ideal.absNorm q : ℕ) : ℤ)}) ∧ φ ζ = ζ ^ Ideal.absNorm q ∧
      IsArithFrobAt ℤ (φ.restrictScalars ℚ) P := by
  set p := Ideal.absNorm q with hpdef
  have hq0 : q ≠ ⊥ := by
    intro h
    rw [h, Ideal.absNorm_bot] at hpdef
    exact Nat.not_prime_zero (hpdef ▸ hqp)
  have hqmax : q.IsMaximal := hq.isMaximal hq0
  obtain ⟨P, hPmax, hPq⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 M) q
  have hPunder : P.under (𝓞 E) = q := hPq.over.symm
  have hP0 : P ≠ ⊥ := by
    intro h
    apply hq0
    rw [← hPunder, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hPfin : Finite (𝓞 M ⧸ P) :=
    (Ideal.absNorm_ne_zero_iff P).mp (fun h => hP0 (Ideal.absNorm_eq_zero_iff.mp h))
  obtain ⟨σ, hσ⟩ := IsArithFrobAt.exists_of_isInvariant (𝓞 E) (M ≃ₐ[E] M) P

  have hqZ : q.under ℤ = Ideal.span {(p : ℤ)} := by
    have hpr : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hqp).irreducible
    have hle : Ideal.span {(p : ℤ)} ≤ q.under ℤ := by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under_def, Ideal.mem_comap]
      have := Ideal.absNorm_mem q
      rw [← hpdef] at this
      simpa using this
    exact (hpr.eq_of_le (Ideal.IsPrime.under ℤ q).ne_top hle).symm
  have hPZ : P.under ℤ = Ideal.span {(p : ℤ)} := by
    rw [← Ideal.under_under (B := 𝓞 E), hPunder, hqZ]
  have hcardZ : Nat.card (ℤ ⧸ P.under ℤ) = p := by
    rw [hPZ, Nat.card_congr (Int.quotientSpanNatEquivZMod p).toEquiv, Nat.card_zmod]
  have hcardE : Nat.card (𝓞 E ⧸ P.under (𝓞 E)) = p := by
    rw [hPunder, hpdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hfrob : IsArithFrobAt ℤ (σ.restrictScalars ℚ) P := by
    intro x
    have := hσ x
    rw [hcardE] at this
    show (σ.restrictScalars ℚ) • x - x ^ Nat.card (ℤ ⧸ P.under ℤ) ∈ P
    rw [hcardZ]
    exact this
  refine ⟨P, hPmax.isPrime, σ, ⟨hPZ.symm⟩, ?_, hfrob⟩

  have hint : IsIntegral ℤ ζ := hζ.isIntegral (Nat.Prime.pos Fact.out)
  let z : 𝓞 M := ⟨ζ, hint⟩
  have hz : z ^ l = 1 := by
    apply RingOfIntegers.ext
    rw [RingOfIntegers.coe_eq_algebraMap, RingOfIntegers.coe_eq_algebraMap, map_one]
    exact (map_pow (algebraMap (𝓞 M) M) z l).trans hζ.pow_eq_one
  have hl : ((l : ℕ) : 𝓞 M) ∉ P := by
    intro h
    have h' : ((l : ℕ) : ℤ) ∈ P.under ℤ := by
      rw [Ideal.mem_comap]; simpa using h
    rw [hPZ, Ideal.mem_span_singleton] at h'
    have hdvd : p ∣ l := by exact_mod_cast h'
    exact hql ((Nat.prime_dvd_prime_iff_eq hqp Fact.out).mp hdvd)
  have key := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hfrob hz hl
  rw [hcardZ] at key
  calc σ ζ = (((σ.restrictScalars ℚ) • z : 𝓞 M) : M) := rfl
    _ = ((z ^ p : 𝓞 M) : M) := congrArg (fun y : 𝓞 M => (y : M)) key
    _ = ζ ^ p := by
      rw [RingOfIntegers.coe_eq_algebraMap]
      exact (map_pow (algebraMap (𝓞 M) M) z p).trans rfl

end ReciprocityTheory.Cheb
end

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem isArithFrobAt_restrictNormal {K M : Type} [Field K] [NumberField K] [IsGalois ℚ K] [Field M] [NumberField M]
    [Algebra K M] (g : Gal(M/ℚ)) (p : ℕ) (P : Ideal (𝓞 M)) (hP : P.IsPrime)
    (hPp : P.LiesOver (Ideal.span {(p : ℤ)})) (h : IsArithFrobAt ℤ g P) :
    (P.under (𝓞 K)).IsPrime ∧ (P.under (𝓞 K)).LiesOver (Ideal.span {(p : ℤ)}) ∧
      IsArithFrobAt ℤ (AlgEquiv.restrictNormal g K) (P.under (𝓞 K)) := by
  refine ⟨Ideal.IsPrime.under _ _, ⟨by rw [Ideal.under_under]; exact hPp.over⟩, ?_⟩
  intro y
  have hu : (P.under (𝓞 K)).under ℤ = P.under ℤ := Ideal.under_under P
  have hc : algebraMap (𝓞 K) (𝓞 M) ((AlgEquiv.restrictNormal g K) • y) =
      g • algebraMap (𝓞 K) (𝓞 M) y := by
    apply NumberField.RingOfIntegers.ext
    exact AlgEquiv.restrictNormal_commutes g K (y : K)
  show _ ∈ Ideal.comap _ P
  rw [Ideal.mem_comap]
  simp only [MulSemiringAction.toAlgHom_apply, hu, map_sub, map_pow, hc]
  simpa using h (algebraMap (𝓞 K) (𝓞 M) y)

end ReciprocityTheory.Cheb
end

section
open NumberField Polynomial

namespace ReciprocityTheory.Cheb

theorem exists_unit_orderOf_eq (l : ℕ) [Fact l.Prime] : ∃ τ : (ZMod l)ˣ, orderOf τ = l - 1 := by
  obtain ⟨τ, hτ⟩ := IsCyclic.exists_generator (α := (ZMod l)ˣ)
  refine ⟨τ, ?_⟩
  rw [orderOf_eq_card_of_forall_mem_zpowers hτ, Nat.card_eq_fintype_card, ZMod.card_units]

theorem cross : CycStatement → Statement := by
  intro hB K _ _ _ σ T
  obtain ⟨N, hN⟩ := exists_forall_isUnramifiedAt_of_liesOver K
  obtain ⟨N', hN'⟩ := exists_forall_cyclotomic_irreducible K
  have hk : orderOf σ ≠ 0 := (orderOf_pos σ).ne'
  obtain ⟨l, hlp, hlgt, hlmod⟩ := Nat.exists_prime_gt_modEq_one (max N' (T.sup id)) hk
  have : Fact l.Prime := ⟨hlp⟩
  have hσ : orderOf σ ∣ l - 1 := (Nat.modEq_iff_dvd' hlp.one_lt.le).mp hlmod.symm
  have hirr : Irreducible (cyclotomic l K) := hN' l hlp (lt_of_le_of_lt (le_max_left _ _) hlgt)
  have : NeZero l := ⟨hlp.ne_zero⟩
  have := isGalois_cyclotomicField K l
  let M := CyclotomicField l K
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta l K M) l := IsCyclotomicExtension.zeta_spec l K M
  obtain ⟨τ, hτ⟩ := exists_unit_orderOf_eq l
  obtain ⟨g, hg, hgζ⟩ := exists_lift_pow (M := M) l hirr hζ σ τ
  let E := IntermediateField.fixedField (Subgroup.zpowers g)
  have hirrE : Irreducible (cyclotomic l E) := irreducible_cyclotomic_fixedField hζ σ hσ τ hτ g hg hgζ
  obtain ⟨q, hq, hqp, hqT, hqmod⟩ := hB E l hirrE τ (T ∪ Finset.range (N + 1) ∪ {l})
  have hql : Ideal.absNorm q ≠ l := fun h => hqT (by simp [h])
  obtain ⟨P, hP, φ, hPp, hφζ, hφ⟩ := exists_frob_above E l hζ q hq hqp hql
  have hφg : φ.restrictScalars ℚ = g := eq_of_apply_eq_pow hζ σ hσ τ hτ g hg hgζ φ _ hφζ hqmod
  rw [hφg] at hφ
  obtain ⟨hQ, hQp, hQf⟩ := isArithFrobAt_restrictNormal (K := K) g _ P hP hPp hφ
  rw [hg] at hQf
  refine ⟨Ideal.absNorm q, hqp, fun h => hqT (by simp [h]), P.under (𝓞 K), hQ, hQp, ?_, hQf⟩
  have := hQ
  have := hQp
  refine hN _ hqp ?_ _
  by_contra h
  exact hqT (by simp; omega)

end ReciprocityTheory.Cheb
end

section
namespace ReciprocityTheory.Cheb

theorem statement_holds : Statement := cross cyc_holds

end ReciprocityTheory.Cheb
end
