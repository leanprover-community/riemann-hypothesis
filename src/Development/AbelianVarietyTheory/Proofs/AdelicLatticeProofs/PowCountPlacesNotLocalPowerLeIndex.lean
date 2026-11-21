import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.UnitsMappingToPowersLeUnitsLocalKummerNorms
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsForallAbvSubLt
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsIsKum
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HerbrandPrimeOrderStatement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CyclicKummerNormFixedHilbert90Statement
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PIdxUnitsFiniteExtensionAdicCompletionStatement

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem pow_card_le_index_iInf_of_prime :
    ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime →
      (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) →
      (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  intro p G ι _ _ K hp hpow hx hind
  classical
  choose x hx1 hx2 using hx
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (G ⧸ (⨅ i, K i)) := Nat.finite_of_card_ne_zero hind
  have hord : ∀ j, orderOf (QuotientGroup.mk' (K j) (x j)) = p := by
    intro j
    apply orderOf_eq_prime
    · rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hpow j _
    · rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
      exact hx1 j
  have hprod : ∀ (n : ι → Fin p) (j : ι),
      QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ)) = (QuotientGroup.mk' (K j) (x j)) ^ (n j : ℕ) := by
    intro n j
    rw [map_prod, Finset.prod_eq_single j]
    · rw [map_pow]
    · intro i _ hij
      rw [map_pow]
      have : QuotientGroup.mk' (K j) (x i) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hx2 i j (Ne.symm hij)
      rw [this, one_pow]
    · intro h
      exact absurd (Finset.mem_univ j) h
  let f : (ι → Fin p) → G ⧸ (⨅ i, K i) := fun n => QuotientGroup.mk (∏ i, x i ^ (n i : ℕ))
  have hf : Function.Injective f := by
    intro n m h
    have h1 := QuotientGroup.eq.1 h
    funext j
    have h2 := Subgroup.mem_iInf.1 h1 j
    have h3 : QuotientGroup.mk' (K j) (∏ i, x i ^ (n i : ℕ))
        = QuotientGroup.mk' (K j) (∏ i, x i ^ (m i : ℕ)) := QuotientGroup.eq.2 h2
    rw [hprod, hprod] at h3
    apply Fin.ext
    refine pow_injOn_Iio_orderOf ?_ ?_ h3
    · rw [hord]; exact (n j).2
    · rw [hord]; exact (m j).2
  have := Nat.card_le_card_of_injective f hf
  simpa [Subgroup.index] using this

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_card_le_index_iInf_of_prime' : ∀ (p : ℕ) (G ι : Type) [CommGroup G] [Fintype ι] (K : ι → Subgroup G), p.Prime → (∀ (i : ι) (x : G), x ^ p ∈ K i) → (∀ i, ∃ x, x ∉ K i ∧ ∀ j, j ≠ i → x ∈ K j) → (⨅ i, K i).index ≠ 0 → p ^ Fintype.card ι ≤ (⨅ i, K i).index := by
  atlas_forward_decl GlobalTheory.CNorm.pow_card_le_index_iInf_of_prime
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mul_pow_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {p : ℕ} (hp : 0 < p) {y : K} (hy : y ≠ 0) :
    {a : K | a ≠ 0 ∧ ∃ r : K, a = y * r ^ p} ∈ nhds y := by
  have hd : HasStrictDerivAt (fun r : K => y * r ^ p) (y * ((p : K) * 1 ^ (p - 1))) 1 :=
    (hasStrictDerivAt_pow p (1 : K)).const_mul y
  have hne : y * ((p : K) * 1 ^ (p - 1)) ≠ 0 := by
    have : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    simp [hy, this]
  have h := hd.map_nhds_eq hne
  simp only [one_pow, mul_one] at h
  refine Filter.inter_mem (isOpen_ne.mem_nhds hy) ?_
  rw [← h]
  exact Filter.mem_map.2 (Filter.Eventually.of_forall fun r => ⟨r, rfl⟩)

theorem exists_approx_mod_powers :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  intro p F _ _ S y hp hy
  let U : Set (((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    ⋂ v : S, {q | q.1 v ≠ 0 ∧ ∃ r : v.1.adicCompletion F, q.1 v = y v.1 * r ^ p}
  have hU : U ∈ nhds ((fun v : S => y v.1), (0 : (F →+* ℝ) → ℝ)) := by
    refine Filter.iInter_mem.2 fun v => ?_
    have hc : Continuous fun q : ((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ) => q.1 v :=
      (continuous_apply v).comp continuous_fst
    have : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    letI : NontriviallyNormedField (v.1.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.1.adicCompletion F) ℤᵐ⁰
    exact hc.continuousAt.preimage_mem_nhds
      (mul_pow_mem_nhds (K := v.1.adicCompletion F) hp (hy v.1))
  obtain ⟨x, hx⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real F S).mem_nhds hU
  have h1 : ∀ v : S, algebraMap F (v.1.adicCompletion F) x ≠ 0 ∧
      ∃ r : v.1.adicCompletion F, algebraMap F (v.1.adicCompletion F) x = y v.1 * r ^ p :=
    fun v => Set.mem_iInter.1 hx v
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨1, one_ne_zero, fun v hv => absurd (map_zero _) (h1 ⟨v, hv⟩).1⟩
  · exact ⟨x, hx0, fun v hv => (h1 ⟨v, hv⟩).2⟩

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_mod_powers' : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  atlas_forward_decl GlobalTheory.CNorm.exists_approx_mod_powers
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem nonnorm_pIdx_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pIdx p (U.map f) = pIdx p U := by
  have h : pows p (U.map f) = (pows p U).map f := by
    unfold pows
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp
  unfold pIdx
  rw [h, Subgroup.relIndex_map_map_of_injective _ _ hf]

theorem nonnorm_pTor_map (p : ℕ) {G H : Type} [CommGroup G] [CommGroup H] (f : G →* H)
    (hf : Function.Injective f) (U : Subgroup G) : pTor p (U.map f) = pTor p U := by
  unfold pTor
  symm
  refine Nat.card_eq_of_bijective
    (fun x => ⟨f x.1, Subgroup.mem_map_of_mem f x.2.1, by rw [← map_pow, x.2.2, map_one]⟩) ⟨?_, ?_⟩
  · intro x y hxy
    exact Subtype.ext (hf (congrArg Subtype.val hxy))
  · rintro ⟨_, ⟨x, hx, rfl⟩, h⟩
    refine ⟨⟨x, hx, hf ?_⟩, rfl⟩
    rw [map_pow, h, map_one]

theorem exists_local_nonnorm : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F)
    (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p →
    (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) →
    ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F))
      (algebraMap F (v.adicCompletion F) δ) := by
  intro p F _ _ ζ δ v hp hζ hδ
  by_contra hall
  push_neg at hall
  haveI : CharZero (v.adicCompletion F) :=
    charZero_of_injective_algebraMap (algebraMap F (v.adicCompletion F)).injective
  have hζ' : IsPrimitiveRoot (algebraMap F (v.adicCompletion F) ζ) p :=
    hζ.map_of_injective (algebraMap F (v.adicCompletion F)).injective
  obtain ⟨L, _, _, θ, σ, hK⟩ := exists_isKum p (v.adicCompletion F) _ _ hp hζ' hδ
  obtain ⟨hfd, hrk, hσp, hfix, -, -, hnorm⟩ := GlobalTheory.T.cyclic_hilbert90_kummer_and_mem_kNorm_iff p _ L _ _ θ σ hK
  obtain ⟨e, he⟩ : ∃ e : ℕ, v.valuation F (p : F) = WithZero.exp (-(e : ℤ)) := by
    have h0 : v.valuation F (p : F) ≠ 0 := by
      rw [Valuation.ne_zero_iff]
      exact_mod_cast hp.ne_zero
    have h1 : v.valuation F (p : F) ≤ 1 := by
      have := v.valuation_le_one (K := F) (p : 𝓞 F)
      simpa using this
    have h2 : WithZero.log (v.valuation F (p : F)) ≤ 0 := by
      rw [← WithZero.exp_log h0, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
      exact h1
    refine ⟨(-WithZero.log (v.valuation F (p : F))).toNat, ?_⟩
    rw [Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log h0]
  obtain ⟨htL, hiL⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e L hp.pos he
  obtain ⟨htK, hiK⟩ := GlobalTheory.T.pIdx_units_finite_extension_adicCompletion' p F v e (v.adicCompletion F) hp.pos he
  rw [hrk] at hiL
  rw [Module.finrank_self, pow_one] at hiK
  have hQ : Ideal.absNorm v.asIdeal ^ e ≠ 0 :=
    pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  generalize Ideal.absNorm v.asIdeal ^ e = Q at hiL hiK hQ
  let s : Lˣ →* Lˣ := Units.map (σ : L →* L)
  have hs : ∀ (n : ℕ) (a : Lˣ), ((s^[n] a : Lˣ) : L) = σ^[n] (a : L) := by
    intro n
    induction n with
    | zero => intro a; rfl
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  let f : (v.adicCompletion F)ˣ →* Lˣ :=
    Units.map (algebraMap (v.adicCompletion F) L : v.adicCompletion F →* L)
  have hf : Function.Injective f :=
    Units.map_injective (algebraMap (v.adicCompletion F) L).injective
  have hfx : fix s = (⊤ : Subgroup (v.adicCompletion F)ˣ).map f := by
    ext a
    rw [mem_fix]
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := hfix a (congrArg Units.val ha)
      have hb0 : b ≠ 0 := by
        rintro rfl
        exact a.ne_zero (by rw [hb, map_zero])
      exact ⟨Units.mk0 b hb0, trivial, Units.ext hb.symm⟩
    · rintro ⟨b, -, rfl⟩
      exact Units.ext (σ.commutes (b : v.adicCompletion F))
  have hiL0 : pIdx p (⊤ : Subgroup Lˣ) ≠ 0 := by
    rw [hiL]
    exact mul_ne_zero (mul_ne_zero hp.ne_zero (pow_ne_zero _ hQ)) htL
  obtain ⟨-, h1, -, -, hH⟩ := GlobalTheory.T.herbrand_prime_order' p Lˣ s hp
    (fun a => Units.ext (by rw [hs, hσp])) hiL0 htL
  have h0 : (nrm s p).range.relIndex (fix s) = 1 := by
    rw [Subgroup.relIndex_eq_one, hfx]
    rintro _ ⟨c, -, rfl⟩
    obtain ⟨y, hy⟩ := (hnorm c).1 (hall c)
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ∏ i ∈ Finset.range p, σ^[i] (0 : L) = 0 :=
        Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) rfl
      rw [this] at hy
      exact c.ne_zero ((map_eq_zero _).1 hy.symm)
    refine ⟨Units.mk0 y hy0, Units.ext ?_⟩
    rw [nrm_apply, Units.coe_prod]
    simp only [hs, Units.val_mk0]
    exact hy
  rw [h0, hfx, nonnorm_pIdx_map p f hf, nonnorm_pTor_map p f hf, hiL, hiK, one_pow] at hH
  generalize pTor p (⊤ : Subgroup Lˣ) = tL at hH htL
  generalize pTor p (⊤ : Subgroup (v.adicCompletion F)ˣ) = tK at hH htK
  generalize (dif s).range.relIndex (nrm s p).ker = h at hH h1
  have hc : Q ^ p * tL * tK ^ p ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero _ hQ) htL) (pow_ne_zero _ htK)
  have key : p = h ^ (p - 1) * p ^ p := by
    apply mul_right_cancel₀ hc
    rw [mul_pow, mul_pow] at hH
    linear_combination hH
  have hle : p ^ p ≤ p := by
    calc p ^ p ≤ h ^ (p - 1) * p ^ p := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (pow_ne_zero _ h1))
      _ = p := key.symm
  have hlt : p ^ 1 < p ^ p := Nat.pow_lt_pow_right hp.one_lt hp.one_lt
  rw [pow_one] at hlt
  omega

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (ζ δ : F) (v : HeightOneSpectrum (𝓞 F)), p.Prime → IsPrimitiveRoot ζ p → (∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ) → ∃ c : (v.adicCompletion F)ˣ, c ∉ kNorm p (RingHom.id (v.adicCompletion F)) (algebraMap F (v.adicCompletion F) δ) := by
  atlas_forward_decl GlobalTheory.CNorm.exists_local_nonnorm
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

open NumberField IsDedekindDomain in
private theorem exists_valuation_natCast_eq_exp_neg_and_dvd {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {p : ℕ} (hp : 0 < p) :
    ∃ e : ℕ, HeightOneSpectrum.valuation F v (p : F) = WithZero.exp (-(e : ℤ)) ∧
      v.asIdeal ^ e ∣ Ideal.span {(p : 𝓞 F)} := by
  have hval : HeightOneSpectrum.valuation F v (p : F) = v.intValuation (p : 𝓞 F) := by
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := F)]
    simp
  have hne : v.intValuation (p : 𝓞 F) ≠ 0 :=
    v.intValuation_ne_zero _ (by exact_mod_cast hp.ne')
  have hle : v.intValuation (p : 𝓞 F) ≤ 1 := v.intValuation_le_one _
  set a := v.intValuation (p : 𝓞 F) with ha
  have hlog : WithZero.log a ≤ 0 := by
    rw [← WithZero.exp_le_exp, WithZero.exp_log hne, WithZero.exp_zero]
    exact hle
  refine ⟨(-WithZero.log a).toNat, ?_, ?_⟩
  · rw [hval, Int.toNat_of_nonneg (by omega), neg_neg, WithZero.exp_log hne]
  · rw [← HeightOneSpectrum.intValuation_le_pow_iff_dvd, Int.toNat_of_nonneg (by omega), neg_neg,
      WithZero.exp_log hne]

open NumberField IsDedekindDomain in
private theorem powSub_eq_comap_pows_units_map {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) :
    _root_.GlobalTheory.CNorm.powSub p φ =
      (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).comap (Units.map φ.toMonoidHom) := by
  ext x
  rw [_root_.GlobalTheory.CNorm.mem_powSub, Subgroup.mem_comap]
  unfold _root_.GlobalTheory.CNorm.pows
  simp only [Subgroup.mem_map, Subgroup.mem_top, true_and, powMonoidHom_apply]
  constructor
  · rintro ⟨r, hr⟩
    have hr0 : r ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne'] at hr
      exact (map_ne_zero φ).2 x.ne_zero hr.symm
    exact ⟨Units.mk0 r hr0, Units.ext (by simpa using hr)⟩
  · rintro ⟨y, hy⟩
    refine ⟨(y : L), ?_⟩
    have := congrArg Units.val hy
    simpa using this

open NumberField IsDedekindDomain in
private theorem powSub_index_ne_zero_and_le_pIdx {F L : Type} [Field F] [Field L] {p : ℕ} (hp : 0 < p)
    (φ : F →+* L) (h : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) ≠ 0) :
    (_root_.GlobalTheory.CNorm.powSub p φ).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.powSub p φ).index ≤ _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) := by
  have hdef : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup Lˣ) = (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ)).index := by
    unfold _root_.GlobalTheory.CNorm.pIdx
    exact Subgroup.relIndex_top_right _
  rw [hdef] at h ⊢
  rw [powSub_eq_comap_pows_units_map hp, Subgroup.index_comap]
  have hd := Subgroup.relIndex_dvd_index_of_normal (_root_.GlobalTheory.CNorm.pows p (⊤ : Subgroup Lˣ))
    (Units.map φ.toMonoidHom).range
  exact ⟨ne_zero_of_dvd_ne_zero h hd, Nat.le_of_dvd (Nat.pos_of_ne_zero h) hd⟩

open NumberField IsDedekindDomain in
private theorem pTor_units_le {L : Type} [Field L] {p : ℕ} (hp : 0 < p) :
    _root_.GlobalTheory.CNorm.pTor p (⊤ : Subgroup Lˣ) ≤ p := by
  unfold _root_.GlobalTheory.CNorm.pTor
  classical
  have hinj : Function.Injective (fun x : {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1} =>
      (⟨(x.1 : L), by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots hp, ← Units.val_pow_eq_pow_val, x.2.2,
          Units.val_one]⟩ : (Polynomial.nthRoots p (1 : L)).toFinset)) := by
    intro x y hxy
    exact Subtype.ext (Units.ext (congrArg Subtype.val hxy))
  calc Nat.card {x : Lˣ // x ∈ (⊤ : Subgroup Lˣ) ∧ x ^ p = 1}
      ≤ Nat.card (Polynomial.nthRoots p (1 : L)).toFinset := Nat.card_le_card_of_injective _ hinj
    _ = (Polynomial.nthRoots p (1 : L)).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ (Polynomial.nthRoots p (1 : L)).card := Multiset.toFinset_card_le _
    _ ≤ p := Polynomial.card_nthRoots p 1

open NumberField IsDedekindDomain in
private theorem prod_absNorm_pow_le_pow_finrank {F : Type} [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) {p : ℕ} (hp : 0 < p) (e : HeightOneSpectrum (𝓞 F) → ℕ)
    (he : ∀ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)}) :
    ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v ≤ p ^ Module.finrank ℚ F := by
  have hdvd : ∏ v ∈ S, v.asIdeal ^ e v ∣ Ideal.span {(p : 𝓞 F)} := by
    refine Finset.prod_dvd_of_coprime ?_ he
    intro v _ w _ hvw
    have hne : v.asIdeal ≠ w.asIdeal := fun h => hvw (HeightOneSpectrum.ext h)
    exact (Ideal.isCoprime_iff_sup_eq.mpr
      (Ideal.IsMaximal.coprime_of_ne v.isMaximal w.isMaximal hne)).pow
  have hnorm : Ideal.absNorm (Ideal.span {(p : 𝓞 F)}) = p ^ Module.finrank ℚ F := by
    rw [Ideal.absNorm_span_singleton]
    have : (p : 𝓞 F) = algebraMap ℤ (𝓞 F) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank]
    simp
  have h := Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd hdvd)
  rw [hnorm, map_prod] at h
  simp only [map_pow] at h
  exact Nat.le_of_dvd (pow_pos hp _) h

open NumberField IsDedekindDomain Polynomial in
open scoped WithZero TensorProduct in

theorem _root_.GlobalTheory.CNorm.index_finPow_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F]
    [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p →
    (_root_.GlobalTheory.CNorm.finPow p F S).index ≠ 0 ∧
      (_root_.GlobalTheory.CNorm.finPow p F S).index ≤
        p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  intro p F _ _ _ S hp
  choose! e he hdiv using fun v : HeightOneSpectrum (𝓞 F) => exists_valuation_natCast_eq_exp_neg_and_dvd v hp
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F),
      (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≠ 0 ∧
        (_root_.GlobalTheory.CNorm.powSub p (algebraMap F (v.adicCompletion F))).index ≤
          p * Ideal.absNorm v.asIdeal ^ e v * p := by
    intro v
    obtain ⟨ht, hrel⟩ :=
      _root_.GlobalTheory.CNorm.pIdx_units_finite_extension_adicCompletion p F v (e v) (v.adicCompletion F) hp (he v)
    rw [Module.finrank_self, pow_one] at hrel
    have hN : Ideal.absNorm v.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact v.ne_bot
    have hne : _root_.GlobalTheory.CNorm.pIdx p (⊤ : Subgroup (v.adicCompletion F)ˣ) ≠ 0 := by
      rw [hrel]
      exact mul_ne_zero (mul_ne_zero hp.ne' (pow_ne_zero _ hN)) ht
    obtain ⟨h1, h2⟩ := powSub_index_ne_zero_and_le_pIdx hp (algebraMap F (v.adicCompletion F)) hne
    refine ⟨h1, h2.trans ?_⟩
    rw [hrel]
    exact Nat.mul_le_mul_left _ (pTor_units_le hp)
  have hinf : _root_.GlobalTheory.CNorm.finPow p F S =
      ⨅ v : S, _root_.GlobalTheory.CNorm.powSub p
        (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F)) := by
    unfold _root_.GlobalTheory.CNorm.finPow
    rw [iInf_subtype']
  rw [hinf]
  refine ⟨Subgroup.index_iInf_ne_zero fun v => (hloc v).1, (Subgroup.index_iInf_le _).trans ?_⟩
  calc ∏ v : S, (_root_.GlobalTheory.CNorm.powSub p
          (algebraMap F ((v : HeightOneSpectrum (𝓞 F)).adicCompletion F))).index
      ≤ ∏ v : S, (p * Ideal.absNorm (v : HeightOneSpectrum (𝓞 F)).asIdeal ^ e v * p) :=
        Finset.prod_le_prod' fun v _ => (hloc v).2
    _ = p ^ (2 * S.card) * ∏ v ∈ S, Ideal.absNorm v.asIdeal ^ e v := by
        rw [Finset.prod_coe_sort S (fun v => p * Ideal.absNorm v.asIdeal ^ e v * p)]
        simp only [Finset.prod_mul_distrib, Finset.prod_const]
        ring
    _ ≤ p ^ (2 * S.card) * p ^ Module.finrank ℚ F :=
        Nat.mul_le_mul_left _ (prod_absNorm_pow_le_pow_finrank S hp e fun v _ => hdiv v)
    _ = p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
        rw [IsTotallyComplex.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
          IsTotallyComplex.nrRealPlaces_eq_zero, ← pow_add]
        ring_nf

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitsLocalPowersAtPlaces_index_le : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (S : Finset (HeightOneSpectrum (𝓞 F))), 0 < p → (finPow p F S).index ≠ 0 ∧ (finPow p F S).index ≤ p ^ (2 * (S.card + Fintype.card (InfinitePlace F))) := by
  atlas_forward_decl GlobalTheory.CNorm.index_finPow_le
end

section
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mem_kNorm_iff_map_mem_id (p : ℕ) {F L : Type} [Field F] [Field L] (φ : F →+* L) (δ : F)
    (x : Fˣ) :
    x ∈ kNorm p φ δ ↔ Units.map (φ : F →* L) x ∈ kNorm p (RingHom.id L) (φ δ) := by
  rw [mem_kNorm, mem_kNorm]
  exact Iff.rfl

theorem pow_tNon_le_index_finNorm :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ : F)
      (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p →
      (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  intro p F _ _ _ ζ δ S hp hζ
  classical
  have hpow := (GlobalTheory.T.unitsMappingToPowers_le_unitsLocalKummerNorms p hp.pos).1
  have hPN : finPow p F S ≤ finNorm p F δ S := by
    unfold finPow finNorm
    exact iInf_mono fun v => iInf_mono fun _ => hpow _ _ _ _
  have h0 : (finNorm p F δ S).index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (GlobalTheory.T.unitsLocalPowersAtPlaces_index_le p F S hp.pos).1 (Subgroup.index_dvd_of_le hPN)
  refine ⟨h0, ?_⟩
  set A : Set (HeightOneSpectrum (𝓞 F)) :=
    {v | v ∈ S ∧ ∀ r : v.adicCompletion F, r ^ p ≠ algebraMap F (v.adicCompletion F) δ} with hA
  have hAf : A.Finite := S.finite_toSet.subset fun v hv => hv.1
  letI : Fintype A := hAf.fintype
  let K : A → Subgroup Fˣ := fun v => kNorm p (algebraMap F (v.1.adicCompletion F)) δ
  have hle : finNorm p F δ S ≤ ⨅ i, K i := le_iInf fun v => iInf₂_le v.1 v.2.1
  have hdvd := Subgroup.index_dvd_of_le hle
  have hcard : Fintype.card A = tNon p F δ S := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [← hcard]
  refine le_trans (GlobalTheory.T.pow_card_le_index_iInf_of_prime' p Fˣ A K hp ?_ ?_ (ne_zero_of_dvd_ne_zero h0 hdvd))
    (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd)
  · intro v x
    exact hpow _ _ _ _ ⟨algebraMap F _ (x : F), by simp⟩
  · intro v
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_unit_not_localKummerNorm_of_not_pow p F ζ δ v.1 hp hζ v.2.2
    obtain ⟨x, hx0, hxv⟩ := GlobalTheory.T.exists_approx_mod_powers' p F S
      (Function.update (fun w : HeightOneSpectrum (𝓞 F) => (1 : w.adicCompletion F)) v.1
        (c : v.1.adicCompletion F)) hp.pos (by
        intro w
        by_cases hw : w = v.1
        · subst hw; simp
        · simp [Function.update_of_ne hw])
    refine ⟨Units.mk0 x hx0, ?_, ?_⟩
    · intro hm
      obtain ⟨r, hr⟩ := hxv v.1 v.2.1
      rw [Function.update_self] at hr
      have hr0 : r ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero, mul_zero] at hr
        exact hx0 (by simpa using hr)
      have hm' := (mem_kNorm_iff_map_mem_id p _ δ _).1 hm
      have hrm : (Units.mk0 r hr0) ^ p ∈ kNorm p (RingHom.id (v.1.adicCompletion F))
          (algebraMap F (v.1.adicCompletion F) δ) := hpow _ _ _ _ ⟨r, by simp⟩
      apply hc
      have hq := Subgroup.div_mem _ hm' hrm
      convert hq using 1
      rw [eq_div_iff_mul_eq']
      apply Units.ext
      simpa using hr.symm
    · intro w hj
      have hw : w.1 ≠ v.1 := fun h => hj (Subtype.ext h)
      obtain ⟨r, hr⟩ := hxv w.1 w.2.1
      rw [Function.update_of_ne hw, one_mul] at hr
      exact hpow _ _ _ _ ⟨r, hr.symm⟩

end GlobalTheory.CNorm
end

open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_countPlacesNotLocalPower_le_index : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] [IsTotallyComplex F] (ζ δ : F) (S : Finset (HeightOneSpectrum (𝓞 F))), p.Prime → IsPrimitiveRoot ζ p → (finNorm p F δ S).index ≠ 0 ∧ p ^ tNon p F δ S ≤ (finNorm p F δ S).index := by
  atlas_forward_decl GlobalTheory.CNorm.pow_tNon_le_index_finNorm
end
