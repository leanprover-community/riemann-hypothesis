import Development.AutomorphicArithmetic.FrobeniusLocalisation.MuDefs
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsRationalUnitaryDeterminantMap
import Development.AutomorphicArithmetic.FrobeniusLocalisation.FrobGSpec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AutomorphicArithmetic.WeightCongruences.ProdResidueCharNormOneUnitEqOne

section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem mem_pow_of_prim {L : Type} [Field L] [NumberField L] (p : ℕ) [Fact p.Prime]
    (Q : Ideal (𝓞 L)) (hQ : Q.IsPrime) (hpQ : (p : 𝓞 L) ∈ Q) (η : L) (hη : IsPrimitiveRoot η p) :
    (p : 𝓞 L) ∈ Q ^ (p - 1) := by
  obtain ⟨u, hu⟩ := IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime p hη
  have hx : hη.toInteger - 1 ∈ Q := by
    apply hQ.mem_of_pow_mem (p - 1)
    have : (hη.toInteger - 1) ^ (p - 1) = (p : 𝓞 L) * ((u⁻¹ : (𝓞 L)ˣ) : 𝓞 L) := by
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
    rw [this]
    exact Q.mul_mem_right _ hpQ
  rw [← hu]
  exact (Q ^ (p - 1)).mul_mem_right _ (Ideal.pow_mem_pow hx (p - 1))

theorem UpperTheory.HF.Formalism.HC.HostAx.not_dvd_muW_of_unramified :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → p ≠ 2 → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P → (p : 𝓞 H.E) ∉ P ^ 2 → ¬ p ∣ H.muW := by
  intro φ H p hp hp2 P hP hpP hpP2 hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨ζ, hζ⟩ := (HostRaw.dvd_muW_iff _ hp.pos).1 hdvd
  have h := mem_pow_of_prim p P hP hpP ζ hζ
  have h2 : 2 ≤ p - 1 := by
    have := hp.two_le
    omega
  exact hpP2 (Ideal.pow_le_pow_right h2 h)
end

section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.HC Formalism.FrobeniusOrbits
open scoped Pointwise

private theorem eq_of_pow_eq_one_of_sub_mem {S : Type*} [CommRing S] [IsDomain S] (P : Ideal S) [hP : P.IsPrime] {m : ℕ} (hm : (m : S) ∉ P)
    {x y : S} (hx : x ^ m = 1) (hy : y ^ m = 1) (hxy : x - y ∈ P) : x = y := by
  by_contra hne
  have h1 := geom_sum₂_mul x y m
  rw [hx, hy, sub_self, mul_eq_zero, sub_eq_zero] at h1
  have h2 := congrArg (Ideal.Quotient.mk P) (h1.resolve_right hne)
  have h3 : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y := Ideal.Quotient.eq.mpr hxy
  rw [RingHom.map_geom_sum₂, h3, geom_sum₂_self, map_zero, ← map_pow, ← map_natCast (Ideal.Quotient.mk P), ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem] at h2
  rcases hP.mem_or_mem h2 with h4 | h4
  · exact hm h4
  · have h5 : y ∈ P := hP.mem_of_pow_mem _ h4
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
    have h6 := P.pow_mem_of_mem h5 m (Nat.pos_of_ne_zero hm0)
    rw [hy] at h6
    exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h6)

theorem UpperTheory.HF.Formalism.HC.HostAx.isRt_eq_one_of_sub_mem :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → ¬ p ∣ H.muW → ∀ (P : Ideal (𝓞 H.E)), P.IsPrime → (p : 𝓞 H.E) ∈ P →
      ∀ ξ ξ' : 𝓞 H.E, H.IsRt (ξ : H.E) → H.IsRt (ξ' : H.E) → ξ - ξ' ∈ P → ξ = ξ' := by
  intro φ H p hp hpw P hP hpP ξ ξ' hξ hξ' hsub
  have key : ∀ x : 𝓞 H.E, H.IsRt (x : H.E) → x ^ H.muW = 1 := by
    intro x hx
    apply RingOfIntegers.coe_injective
    rw [map_pow, map_one]
    exact (H.isRt_iff _).1 hx
  have hw : ((H.muW : ℕ) : 𝓞 H.E) ∉ P := by
    intro h
    have hc : IsCoprime ((p : ℕ) : 𝓞 H.E) ((H.muW : ℕ) : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.Prime.coprime_iff_not_dvd hp).2 hpw)
    obtain ⟨a, b, hab⟩ := hc
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact P.add_mem (P.mul_mem_left a hpP) (P.mul_mem_left b h)
  exact eq_of_pow_eq_one_of_sub_mem P hw (key ξ hξ) (key ξ' hξ') hsub
end

section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.frob_decomp :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ) [Fact p.Prime], ¬ p ∣ H.condN → ∀ (P : Ideal (𝓞 H.E)) [P.IsPrime] [P.LiesOver (span {(p : ℤ)})],
      (∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P ↔ H.galE σ ∈ Subgroup.zpowers (H.frobG p)) ∧
      Nat.card (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P) = orderOf (H.frobG p) ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard * orderOf (H.frobG p) = 4 * φ.ord := by
  intro φ H p hpf hp P _ _
  have hpp : p.Prime := Fact.out
  have hco : Nat.Coprime p H.condN := hpp.coprime_iff_not_dvd.2 hp
  have hoc : ordCompl[p] H.condN = H.condN := by
    rw [Nat.factorization_eq_zero_of_not_dvd hp, pow_zero, Nat.div_one]
  have h1 : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ ∈ MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P ↔
      H.galE σ ∈ Subgroup.zpowers (H.frobG p) := by
    intro σ
    rw [H.der.decomp p P σ, hoc, ← mem_powers_iff_mem_zpowers, H.frobG_of_coprime hco]
    constructor
    · rintro ⟨u, k, hu, hσ⟩
      refine ⟨k, ?_⟩
      have hu' : u = ZMod.unitOfCoprime p hco ^ k := by
        apply Units.ext
        rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow,
          ← (ZMod.natCast_eq_natCast_iff _ _ _).2 hu, ZMod.natCast_zmod_val]
      show H.art (ZMod.unitOfCoprime p hco) ^ k = H.gal σ
      rw [hσ, hu', map_pow]
    · rintro ⟨k, hk⟩
      refine ⟨ZMod.unitOfCoprime p hco ^ k, k, ?_, ?_⟩
      · rw [Units.val_pow_eq_pow_val, ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ZMod.val_natCast]
        exact Nat.mod_modEq _ _
      · rw [map_pow]
        exact hk.symm
  have h2 : Nat.card (MulAction.stabilizer (H.E ≃ₐ[ℚ] H.E) P) = orderOf (H.frobG p) := by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (H.gal.toEquiv.subtypeEquiv h1)
  refine ⟨h1, h2, ?_⟩
  have := H.galois
  have horb : MulAction.orbit (H.E ≃ₐ[ℚ] H.E) P = primesOver (span {(p : ℤ)}) (𝓞 H.E) := by
    ext Q
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨inferInstanceAs (g • P).IsPrime, inferInstanceAs ((g • P).LiesOver _)⟩
    · rintro ⟨hQ1, hQ2⟩
      exact Ideal.exists_smul_eq_of_isGaloisGroup (span {(p : ℤ)}) P Q (H.E ≃ₐ[ℚ] H.E)
  rw [← horb, ← h2, ← MulAction.index_stabilizer, Subgroup.index_mul_card, ← φ.natCard_GG]
  exact Nat.card_congr H.gal.toEquiv
end

section
open UpperTheory.HF

open NumberField IntermediateField Ideal Formalism.FrobeniusOrbits Formalism.HC
open scoped Pointwise

theorem UpperTheory.HF.split_complete :
    ∀ (φ : Frame) (H : HostAx φ) (p : ℕ), p.Prime → p ≡ 1 [MOD H.condN] →
      ¬ p ∣ H.condN ∧ H.frobG p = 1 ∧ jacobiSym (-(H.d : ℤ)) p = 1 ∧ H.condN < p ∧ 16 * H.d * H.q ∣ p - 1 ∧
      (primesOver (span {(p : ℤ)}) (𝓞 H.E)).ncard = 4 * φ.ord := by
  intro φ H p hp h1
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : H.condN ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).1 h1.symm
  have h2 := hp.two_le
  have hlt : H.condN < p := by
    have := Nat.le_of_dvd (by omega) hdvd
    omega
  have hnd : ¬ p ∣ H.condN := fun h => absurd (Nat.le_of_dvd H.condN_pos h) (by omega)
  have hc : Nat.Coprime p H.condN := hp.coprime_iff_not_dvd.2 hnd
  have hfrob : H.frobG p = 1 := by
    rw [H.frobG_of_coprime hc]
    have hu : ZMod.unitOfCoprime p hc = 1 := by
      apply Units.ext
      rw [ZMod.coe_unitOfCoprime, Units.val_one, (ZMod.natCast_eq_natCast_iff _ _ _).2 h1, Nat.cast_one]
    rw [hu, map_one]
  refine ⟨hnd, hfrob, ?_, hlt, ?_, ?_⟩
  · refine (UpperTheory.HF.frobG_spec φ H p hnd).2.2.2.2.1.1 ?_
    rw [hfrob]
    exact one_mem _
  · refine Dvd.dvd.trans ?_ hdvd
    rw [mul_right_comm]
    exact Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_right H.sixteen_dvd_QS _) _
  · haveI : (span {(p : ℤ)}).IsPrime :=
      (span_singleton_prime (by exact_mod_cast hp.ne_zero)).2 (Nat.prime_iff_prime_int.1 hp)
    obtain ⟨⟨P, hP1, hP2⟩⟩ := Ideal.nonempty_primesOver (S := 𝓞 H.E) (span {(p : ℤ)})
    have h := (UpperTheory.HF.frob_decomp φ H p hnd P).2.2
    rwa [hfrob, orderOf_one, mul_one] at h
end

section
open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory
open scoped Pointwise

private theorem not_dvd_discr_of_splitsC {L : Type} [Field L] [NumberField L] [IsGalois ℚ L] {p : ℕ} (hp : p.Prime)
    (hs : SplitsC L p) : ¬ (p : ℤ) ∣ discr L := by
  have : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hm : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have h1 := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (Ideal.span {(p : ℤ)}) (𝓞 L) (L ≃ₐ[ℚ] L)
  unfold SplitsC at hs
  rw [← ncard_places_eq_primesOver hp, hs, IsGalois.card_aut_eq_finrank] at h1
  have he := Nat.eq_one_of_mul_eq_one_right ((mul_eq_left₀ Module.finrank_pos.ne').1 h1)
  rw [NumberField.not_dvd_discr_iff_isUnramifiedIn L (𝓞 L) hpZ,
    Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one]
  intro P _ hlo
  rwa [Ideal.ramificationIdxIn_eq_ramificationIdx (Ideal.span {(p : ℤ)}) P (L ≃ₐ[ℚ] L)] at he

private theorem exists_place {L : Type} [Field L] [NumberField L] {p : ℕ} (hs : SplitsC L p) :
    ∃ v : HeightOneSpectrum (𝓞 L), ((p : ℕ) : 𝓞 L) ∈ v.asIdeal := by
  unfold SplitsC at hs
  exact Set.nonempty_of_ncard_ne_zero (hs ▸ Module.finrank_pos.ne')

private theorem pow_sub_one_mem {L : Type} [Field L] [NumberField L] {p : ℕ} (v : HeightOneSpectrum (𝓞 L))
    (hN : Ideal.absNorm v.asIdeal = p) {x : 𝓞 L} {m : ℕ} (hm : m ≠ 0) (hx : x ^ m = 1) :
    x ^ (p - 1) - 1 ∈ v.asIdeal := by
  have := v.isMaximal
  let := Ideal.Quotient.field v.asIdeal
  have : Finite (𝓞 L ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot _ v.ne_bot
  let := Fintype.ofFinite (𝓞 L ⧸ v.asIdeal)
  have hc : Fintype.card (𝓞 L ⧸ v.asIdeal) = p := by
    rw [← hN, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have h0 : Ideal.Quotient.mk v.asIdeal x ≠ 0 := by
    intro h
    have h1 := congrArg (Ideal.Quotient.mk v.asIdeal) hx
    rw [map_pow, h, zero_pow hm, map_one] at h1
    exact zero_ne_one h1
  rw [← Ideal.Quotient.eq, map_pow, map_one, ← hc]
  exact FiniteField.pow_card_sub_one_eq_one _ h0

theorem UpperTheory.HF.Formalism.HC.HostAx.splitsC_facts :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → (p ≡ 1 [MOD H.condN] → SplitsC H.E p) ∧
      (SplitsC H.E p → ¬ p ∣ H.w ∧ H.w ∣ p - 1 ∧ ∀ v : HeightOneSpectrum (𝓞 H.E), ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal →
        Ideal.absNorm v.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v.asIdeal ^ 2 ∧ ¬ ConjPl H.conj.toRingEquiv v v ∧
        (∃ x : 𝓞 H.E, x ∈ v.asIdeal ∧ ∀ y : 𝓞 H.E, (y : H.E) = H.conj (x : H.E) → y ∉ v.asIdeal) ∧
        ∀ Q : HeightOneSpectrum (𝓞 H.K), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal → ∀ v', ConjPl H.conj.toRingEquiv v v' →
          ((p : ℕ) : 𝓞 H.E) ∈ v'.asIdeal ∧ (v.under (𝓞 H.K) = Q ↔ v'.under (𝓞 H.K) ≠ Q)) := by
  intro φ H p hp
  have hG : IsGalois ℚ H.E := H.galois
  refine ⟨fun h => ?_, fun hs => ?_⟩
  · unfold SplitsC
    rw [ncard_places_eq_primesOver hp, (UpperTheory.HF.split_complete φ H p hp h).2.2.2.2.2, H.finrank_cmField]
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact not_dvd_discr_of_splitsC hp hs (by exact_mod_cast H.der.discr_primes.2.1)
  obtain ⟨v₀, hv₀⟩ := exists_place hs
  obtain ⟨hN₀, hu₀, -⟩ := splitsC_place hp hs v₀ hv₀
  have hpw : ¬ p ∣ H.w := H.not_dvd_muW_of_unramified p hp hp2 v₀.asIdeal v₀.isPrime hv₀ hu₀
  refine ⟨hpw, ?_, fun v hv => ?_⟩
  · have hζ := H.muGen_prim
    let x : 𝓞 H.E := hζ.toInteger
    have hx : (x : H.E) = H.muGen := rfl
    have hxw : x ^ H.w = 1 := hζ.toInteger_isPrimitiveRoot.pow_eq_one
    have h1 : x ^ (p - 1) = 1 := by
      refine H.isRt_eq_one_of_sub_mem p hp hpw v₀.asIdeal v₀.isPrime hv₀ _ _ ?_ ?_
        (pow_sub_one_mem v₀ hN₀ H.w_pos.ne' hxw)
      · exact (H.isRt_iff_pow _).2 ⟨p - 1, by rw [← hx]; rfl⟩
      · exact ⟨1, one_pos, by simp⟩
    exact hζ.toInteger_isPrimitiveRoot.dvd_of_pow_eq_one _ h1
  have hsq := H.sqd_sq
  have hc := H.conj_sqd
  have hb0 := H.sqd_ne_zero
  have hb : ∀ σ : H.E ≃ₐ[ℚ] H.E, σ H.sqd = H.sqd ∨ σ H.sqd = -H.sqd := by
    intro σ
    apply sq_eq_sq_iff_eq_or_eq_neg.1
    rw [← map_pow, hsq, map_neg, map_natCast]
  obtain ⟨h1, h2, h3⟩ := splitsC_place hp hs v hv
  have hne : H.conj • v.asIdeal ≠ v.asIdeal := fun heq => H.conj_ne_one (h3 _ heq)
  refine ⟨h1, h2, fun h => hne ((conjPl_iff_smul H.conj v v).1 h), ?_, fun Q hQ v' hvv => ⟨?_, ?_⟩⟩
  · by_contra hn
    push Not at hn
    have hle : H.conj • v.asIdeal ≤ v.asIdeal := by
      intro y hy
      rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hy
      obtain ⟨z, hz, hzv⟩ := hn _ hy
      have e : z = y := RingOfIntegers.ext (hz.trans (H.conj.apply_symm_apply (y : H.E)))
      exact e ▸ hzv
    obtain ⟨w, hw, -⟩ := existsUnique_conjPl H.conj.toRingEquiv v
    have hw' := (conjPl_iff_smul H.conj v w).1 hw
    apply hne
    rw [hw'] at hle ⊢
    exact w.isMaximal.eq_of_le v.isPrime.ne_top hle
  · exact ((conjPl_iff_mem _ v v').1 hvv _ _ (by simp)).1 hv
  · exact under_eq_iff_under_ne hp hs H.sqd hb0 hb H.conj hc v v' hv ((conjPl_iff_smul H.conj v v').1 hvv) Q hQ
end

section
open UpperTheory.HF

open NumberField IsDedekindDomain Formalism.HC Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory

theorem UpperTheory.HF.Formalism.HC.HostAx.prod_tame_eq_one :
    ∀ {φ : Frame} (H : HostAx φ) (p : ℕ), p.Prime → SplitsC H.E p → ∀ (Q : HeightOneSpectrum (𝓞 H.K)), ((p : ℕ) : 𝓞 H.K) ∈ Q.asIdeal →
      ∀ (ω : (ZMod p)ˣ →* ℂˣ) (θ : ∀ w : HeightOneSpectrum (𝓞 H.E), (𝓞 H.E ⧸ w.asIdeal)ˣ →* ℂˣ),
      (∀ w ∈ aboveF (L := H.E) H.K Q, ∀ (a : ℕ) (ha : a.Coprime p) (b : (𝓞 H.E ⧸ w.asIdeal)ˣ),
        (b : 𝓞 H.E ⧸ w.asIdeal) = Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E) → θ w b = ω (ZMod.unitOfCoprime a ha)) →
      ∀ ζ : (𝓞 H.E)ˣ, H.IsMu ((ζ : 𝓞 H.E) : H.E) →
        ∏ w ∈ aboveF (L := H.E) H.K Q, θ w (Units.map (Ideal.Quotient.mk w.asIdeal).toMonoidHom ζ) = 1 := by
  intro φ H p hp hs Q hQ ω θ hθ ζ hζ
  have hG : IsGalois ℚ H.E := H.galois
  have hGK : IsGalois H.K H.E := IsGalois.tower_top_of_isGalois ℚ H.K H.E
  have memS : ∀ w, w ∈ aboveF (L := H.E) H.K Q ↔ w.under (𝓞 H.K) = Q := fun w => by
    rw [aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have overp : ∀ w ∈ aboveF (L := H.E) H.K Q, ((p : ℕ) : 𝓞 H.E) ∈ w.asIdeal := by
    intro w hw
    have h1 : ((p : ℕ) : 𝓞 H.K) ∈ (w.under (𝓞 H.K)).asIdeal := by rw [(memS w).1 hw]; exact hQ
    have h2 : ((p : ℕ) : 𝓞 H.K) ∈ Ideal.under (𝓞 H.K) w.asIdeal := h1
    rw [Ideal.mem_under, map_natCast] at h2
    exact h2
  refine UpperTheory.prod_residue_char_norm_one_unit_eq_one H.K H.E p hp Q _ memS (fun w hw => ?_) ω θ (fun w hw a ha => ?_) ζ (H.der.norm_mu _ hζ)
  · have h := ((H.splitsC_facts p hp).2 hs).2.2 w (overp w hw)
    exact ⟨h.1, h.2.1⟩
  · have hu : IsUnit (Ideal.Quotient.mk w.asIdeal (a : 𝓞 H.E)) := by
      obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 ha
      have h0 : Ideal.Quotient.mk w.asIdeal (p : 𝓞 H.E) = 0 := Ideal.Quotient.eq_zero_iff_mem.2 (overp w hw)
      have h1 := congrArg (Int.cast : ℤ → 𝓞 H.E ⧸ w.asIdeal) huv
      rw [map_natCast] at h0 ⊢
      push_cast at h1
      rw [h0, mul_zero, add_zero, mul_comm] at h1
      exact IsUnit.of_mul_eq_one _ h1
    exact ⟨hu.unit, rfl, hθ w hw a ha _ rfl⟩
end
