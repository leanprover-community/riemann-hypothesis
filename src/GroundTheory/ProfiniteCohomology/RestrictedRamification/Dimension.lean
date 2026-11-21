import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Brauer
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteSetOfNsmulEqZeroQZ
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DimensionSylow
import GroundTheory.ProfiniteCohomology.RestrictedRamification.SurjectiveOfInjectiveOfInjective
import GroundTheory.ProfiniteCohomology.RestrictedRamification.FiniteOpen
import GroundTheory.ProfiniteCohomology.CompactSupportCohomology

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open NumberField IsDedekindDomain GroundTheory.Global DirectSum

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem QZ.nsmul_mk (j : ℕ) (r : ℚ) : j • QZ.mk r = QZ.mk (j * r) := by
  have h := map_nsmul QZ.mkHom j r
  rw [nsmul_eq_mul] at h
  exact h.symm

open Classical in

def qzDiv (ℓ : ℕ) (q : QZ) : QZ :=
  if q = 0 then 0 else QZ.mk ((QZ.mk_surjective q).choose / ℓ)

theorem qzDiv_zero (ℓ : ℕ) : qzDiv ℓ 0 = 0 := by
  simp [qzDiv]

theorem nsmul_qzDiv {ℓ : ℕ} (hℓ : ℓ ≠ 0) (q : QZ) : ℓ • qzDiv ℓ q = q := by
  by_cases hq : q = 0
  · rw [hq, qzDiv_zero, smul_zero]
  · rw [qzDiv, if_neg hq, QZ.nsmul_mk]
    have hℓq : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
    rw [mul_div_cancel₀ _ hℓq]
    exact (QZ.mk_surjective q).choose_spec

variable {K : FiniteSubfield}

theorem eq_zero_inl_of_pow_nsmul_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (v : InfinitePlace K.1)
    (hv : ℓ ≠ 2 ∨ v.IsComplex) (t : localGaloisCohomology K 2 (.inl v)) (k : ℕ) (ht : ℓ ^ k • t = 0) :
    t = 0 := by
  rcases hv with h2 | hc
  · have h2t : 2 • t = 0 := by
      apply placeInv_injective (.inl v)
      rw [map_nsmul, map_zero]
      rcases placeInv_inl_eq_zero_or_eq_half v t with h | h
      · rw [h, smul_zero]
      · rw [h, two_nsmul, QZ.mk_half_add_mk_half]
    exact eq_zero_of_coprime_nsmul_eq_zero ((Nat.coprime_primes Nat.prime_two hℓ).2 (Ne.symm h2)) h2t ht
  · have := subsingleton_cohomology_two_of_isComplex v hc
    exact Subsingleton.elim (α := cohomology (galUnitsZ v.Completion (AlgebraicClosure v.Completion)) 2) _ _

variable (K) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem exists_nsmul_eq_localPrimaryKernel (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (t : localPrimaryKernel K S ℓ) : ∃ s : localPrimaryKernel K S ℓ, ℓ • s = t := by
  classical
  obtain ⟨⟨k, hk⟩, hout, hsum⟩ := t.2
  have hℓ0 : ℓ ≠ 0 := hℓ.ne_zero
  have hinf : ∀ v : InfinitePlace K.1, (t : ⨁ v : Place K.1, localGaloisCohomology K 2 v) (.inl v) = 0 :=
    fun v => eq_zero_inl_of_pow_nsmul_eq_zero hℓ v (hK.imp id fun h => h.isComplex v) _ k (by
      have := congrArg (fun x : ⨁ v : Place K.1, localGaloisCohomology K 2 v => x (.inl v)) hk
      rwa [DFinsupp.smul_apply] at this)
  let e : ∀ v : HeightOneSpectrum (𝓞 K.1), localGaloisCohomology K 2 (.inr v) ≃+ QZ := fun v =>
    AddEquiv.ofBijective (placeInv (.inr v)) (placeInv_bijective_inr v)
  let f : ∀ v : Place K.1, localGaloisCohomology K 2 v → localGaloisCohomology K 2 v
    | .inl _ => fun _ => 0
    | .inr v => fun x => (e v).symm (qzDiv ℓ (e v x))
  have hf : ∀ v, f v 0 = 0 := by
    rintro (v | v)
    · rfl
    · change (e v).symm (qzDiv ℓ (e v 0)) = 0
      rw [map_zero, qzDiv_zero, map_zero]
  let s₀ : ⨁ v : Place K.1, localGaloisCohomology K 2 v := DFinsupp.mapRange f hf t.1
  have hs₀ : ℓ • s₀ = t := by
    refine DFinsupp.ext fun v => ?_
    rw [DFinsupp.smul_apply, DFinsupp.mapRange_apply]
    rcases v with v | v
    · change ℓ • (0 : localGaloisCohomology K 2 (.inl v)) = _
      rw [smul_zero, hinf v]
    · change ℓ • (e v).symm (qzDiv ℓ (e v _)) = _
      rw [← map_nsmul, nsmul_qzDiv hℓ0, AddEquiv.symm_apply_apply]
  obtain ⟨v₀, hv₀⟩ := exists_place_above K ℓ hℓ
  let c := sumPlaceInv K s₀
  let o : ⨁ v : Place K.1, localGaloisCohomology K 2 v :=
    DirectSum.of (fun v : Place K.1 => localGaloisCohomology K 2 v) (Sum.inr v₀) ((e v₀).symm c)
  let s : ⨁ v : Place K.1, localGaloisCohomology K 2 v := s₀ - o
  have hc : ℓ • c = 0 := by
    change ℓ • sumPlaceInv K s₀ = 0
    rw [← map_nsmul, hs₀, hsum]
  have hs : ℓ • s = t := by
    rw [smul_sub, hs₀, ← map_nsmul, ← map_nsmul, hc, map_zero, map_zero, sub_zero]
  refine ⟨⟨s, ⟨k + 1, ?_⟩, fun v hv => ?_, ?_⟩, Subtype.ext hs⟩
  · rw [pow_succ, mul_smul, hs, hk]
  · have hne : (.inr v : Place K.1) ≠ .inr v₀ := fun h => hv (by cases h; exact hS v₀ hv₀)
    change s₀ (.inr v) - o (.inr v) = 0
    rw [show o (.inr v) = 0 from DirectSum.of_eq_of_ne _ _ _ hne, sub_zero]
    change (e v).symm (qzDiv ℓ (e v (t.1 (.inr v)))) = 0
    rw [hout v hv, map_zero, qzDiv_zero, map_zero]
  · change sumPlaceInv K (s₀ - o) = 0
    rw [map_sub, sumPlaceInv_of]
    change c - e v₀ ((e v₀).symm c) = 0
    rw [AddEquiv.apply_symm_apply, sub_self]

set_option maxHeartbeats 1000000 in
include hℓ hS in

theorem exists_nsmul_eq_h2SUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (y : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ) :
    ∃ z : AddCommGroup.primaryComponent (cohomology (galSUnitsMax K.1 ℚ̄ S) 2) ℓ, ℓ • z = y := by
  obtain ⟨ιs⟩ := nonempty_localEmbeddings K
  let E := sUnitsH2PrimaryEquiv K S ℓ hℓ hS ιs
  obtain ⟨s, hs⟩ := exists_nsmul_eq_localPrimaryKernel K S ℓ hℓ hS hK (E y)
  refine ⟨E.symm s, ?_⟩
  rw [← E.symm_apply_apply y, ← hs]
  exact (map_nsmul E.symm ℓ s).symm

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem nsmul_rootsOfUnity_eq_zero {E : Type*} [CommMonoid E] (ℓ : ℕ)
    (a : Additive (rootsOfUnity ℓ E)) : ℓ • a = 0 := by
  apply Additive.toMul.injective
  rw [toMul_nsmul, toMul_zero]
  exact Subtype.ext ((mem_rootsOfUnity ℓ _).1 (Additive.toMul a).2)

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {E : ShortComplex (Rep.{0} (ULift.{0} ℤ) G)} [IsDiscreteRep E.X₁]
  [IsDiscreteRep E.X₂] [IsDiscreteRep E.X₃]

theorem eq_zero_h3_of_shortExact (hE : E.ShortExact) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hX : ∀ a : E.X₁, ℓ • a = 0) (h3 : ∀ z : cohomology E.X₂ 3, ℓ • z = 0 → z = 0)
    (hdiv : ∀ y : cohomology E.X₃ 2, (∃ j : ℕ, ℓ ^ j • y = 0) →
      ∃ z : cohomology E.X₂ 2, (cohomologyMap E.g 2).hom z = y)
    (x : cohomology E.X₁ 3) : x = 0 := by
  have hfx : (cohomologyMap E.f 3).hom x = 0 := by
    refine h3 _ ?_
    rw [← map_nsmul, nsmul_cohomology_eq_zero _ hX 3 x, map_zero]
  obtain ⟨y, rfl⟩ := exists_δ_eq_of_cohomologyMap_f_eq_zero hE 2 3 rfl x hfx
  have hyt : IsOfFinAddOrder y := isTorsion_cohomology _ (by norm_num) y
  have hδℓ : ℓ ^ 1 • (δ hE 2 3 rfl).hom.toAddMonoidHom y = 0 := by
    rw [pow_one]
    exact nsmul_cohomology_eq_zero _ hX 3 _
  obtain ⟨y', hj, hy'⟩ := exists_primary_map_eq (δ hE 2 3 rfl).hom.toAddMonoidHom hℓ hyt hδℓ
  change (δ hE 2 3 rfl).hom y = 0
  rw [← show (δ hE 2 3 rfl).hom y' = (δ hE 2 3 rfl).hom y from hy']
  obtain ⟨z, rfl⟩ := hdiv y' hj
  rw [← ModuleCat.comp_apply, comp_δ]
  rfl

end Abstract

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) (ℓ : ℕ) (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

set_option maxHeartbeats 1000000 in
include hℓ hS in

theorem eq_zero_h3_rootsOfUnity_of_h3_sUnits (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (h3 : ∀ z : cohomology (galSUnitsMax K.1 ℚ̄ S) 3, ℓ • z = 0 → z = 0)
    (x : cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 3) : x = 0 := by
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have hE := sUnitsKummerSequence_shortExact (Ω := ℚ̄) S ℓ (fun v hv h => hv (hS v h))
  refine eq_zero_h3_of_shortExact (E := sUnitsKummerSequence S (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) hE hℓ (nsmul_rootsOfUnity_eq_zero ℓ) h3 (fun y hy => ?_) x
  obtain ⟨z, hz⟩ := exists_nsmul_eq_h2SUnits K S ℓ hℓ hS hK ⟨y, hy⟩
  refine ⟨z.1, ?_⟩
  rw [sUnitsKummerSequence_g]
  exact (cohomologyMap_nsmul_id_apply _ ℓ 2 z.1).trans (congrArg Subtype.val hz)

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory NumberField IsDedekindDomain GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Abstract

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem subsingleton_cohomology_of_cdp_le_two {n : ℕ} (hn : n ≠ 0)
    (hcd : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ n → cdp ℓ G ≤ 2) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) := by
  have htors : IsAddTorsion M := fun m =>
    isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨n, Nat.pos_of_ne_zero hn, hM m⟩
  suffices h : ∀ x : cohomology M r, x = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  refine eq_zero_of_primaryComponent_eq_bot n hn (fun ℓ hℓ hℓn => ?_) x
    (nsmul_cohomology_eq_zero M hM r x)
  refine primaryComponent_cohomology_eq_bot_of_cdp_lt (p := ℓ) M htors ?_
  calc cdp ℓ G ≤ 2 := hcd ℓ hℓ hℓn
    _ < r := by exact_mod_cast (show 2 < r by omega)

end Abstract

section Global

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1)))

instance isDiscreteRep_galRootsOfUnity_gs (m : ℕ) :
    IsDiscreteRep (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) m) :=
  isDiscreteRep_galRootsOfUnity m

instance isDiscreteRep_res_galRootsOfUnity_gs (m : ℕ) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    IsDiscreteRep (Rep.res U.subtype (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) m)) :=
  isDiscreteRep_res_subtype _ U

theorem nonempty_zmod_addEquiv_rootsOfUnity_gs {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    Nonempty (ZMod ℓ ≃+ Additive (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))) := by
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℚ̄ ℓ
  have hmem : ζ ∈ maxUnramifiedOutside K.1 ℚ̄ S :=
    mem_maxUnramifiedOutside_of_pow_eq_one S hℓ.ne_zero (fun v hv h => hv (hS v h)) hζ.pow_eq_one
  have hζ' : IsPrimitiveRoot (⟨ζ, hmem⟩ : maxUnramifiedOutside K.1 ℚ̄ S) ℓ :=
    IsPrimitiveRoot.of_map_of_injective (f := (maxUnramifiedOutside K.1 ℚ̄ S).val) hζ
      (maxUnramifiedOutside K.1 ℚ̄ S).val.toRingHom.injective
  have hcard := hζ'.card_rootsOfUnity
  have : Finite (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ.ne_zero)
  have : Nontrivial (rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hcard]; exact hℓ.one_lt)
  obtain ⟨η, hη⟩ := exists_ne (1 : rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S))
  have hη0 : Additive.ofMul η ≠ 0 := hη
  have hηp : ℓ • Additive.ofMul η = 0 := by
    have h := pow_card_eq_one' (G := rootsOfUnity ℓ (maxUnramifiedOutside K.1 ℚ̄ S)) (x := η)
    rw [hcard] at h
    rw [← ofMul_pow, h]
    rfl
  exact ⟨AddEquiv.ofBijective _ ((zmod_lift_zmultiplesHom_injective hη0 hηp).bijective_of_nat_card_le
    (by rw [Nat.card_zmod, Nat.card_congr Additive.ofMul.symm, hcard]))⟩

variable {ℓ : ℕ} (hℓ : ℓ.Prime)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem subsingleton_h3_rootsOfUnity (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1) :
    Subsingleton (cohomology (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) 3) :=
  ⟨fun x y => (eq_zero_h3_rootsOfUnity_of_h3_sUnits K S ℓ hℓ hS hK
    (fun z hz => eq_zero_of_h3_sUnits K S ℓ hℓ hS z 1 (by rwa [pow_one])) x).trans
    (eq_zero_h3_rootsOfUnity_of_h3_sUnits K S ℓ hℓ hS hK
      (fun z hz => eq_zero_of_h3_sUnits K S ℓ hℓ hS z 1 (by rwa [pow_one])) y).symm⟩

include hℓ hS in

theorem subsingleton_h3_res_rootsOfUnity (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ)) 3) := by
  obtain ⟨L, hKL, hL, rfl⟩ := exists_gsOpenSubgroup_eq K S U
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hKL' : ℓ ≠ 2 ∨ IsTotallyComplex L.1 :=
    hK.imp id fun h => by
      have := h
      exact isTotallyComplex_of_algebra K.1 L.1
  have := subsingleton_h3_rootsOfUnity L (placesOver S) hℓ hSL hKL'
  exact ((gsRootsOfUnityCohomologyIso S hL ℓ 3).toLinearEquiv.toEquiv.symm).subsingleton

include hℓ hS in

theorem cdp_galUnramifiedOutside_le_two (hK : ℓ ≠ 2 ∨ IsTotallyComplex K.1) :
    cdp ℓ (galUnramifiedOutside K.1 ℚ̄ S) ≤ 2 := by
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity_gs K S hℓ hS
  exact cdp_le_of_forall_openSubgroup hℓ (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) ℓ) e 2
    (subsingleton_h3_res_rootsOfUnity K S hℓ hS hK)

end Global

section Vanishing

variable (K : FiniteSubfield) (S : Set (HeightOneSpectrum (𝓞 K.1))) {n : ℕ} (hn : n ≠ 0)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hK : Odd n ∨ IsTotallyComplex K.1)

include hn hS hK in

theorem cdp_galUnramifiedOutside_le_two_of_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓn : ℓ ∣ n) :
    cdp ℓ (galUnramifiedOutside K.1 ℚ̄ S) ≤ 2 := by
  refine cdp_galUnramifiedOutside_le_two K S hℓ (fun v hv => hS v ?_) ?_
  · obtain ⟨c, hc⟩ := hℓn
    rw [hc, Nat.cast_mul]
    exact v.asIdeal.mul_mem_right _ hv
  · refine hK.imp (fun ho h2 => ?_) id
    rw [h2] at hℓn
    exact (Nat.not_even_iff_odd.2 ho) (even_iff_two_dvd.2 hℓn)

include hn hS hK in

theorem subsingleton_cohomology_gs_of_three_le (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (M : Rep.{0} (ULift.{0} ℤ) (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S))) [IsDiscreteRep M]
    (hM : ∀ m : M, n • m = 0) {r : ℕ} (hr : 3 ≤ r) : Subsingleton (cohomology M r) :=
  subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ hℓn =>
    (cdp_openSubgroup_le ℓ U).trans (cdp_galUnramifiedOutside_le_two_of_dvd K S hn hS hK hℓ hℓn)) M hM hr

include hn hS hK in

theorem subsingleton_h3_res_rootsOfUnity_of_odd (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) :
    Subsingleton (cohomology (Rep.res (U : Subgroup (galUnramifiedOutside K.1 ℚ̄ S)).subtype
      (galRootsOfUnity.{0} K.1 (maxUnramifiedOutside K.1 ℚ̄ S) n)) 3) :=
  subsingleton_cohomology_gs_of_three_le K S hn hS hK U _
    (fun m => nsmul_rootsOfUnity_eq_zero (E := maxUnramifiedOutside K.1 ℚ̄ S) n m) le_rfl

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

set_option maxHeartbeats 2000000 in
include hn hS hK in

theorem subsingleton_compactCohomology_four (M : Rep.{0} (ULift.{0} ℤ) (galUnramifiedOutside K.1 ℚ̄ S))
    [IsDiscreteRep M] (hM : ∀ m : M, n • m = 0) :
    Subsingleton (compactCohomologyRes (gsFinFamily S ιs) M 4) := by
  suffices h : ∀ x : compactCohomologyRes (gsFinFamily S ιs) M 4, x = 0 from
    ⟨fun x y => (h x).trans (h y).symm⟩
  intro x
  have hglob : Subsingleton (cohomology M 4) :=
    subsingleton_cohomology_of_cdp_le_two hn
      (fun ℓ hℓ hℓn => cdp_galUnramifiedOutside_le_two_of_dvd K S hn hS hK hℓ hℓn) M hM (by norm_num)
  have hloc : ∀ v : S, Subsingleton (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 3) := by
    intro v
    refine subsingleton_cohomology_of_cdp_le_two hn (fun ℓ hℓ _ => ?_)
      (Rep.res (gsFinFamily S ιs v).toMonoidHom M) (fun m => hM m) le_rfl
    refine cdp_galois_le_two _ _ hℓ ?_
    exact_mod_cast hℓ.ne_zero
  obtain ⟨y, rfl⟩ := (ShortComplex.moduleCat_exact_iff _).1
    (compactCohomology_exact_compact (gsFinFamily S ιs) M _ (fun _ => 𝟙 _) 3) x
    (Subsingleton.elim _ _)
  have : Subsingleton (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom M) 3) :=
    Pi.instSubsingleton
  rw [Subsingleton.elim y 0, map_zero]

end Vanishing

end

end GroundTheory.ProfCoh
end
