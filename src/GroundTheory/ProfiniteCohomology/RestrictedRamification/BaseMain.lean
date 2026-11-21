import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLevel
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseFixed
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseLocal
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Dimension
import GroundTheory.ProfiniteCohomology.RestrictedRamification.Finite
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseCores
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BasePairing

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

theorem finite_of_exact_of_finite {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Finite A]
    [Finite C] (g : A →+ B) (f : B →+ C) (hex : ∀ b, f b = 0 → ∃ a, g a = b) : Finite B := by
  rw [f.finite_iff_finite_ker_range]
  refine ⟨?_, inferInstance⟩
  have hsub : (f.ker : Set B) ⊆ Set.range g := fun b hb => hex b hb
  exact ((Set.finite_range g).subset hsub).to_subtype

theorem exists_natCast_mem_place (K : FiniteSubfield) {ℓ : ℕ} (hℓ : ℓ.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal := by
  have hnu : ¬ IsUnit ((ℓ : ℕ) : 𝓞 K.1) := by
    rintro ⟨u, hu⟩
    have h : ((ℓ : ℕ) : 𝓞 K.1) * ((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) = 1 := by
      rw [← hu]
      exact u.mul_inv
    have hK : ((ℓ : ℕ) : K.1) * (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = 1 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) h
      rwa [map_mul, map_natCast, map_one] at this
    have hint : IsIntegral ℤ (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) :=
      NumberField.RingOfIntegers.isIntegral_coe _
    have heq : (((u⁻¹ : (𝓞 K.1)ˣ) : 𝓞 K.1) : K.1) = algebraMap ℚ K.1 (1 / ℓ) := by
      rw [eq_inv_of_mul_eq_one_right hK]
      simp
    rw [heq, isIntegral_algebraMap_iff (algebraMap ℚ K.1).injective] at hint
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
    have hℓ0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hy' : ((ℓ * y : ℤ) : ℚ) = 1 := by
      rw [Int.cast_mul, show ((y : ℤ) : ℚ) = algebraMap ℤ ℚ y from rfl, hy]
      field_simp
      norm_cast
    have h2 : (ℓ : ℤ) * y = 1 := by exact_mod_cast hy'
    have hunit := Int.eq_one_or_neg_one_of_mul_eq_one h2
    have hℓ1 : (ℓ : ℤ) ≠ 1 := by exact_mod_cast hℓ.one_lt.ne'
    have hℓm : (ℓ : ℤ) ≠ -1 := by omega
    exact hunit.elim hℓ1 hℓm
  have hne : Ideal.span {((ℓ : ℕ) : 𝓞 K.1)} ≠ ⊤ := fun h => hnu (Ideal.span_singleton_eq_top.1 h)
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
  have hℓM : ((ℓ : ℕ) : 𝓞 K.1) ∈ M := hle (Ideal.subset_span rfl)
  have hMbot : M ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hℓM
    have : ((ℓ : ℕ) : K.1) = 0 := by
      have := congrArg (algebraMap (𝓞 K.1) K.1) hℓM
      rwa [map_natCast, map_zero] at this
    exact hℓ.ne_zero (by exact_mod_cast this)
  exact ⟨⟨M, hM.isPrime, hMbot⟩, hℓM⟩

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) (n ℓ k : ℕ) (hℓ : ℓ.Prime)
  (hnk : n = ℓ ^ k) (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)

include hℓ hS in

theorem nonempty_of_natCast_mem : Nonempty S :=
  (exists_natCast_mem_place K hℓ).elim fun v hv => ⟨⟨v, hS v hv⟩⟩

include hnk hS in

theorem mem_of_natCast_pow_mem : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S := by
  intro v hv
  subst hnk
  rw [Nat.cast_pow] at hv
  exact hS v (v.isPrime.mem_of_pow_mem k hv)

variable [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1)

include hnk hS hodd in

theorem subsingleton_gsRoots_three : Subsingleton (cohomology (gsRoots S n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (gsRoots S n) (nsmul_gsRoots S n) le_rfl

include hnk hS hodd in

theorem subsingleton_zmodRep_gs_three :
    Subsingleton (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 3) :=
  subsingleton_cohomology_of_cdp_le_two (NeZero.ne n)
    (fun _ hp hpn => cdp_galUnramifiedOutside_le_two_of_dvd K S (NeZero.ne n)
      (mem_of_natCast_pow_mem S n ℓ k hnk hS) hodd hp hpn) (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n)
    (nsmul_zmodRep_eq_zero _ n) le_rfl

omit [NeZero n] in
theorem natCard_zmodRep (G : Type) [Group G] : Nat.card (zmodRep.{0} G n) = n := by
  change Nat.card (ULift.{0} (ZMod n)) = n
  rw [Nat.card_ulift, Nat.card_zmod]

variable [Finite S]

include hnk hS in

theorem finite_zmodRep_gs_one : Finite (cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1) := by
  have : Finite (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) := inferInstanceAs (Finite (ULift.{0} (ZMod n)))
  refine finite_cohomology_gs K S _ (fun v hv => ?_) 1 (by norm_num)
  rw [natCard_zmodRep] at hv
  exact mem_of_natCast_pow_mem S n ℓ k hnk hS v hv

variable (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))

omit [Finite S] in
include hnk hS in

theorem natCard_gsRoots : Nat.card (gsRoots S n) = n := by
  change Nat.card (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))) = n
  rw [Nat.card_congr Additive.toMul]
  exact card_rootsOfUnity_maxUnramifiedOutside K S n (NeZero.ne n)
    (fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h))

omit [Finite S] in
include hnk hS in

theorem finite_gsRoots_local_one (v : S) :
    Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) := by
  have : Finite (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) :=
    inferInstanceAs (Finite (Additive (rootsOfUnity n (maxUnramifiedOutside K.1 ℚ̄ S))))
  refine finite_cohomology_localField _ ?_ 1
  change ((Nat.card (gsRoots S n) : ℕ) : (v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1) ≠ 0
  rw [natCard_gsRoots S n ℓ k hnk hS]
  exact Nat.cast_ne_zero.2 (NeZero.ne n)

include hnk hS in

theorem finite_gsRoots_compact_two [Fintype S] :
    Finite (compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2) := by
  have : ∀ v : S, Finite (cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1) :=
    finite_gsRoots_local_one S n ℓ k hnk hS ιs
  have hA : Finite (ModuleCat.of (ULift.{0} ℤ)
      (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1)) :=
    inferInstanceAs (Finite (∀ v : S, cohomology (Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n)) 1))
  have hC : Finite (cohomology (gsRoots S n) 2) :=
    finite_cohomology_rootsOfUnity K S n (NeZero.ne n) (mem_of_natCast_pow_mem S n ℓ k hnk hS) 2 le_rfl
  exact finite_of_exact_of_finite
    (localToCompact (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 1).hom.toAddMonoidHom
    (compactToGlobal (gsFinFamily S ιs) (gsRoots S n) (fun v => Rep.res (gsFinFamily S ιs v).toMonoidHom (gsRoots S n))
      (fun _ => 𝟙 _) 2).hom.toAddMonoidHom
    (fun b hb => (ShortComplex.moduleCat_exact_iff_ker_sub_range _).1
      (compactCohomology_exact_compact (gsFinFamily S ιs) (gsRoots S n) _ (fun _ => 𝟙 _) 1) hb)

end

section PlacesOver

variable {K L : FiniteSubfield} [Fact (K ≤ L)] (S : Set (HeightOneSpectrum (𝓞 K.1)))

@[instance_reducible]
noncomputable def fintypePlacesOver [Finite S] : Fintype (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  (placesOver_finite (Set.toFinite S)).fintype

theorem nonempty_placesOver_of_natCast_mem {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S) :
    Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
  nonempty_of_natCast_mem (placesOver S) ℓ hℓ fun _ hw => mem_placesOver_of_natCast_mem hS hw

end PlacesOver

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Local

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1)))
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hnS : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal)
include hnS

set_option maxHeartbeats 1600000 in

theorem bijective_gsRootsLocalMor_of_places (v : S) : Function.Bijective (gsRootsLocalMor S ιs n v).hom :=
  (exists_isPrimitiveRoot_maxUnramifiedOutside K S n (NeZero.ne n) hnS).elim fun _ hz =>
    Additive.ofMul.bijective.comp ((bijective_rootsOfUnityMapHom n
      ((ιs v).comp (maxUnramifiedOutside K.1 ℚ̄ S).val).toRingHom hz).comp Additive.toMul.bijective)

theorem bijective_gsLocalInvRoots_of_places (v : S) : Function.Bijective (gsLocalInvRoots S ιs n v) := by
  have e : ⇑(gsLocalInvRoots S ιs n v) =
      (localDualityHypotheses (Ksep := AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
        (natCast_ne_zero_adicCompletion S n v)).tTop ∘ (cohomologyMap (gsRootsLocalMor S ιs n v) 2).hom :=
    funext (gsLocalInvRoots_eq S ιs n v)
  rw [e]
  exact (bijective_localDualityHypotheses_tTop S n v).comp
    (bijective_cohomologyMap_of_bijective _ (bijective_gsRootsLocalMor_of_places S ιs n hnS v) 2)

end Local

section P1

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1)) (n : ℕ)
  [NeZero n] (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingNondegenerate : Prop :=
  (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
      (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → x = 0) ∧
    (∀ y : compactCohomologyRes (gsFinFamily S ιs) (gsRoots S n) 2,
      (∀ x : cohomology (zmodRep.{0} (galUnramifiedOutside K.1 ℚ̄ S) n) 1,
        gsCompactInv S ιs n hodd h3 (compactCupRes (gsFinFamily S ιs) (zmodMulPairingRight n (gsRoots S n)
          (nsmul_gsRoots S n)) (show 2 + 1 = 3 from rfl) y x) = 0) → y = 0)

end P1

section Level

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

def GsPairingInput (n ℓ : ℕ) [NeZero n] : Prop :=
  ∀ (L : FiniteSubfield) (S' : Set (HeightOneSpectrum (𝓞 L.1))) [Fintype S']
    (ιs' : ∀ v : S', ℚ̄ →ₐ[L.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 L.1)).adicCompletion L.1)),
    (∀ v : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ v.asIdeal → v ∈ S') →
    (∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1) → ∀ (hodd' : Odd n ∨ IsTotallyComplex L.1)
    (h3' : Subsingleton (cohomology (gsRoots S' n) 3)), GsPairingNondegenerate S' ιs' n hodd' h3'

omit [Fintype S] [NeZero n] in
include hnk hS in

theorem natCast_not_mem_of_not_mem : ∀ v ∉ S, ((n : ℕ) : 𝓞 K.1) ∉ v.asIdeal :=
  fun v hv h => hv (mem_of_natCast_pow_mem S n ℓ k hnk hS v h)

set_option maxHeartbeats 3200000 in
include hℓ hnk hS in

theorem gsBaseBijective_of_le (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    {L : FiniteSubfield} [Fact (K ≤ L)] (hL : ∀ x : L.1, algebraMap L.1 ℚ̄ x ∈ maxUnramifiedOutside K.1 ℚ̄ S)
    (hUW : gsOpenSubgroup S hL ≤ W₀) :
    GsBaseBijective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have : Nonempty S := nonempty_of_natCast_mem S ℓ hℓ hS
  let := fintypePlacesOver (L := L) S
  have : Nonempty (placesOver S : Set (HeightOneSpectrum (𝓞 L.1))) :=
    nonempty_placesOver_of_natCast_mem S hℓ hS
  have hSL : ∀ w : HeightOneSpectrum (𝓞 L.1), ((ℓ : ℕ) : 𝓞 L.1) ∈ w.asIdeal → w ∈ placesOver S :=
    fun w hw => mem_placesOver_of_natCast_mem hS hw
  have hμL : ∀ ζ : ℚ̄, ζ ^ n = 1 → ζ ∈ L.1 :=
    rootsOfUnity_mem_of_gsOpenSubgroup_le S n hL W₀ hW₀ hUW (NeZero.ne n) hnS
  have hoddL : Odd n ∨ IsTotallyComplex L.1 := hodd.imp id fun h => by
    have := h
    exact isTotallyComplex_of_algebra K.1 L.1
  have h3L := subsingleton_gsRoots_three (placesOver S) n ℓ k hnk hSL hoddL
  have hPL := hP L (placesOver S) (gsMackeyEmbeddings hL ιs) hSL hμL hoddL h3L
  have hsurj : GsCoresSurjective S ιs n (gsOpenSubgroup S hL) (gsCompactInv S ιs n hodd h3) :=
    (surjective_gsCompactInv S n ιs hodd h3 fun v =>
      (bijective_gsLocalInvRoots_of_places S ιs n hnS v).2).comp (hcores _)
  intro r s h
  exact bijective_zmodCompactDualityMap_gsOpenSubgroup S ιs hL n _
    (gsCompactInv (placesOver S) (gsMackeyEmbeddings hL ιs) n hoddL h3L)
    ⟨bijective_gsCompactInv_of_mem (placesOver S) n (gsMackeyEmbeddings hL ιs) ℓ k hℓ hnk hSL hμL hoddL h3L,
      fun h => bijective_gs_compactZmodDualityMap (placesOver S) (gsMackeyEmbeddings hL ιs) n ℓ k hℓ hnk hSL hμL
        hoddL h3L (subsingleton_zmodRep_gs_three (placesOver S) n ℓ k hnk hSL hoddL)
        (finite_zmodRep_gs_one (placesOver S) n ℓ k hnk hSL)
        (finite_gsRoots_compact_two (placesOver S) n ℓ k hnk hSL (gsMackeyEmbeddings hL ιs)) hPL.1 hPL.2 h⟩ hsurj h

end Level

end

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IsDedekindDomain NumberField CategoryTheory GroundTheory.Global

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

variable {K : FiniteSubfield} (S : Set (HeightOneSpectrum (𝓞 K.1))) [Fintype S]
  (ιs : ∀ v : S, ℚ̄ →ₐ[K.1] AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K.1)).adicCompletion K.1))
  (n ℓ k : ℕ) [NeZero n] (hℓ : ℓ.Prime) (hnk : n = ℓ ^ k)
  (hS : ∀ v : HeightOneSpectrum (𝓞 K.1), ((ℓ : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S)
  (hodd : Odd n ∨ IsTotallyComplex K.1) (h3 : Subsingleton (cohomology (gsRoots S n) 3))

include hℓ hnk hS in

theorem gsBaseBijective_of_fixing (hP : GsPairingInput n ℓ)
    (hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom)
    (W₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S))
    (hW₀ : ∀ σ ∈ W₀, ∀ ζ : (maxUnramifiedOutside K.1 ℚ̄ S)ˣ, ζ ^ n = 1 →
      σ (ζ : maxUnramifiedOutside K.1 ℚ̄ S) = ζ)
    (U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S)) (hU : U ≤ W₀) :
    GsBaseBijective S ιs n U (gsCompactInv S ιs n hodd h3) :=
  (exists_gsOpenSubgroup_eq K S U).elim fun _ h1 => h1.elim fun _ h2 => h2.elim fun hL hUeq =>
    hUeq ▸ gsBaseBijective_of_le S ιs n ℓ k hℓ hnk hS hodd h3 hP hcores W₀ hW₀ hL (hUeq ▸ hU)

set_option maxHeartbeats 1600000 in
include hℓ hnk hS in

theorem exists_compactDualityHypotheses_gs_of_pairing (hP : GsPairingInput n ℓ) :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ := by
  have hnS := natCast_not_mem_of_not_mem S n ℓ k hnk hS
  have hSn : ∀ v : HeightOneSpectrum (𝓞 K.1), ((n : ℕ) : 𝓞 K.1) ∈ v.asIdeal → v ∈ S :=
    mem_of_natCast_pow_mem S n ℓ k hnk hS
  have hD := nonempty_addEquiv_gsRoots_of_places S n hnS
  have : Finite (gsRoots S n) := hD.elim fun e => Finite.of_equiv _ e.toEquiv.symm
  have hcores : ∀ U : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      Function.Surjective (compactCores (gsFinFamily S ιs) U (gsRoots S n) 3).hom := fun U =>
    surjective_gs_compactCores_three K S ιs (NeZero.ne n) hSn hodd U (gsRoots S n) (nsmul_gsRoots S n)
  exact (exists_openSubgroup_fixing_rootsOfUnity K S n (NeZero.ne n)).elim fun W₀ hW₀ => ⟨W₀,
    { nonempty_addEquiv := hD
      subsingleton_four := fun M _ _ hM => subsingleton_compactCohomology_four K S (NeZero.ne n) hSn hodd ιs M hM
      bijective_base := fun U hU {r s} h => gsBaseBijective_of_fixing S ιs n ℓ k hℓ hnk hS hodd h3 hP hcores W₀ hW₀
        U hU h }⟩

include hℓ hnk in

theorem gsPairingInput : GsPairingInput n ℓ := fun _ S' _ ιs' hS' _ hodd' h3' =>
  ⟨gsCompactInv_ker_left S' ιs' n ℓ k hℓ hnk hS' hodd' h3', gsCompactInv_ker_right S' ιs' n ℓ k hℓ hnk hS' hodd' h3'⟩

include hℓ hnk hS in

theorem exists_compactDualityHypotheses_gs :
    ∃ U₀ : OpenSubgroup (galUnramifiedOutside K.1 ℚ̄ S),
      CompactDualityHypotheses (gsFinFamily S ιs) n (gsRoots S n) (gsCompactInv S ιs n hodd h3) U₀ :=
  exists_compactDualityHypotheses_gs_of_pairing S ιs n ℓ k hℓ hnk hS hodd h3 (gsPairingInput n ℓ k hℓ hnk)

end

end GroundTheory.ProfCoh
end
