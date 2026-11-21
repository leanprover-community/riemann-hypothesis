import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.GroupStep
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGen
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsOpenNormalFiniteIndexLeAbsGaloisGroupStatement
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.RootMod
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.FreshChar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormalOfComm
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionAbelianCompletion
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsAbelianOverSubfield
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TransferEqOfIsOpenKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ValuationLeOneOfInteger
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NonsplitOfSqrtConductor
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ExistsPlaceOfPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinitePlacesInertiaNotLeOpenSubgroup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.DecGen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ConjOfSqNonneg
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.PrimeWith
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.TwoPrimes
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.IsSplitAtOfDecompositionLeRestrictionRange
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.ThreeApartOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.Double
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.QuadraticCharTwistOfExistsOfInfinity
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatakeStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BaseChangeIsomorphicFields
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.FormsFiniteGL

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.powChar :
    PowChar := by
  intro p _ n hn hdvd
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units]
  have hog : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  obtain ⟨ω, hωc⟩ := hprim.isUnit hn.ne'
  have hωp : IsPrimitiveRoot ω n := by
    rw [← IsPrimitiveRoot.coe_units_iff, hωc]
    exact hprim
  have hωo : orderOf ω = n := hωp.eq_orderOf.symm
  have hnd : n ∣ p - 1 := Dvd.dvd.trans (Dvd.intro_left 2 rfl) hdvd
  have hd : orderOf ω ∣ orderOf g := by rw [hωo, hog]; exact hnd
  let lam : (ZMod p)ˣ →* ℂˣ := monoidHomOfForallMemZpowers hg hd
  have hlg : lam g = ω := monoidHomOfForallMemZpowers_apply_gen hg hd
  have hωn : ω ^ n = 1 := hωp.pow_eq_one
  have hpow : ∀ a, (lam a) ^ n = 1 := by
    intro a
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
    rw [map_zpow, hlg, ← zpow_natCast, zpow_comm, zpow_natCast, hωn, one_zpow]
  refine ⟨lam, ?_, ?_, ?_⟩
  · ext1 a
    rw [MonoidHom.pow_apply, hpow, MonoidHom.one_apply]
  · obtain ⟨c, hc⟩ := hdvd
    have hcpos : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h
        omega
      · exact h
    have hx2 : (g ^ (n * c)) ^ 2 = 1 := by
      rw [← pow_mul, show n * c * 2 = p - 1 by rw [hc]; ring, ← hog, pow_orderOf_eq_one]
    have hx1 : g ^ (n * c) ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hog, hc] at h1
      have h2 := Nat.le_of_dvd (Nat.mul_pos hn hcpos) h1
      have h3 : 0 < n * c := Nat.mul_pos hn hcpos
      nlinarith
    have hxm : g ^ (n * c) = -1 := by
      have h4 : (((g ^ (n * c) : (ZMod p)ˣ)) : ZMod p) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, hx2, Units.val_one]
      rw [sq] at h4
      rcases mul_self_eq_one_iff.mp h4 with h | h
      · exact absurd (Units.ext (by rw [h, Units.val_one])) hx1
      · exact Units.ext (by rw [h, Units.val_neg, Units.val_one])
    rw [← hxm, map_pow, hlg, pow_mul, hωn, one_pow]
  · intro a ha
    have htop : Subgroup.zpowers a = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, ha, hcard]
    have hga : g ∈ Subgroup.zpowers a := by rw [htop]; trivial
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hga
    have hωa : (lam a) ^ j = ω := by rw [← map_zpow, hlg]
    apply Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (hpow a))
    rw [← hωo]
    apply orderOf_dvd_of_pow_eq_one
    rw [← hωa, ← zpow_natCast, zpow_comm, zpow_natCast, pow_orderOf_eq_one, one_zpow]
end

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem decPow : DecPow := by
  intro F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ
  have hN : ¬ A.valuation (p : Ω) < 1 := by
    simpa using not_valuation_lt_one_of_isPlaceOver hpt hA 1
  have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
  have hint : ζ ∈ IntCl F Ω :=
    IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)
  have hv : A.valuation ζ ≤ 1 := by
    have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
    exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_pow_cong hA hg {⟨ζ, hint⟩}
    refine ⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩
    · rw [← map_pow, hz1, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
  · exact eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem norm_not_mem_sq {F : Type} [Field F] [NumberField F] (u : HeightOneSpectrum (𝓞 F))
    (hd : u.asIdeal.inertiaDeg ℤ = 1) (he : u.asIdeal.ramificationIdx ℤ = 1) :
    ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 F) ∉ u.asIdeal ^ 2 := by
  classical
  have hprime : Nat.Prime (Ideal.absNorm u.asIdeal) :=
    ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 u).2 hd
  haveI : Fact (Nat.Prime (Ideal.absNorm u.asIdeal)) := ⟨hprime⟩
  have hmemZ : ((Ideal.absNorm u.asIdeal : ℕ) : ℤ) ∈ u.asIdeal.under ℤ := by
    rw [Ideal.under_def, Ideal.mem_comap]
    simpa using Ideal.absNorm_mem u.asIdeal
  have hspan : u.asIdeal.under ℤ = Ideal.span {((Ideal.absNorm u.asIdeal : ℕ) : ℤ)} :=
    ((Int.ideal_span_isMaximal_of_prime (Ideal.absNorm u.asIdeal)).eq_of_le
      Ideal.IsPrime.ne_top' ((Ideal.span_singleton_le_iff_mem _).2 hmemZ)).symm
  have hp0 : u.asIdeal.under ℤ ≠ ⊥ := by
    rw [hspan, Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hprime.ne_zero
  have he' : (u.asIdeal.under ℤ).ramificationIdx' u.asIdeal = 1 := by
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (u.asIdeal.under ℤ) u.asIdeal hp0]
    exact he
  have hmap : (u.asIdeal.under ℤ).map (algebraMap ℤ (𝓞 F)) ≤ u.asIdeal := Ideal.map_comap_le
  intro hmem
  refine (Ideal.ramificationIdx'_ne_one_iff hmap).2 ?_ he'
  rw [hspan, Ideal.map_span, Ideal.span_le, Set.image_singleton, Set.singleton_subset_iff]
  simpa using hmem

private theorem dec_le {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    {N : Subgroup (G F Ω)} (hNo : IsOpen (N : Set (G F Ω))) {B : ValuationSubring Ω}
    {u : HeightOneSpectrum (𝓞 F)} (hB : IsPlaceOver B u) (hI : Ine (F := F) B ≤ N) {σ : G F Ω}
    (hσ : IsFrob B (normV u) σ) (hσN : σ ∈ N) : Dec (F := F) B ≤ N := by
  intro d hd
  have h := GlobalTheory.TameQuot.closure_frob_sup_Ine F Ω B u hB ⟨σ, hσ.1⟩ hσ
  have hc : IsClosed ((N.subgroupOf (Dec (F := F) B) : Subgroup (Dec (F := F) B)) : Set (Dec (F := F) B)) :=
    (N.isClosed_of_isOpen hNo).preimage continuous_subtype_val
  have h2 := Subgroup.topologicalClosure_minimal
    (Subgroup.zpowers (⟨σ, hσ.1⟩ : Dec (F := F) B) ⊔ (Ine (F := F) B).subgroupOf (Dec (F := F) B))
    (sup_le (Subgroup.zpowers_le.2 (Subgroup.mem_subgroupOf.2 hσN))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hI (Subgroup.mem_subgroupOf.1 hx)))) hc
  rw [h] at h2
  exact Subgroup.mem_subgroupOf.1 (h2 (Subgroup.mem_top (⟨d, hd⟩ : Dec (F := F) B)))

theorem splitPlace : SplitPlace := by
  intro F Ω _ _ _ _ _ U hU T hT
  obtain ⟨N, hNn, hNo, -, hNU⟩ := GlobalTheory.T.exists_openNormal_finiteIndex_le_absGaloisGroup Ω F U hU
  have hc : GlobalTheory.TwSys.Cheb :=
    GlobalTheory.Published.chebotarevDegreeOne_iff_cheb.1 GlobalTheory.Published.chebotarevDegreeOne'
  unfold GlobalTheory.TwSys.Cheb at hc
  obtain ⟨v, hvA, hd, he, B, hB, hIB, σ, hσ, hσN⟩ := hc F Ω N hNo hNn 1 hT.toFinset
  have hvT : v ∉ T := fun h => hvA (hT.mem_toFinset.2 h)
  have hσN' : σ ∈ N := by simpa using hσN
  have hdec := dec_le hNo hB hIB hσ hσN'
  have hnorm : normV v = Ideal.absNorm v.asIdeal := by
    simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  refine ⟨v, hvT, ?_, ?_, ?_, ?_⟩
  · rw [hnorm]
    exact ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified F).1 v).2 hd
  · rw [hnorm]
    exact Ideal.absNorm_mem _
  · rw [hnorm]
    exact norm_not_mem_sq v hd he
  · intro A hA ρ hρ
    obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hB hA
    apply hNU
    have h1 : τ⁻¹ * ρ * τ ∈ Dec (F := F) B := by
      rw [mem_Dec] at hρ ⊢
      rw [← hτ] at hρ
      rw [mul_smul, mul_smul, hρ, ← mul_smul, inv_mul_cancel, one_smul]
    have h2 := hNn.conj_mem _ (hdec h1) τ
    simpa [mul_assoc] using h2

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private lemma normV_pos' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) : 0 < normV t := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show 0 < Nat.card (𝓞 F ⧸ t.asIdeal)
  rw [h]
  exact Nat.pos_of_ne_zero (fun h0 => t.ne_bot (Ideal.absNorm_eq_zero_iff.mp h0))

private lemma normV_mem' {F : Type} [Field F] [NumberField F] (t : HeightOneSpectrum (𝓞 F)) :
    ((normV t : ℕ) : 𝓞 F) ∈ t.asIdeal := by
  have h : Nat.card (𝓞 F ⧸ t.asIdeal) = Ideal.absNorm t.asIdeal := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  show ((Nat.card (𝓞 F ⧸ t.asIdeal) : ℕ) : 𝓞 F) ∈ t.asIdeal
  rw [h]
  exact Ideal.absNorm_mem _

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.freshPrime :
    SplitPlace → RootMod → FreshPrime := by
  intro hS hR
  unfold SplitPlace at hS
  unfold RootMod at hR
  unfold FreshPrime
  intro F Ω _ _ _ _ _ U hU T hT n hn
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (((2 * n : ℕ)) : Ω) := ⟨by exact_mod_cast (by omega : 2 * n ≠ 0)⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (2 * n)
  have hroot : ∀ t : HeightOneSpectrum (𝓞 F), ∃ x : Ω, x ^ n = (normV t : Ω) :=
    fun t => IsAlgClosed.exists_pow_nat_eq _ hn
  choose y hy using hroot
  set S : Set Ω := insert ζ (y '' T) with hSeq
  haveI : Finite S := (Set.Finite.insert ζ (hT.image y)).to_subtype
  haveI : FiniteDimensional F (IntermediateField.adjoin F S) :=
    IntermediateField.finiteDimensional_adjoin
      (fun x _ => (Algebra.IsAlgebraic.isAlgebraic (R := F) x).isIntegral)
  set U' : Subgroup (G F Ω) := U ⊓ (IntermediateField.adjoin F S).fixingSubgroup with hU'eq
  have hU' : IsOpen (U' : Set (G F Ω)) := by
    rw [hU'eq, Subgroup.coe_inf]
    exact hU.inter (IntermediateField.fixingSubgroup_isOpen _)
  have hfix : ∀ g : G F Ω, g ∈ U' → ∀ x ∈ S, (g : Ω → Ω) x = x := by
    intro g hg x hx
    have hg2 := (Subgroup.mem_inf.mp hg).2
    exact (mem_fixingSubgroup_iff _).mp hg2 x (IntermediateField.subset_adjoin F S hx)
  have hfinset : ∀ a : 𝓞 F, a ≠ 0 → {w : HeightOneSpectrum (𝓞 F) | a ∈ w.asIdeal}.Finite := by
    intro a ha
    have h0 : Ideal.span {a} ≠ (0 : Ideal (𝓞 F)) := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact ha
    simpa only [Ideal.dvd_span_singleton] using Ideal.finite_factors h0
  have hcast : ∀ m : ℕ, m ≠ 0 → ((m : ℕ) : 𝓞 F) ≠ 0 := fun m hm => by exact_mod_cast hm
  set B : Set (HeightOneSpectrum (𝓞 F)) :=
    T ∪ (⋃ t ∈ T, {w | ((normV t : ℕ) : 𝓞 F) ∈ w.asIdeal}) ∪ {w | ((2 * n : ℕ) : 𝓞 F) ∈ w.asIdeal}
    with hBeq
  have hB : B.Finite := by
    refine (hT.union (hT.biUnion fun t _ => hfinset _ (hcast _ (normV_pos' t).ne'))).union ?_
    exact hfinset _ (hcast _ (by omega))
  obtain ⟨u, huB, hp, hpu, hpu2, hdec⟩ := hS F Ω U' hU' B hB
  have hdvd_mem : ∀ m : ℕ, normV u ∣ m → ((m : ℕ) : 𝓞 F) ∈ u.asIdeal := by
    rintro m ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hpu
  obtain ⟨A, hA⟩ := exists_isPlaceOver Ω u
  have hDA : ∀ x ∈ S, ∀ g ∈ Dec A, (g : Ω → Ω) x = x := fun x hx g hg => hfix g (hdec A hA hg) x hx
  refine ⟨u, fun h => huB (Or.inl (Or.inl h)), hp, hpu, hpu2,
    fun A' hA' => le_trans (hdec A' hA') inf_le_left, ?_, ?_⟩
  · refine (hR F Ω A u hA (normV u) hp rfl ζ (2 * n) (by omega) (hDA ζ (Set.mem_insert _ _))).2 hζ ?_
    intro h2
    exact huB (Or.inr (hdvd_mem _ h2))
  · intro t ht
    refine ⟨?_, (hR F Ω A u hA (normV u) hp rfl (y t) n hn
      (hDA (y t) (Set.mem_insert_of_mem _ ⟨t, ht, rfl⟩))).1 (normV t) (hy t)⟩
    intro hut
    by_cases hd : normV u ∣ normV t
    · exact huB (Or.inl (Or.inr (Set.mem_biUnion ht (hdvd_mem _ hd))))
    · have hcop : Nat.Coprime (normV u) (normV t) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hd
      have hg := Nat.gcd_eq_gcd_ab (normV u) (normV t)
      rw [hcop] at hg
      have hg' := congrArg (Int.cast : ℤ → 𝓞 F) hg
      push_cast at hg'
      have h1 : (1 : 𝓞 F) ∈ t.asIdeal := by
        rw [hg']
        exact t.asIdeal.add_mem (Ideal.mul_mem_right _ _ hut) (Ideal.mul_mem_right _ _ (normV_mem' t))
      exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h1)
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.realSpan :
    RealSpan := by
  intro E M Ω F _ _ _ _ _ _ _ _ _ _ _ _ _ g hE hR
  have hnot : ∃ e : E, algebraMap E M e ∉ maximalRealSubfield M := by
    by_contra h
    push_neg at h
    obtain ⟨φ⟩ : Nonempty (M →+* ℂ) := inferInstance
    apply IsTotallyComplex.complexEmbedding_not_isReal (φ.comp (algebraMap E M))
    show ComplexEmbedding.conjugate _ = _
    ext x
    have := (mem_maximalRealSubfield_iff _).1 (h x) φ
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨e, he⟩ := hnot
  set α := algebraMap E M e with hα
  have h2 : Module.finrank (maximalRealSubfield M) M = 2 :=
    Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have htop : IntermediateField.adjoin (maximalRealSubfield M) {α} = ⊤ := by
    have hd := IntermediateField.finrank_dvd_of_le_right
      (le_top : IntermediateField.adjoin (maximalRealSubfield M) {α} ≤ ⊤)
    rw [IntermediateField.finrank_top', h2, Nat.dvd_prime Nat.prime_two] at hd
    rcases hd with hd | hd
    · rw [IntermediateField.finrank_eq_one_iff] at hd
      have hmem := IntermediateField.mem_adjoin_simple_self (maximalRealSubfield M) α
      rw [hd, IntermediateField.mem_bot] at hmem
      obtain ⟨y, hy⟩ := hmem
      exact absurd (hy ▸ y.2) he
    · exact IntermediateField.eq_of_le_of_finrank_eq le_top
        (by rw [hd, IntermediateField.finrank_top', h2])
  intro x
  have hx : x ∈ IntermediateField.adjoin (maximalRealSubfield M) {α} := by
    rw [htop]
    exact IntermediateField.mem_top
  have hx' : x ∈ (IntermediateField.adjoin (maximalRealSubfield M) {α}).toSubfield := hx
  rw [IntermediateField.adjoin_toSubfield] at hx'
  have hle : Subfield.closure (Set.range (algebraMap (maximalRealSubfield M) M) ∪ {α}) ≤
      RingHom.eqLocusField ((g : Ω →+* Ω).comp (algebraMap M Ω)) (algebraMap M Ω) := by
    rw [Subfield.closure_le]
    rintro y (⟨z, rfl⟩ | hy)
    · exact hR z
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      have h1 := hE e
      rw [IsScalarTower.algebraMap_apply E M Ω] at h1
      exact h1
  exact hle hx'
end

section
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem fixingSubgroup_fieldRange {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] (K : Type) [Field K]
    [Algebra E K] [Algebra K Ω] [IsScalarTower E K Ω] :
    (IsScalarTower.toAlgHom E K Ω).fieldRange.fixingSubgroup = fixGrp E Ω K := by
  ext g
  rw [mem_fixGrp, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

theorem inclOf : InclOf := by
  intro E Ω _ _ _ _ _ _ X Y hXY
  have hGal : IsGalois E Ω := inferInstance
  set f := IsScalarTower.toAlgHom E X.K Ω
  set g := IsScalarTower.toAlgHom E Y.K Ω
  have hX := fixingSubgroup_fieldRange (E := E) (Ω := Ω) X.K
  have hY := fixingSubgroup_fieldRange (E := E) (Ω := Ω) Y.K
  have hle : f.fieldRange ≤ g.fieldRange := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup f.fieldRange,
      ← InfiniteGalois.fixedField_fixingSubgroup g.fieldRange]
    apply IntermediateField.fixedField_le
    rw [hX, hY]
    exact hXY
  set eX := AlgEquiv.ofInjectiveField f
  set eY := AlgEquiv.ofInjectiveField g
  set φ : X.K →ₐ[E] Y.K := (eY.symm.toAlgHom.comp (IntermediateField.inclusion hle)).comp eX.toAlgHom
  have hφ : ∀ x : X.K, g (φ x) = f x := by
    intro x
    have h1 : (eY (φ x) : Ω) = g (φ x) := rfl
    rw [← h1]
    have h2 : eY (φ x) = IntermediateField.inclusion hle (eX x) := eY.apply_symm_apply _
    rw [h2]
    rfl
  letI alg : Algebra X.K Y.K := φ.toRingHom.toAlgebra
  have t1 : IsScalarTower E X.K Y.K := IsScalarTower.of_algebraMap_eq (fun a => (φ.commutes a).symm)
  have t2 : IsScalarTower X.K Y.K Ω := IsScalarTower.of_algebraMap_eq (fun x => (hφ x).symm)
  refine ⟨alg, t1, t2, IsGalois.tower_top_of_isGalois E X.K Y.K, ?_⟩
  rw [← hX, ← hY]
  have iX := IntermediateField.finrank_eq_fixingSubgroup_index Ω f.fieldRange
  have iY := IntermediateField.finrank_eq_fixingSubgroup_index Ω g.fieldRange
  have fX : Module.finrank E X.K = Module.finrank E f.fieldRange := eX.toLinearEquiv.finrank_eq
  have fY : Module.finrank E Y.K = Module.finrank E g.fieldRange := eY.toLinearEquiv.finrank_eq
  have tw := Module.finrank_mul_finrank E X.K Y.K
  have hsub : g.fieldRange.fixingSubgroup ≤ f.fieldRange.fixingSubgroup := by
    rw [hX, hY]; exact hXY
  have rel := Subgroup.relIndex_mul_index hsub
  haveI : FiniteDimensional E X.K := Module.Finite.of_restrictScalars_finite ℚ E X.K
  have hpos : 0 < Module.finrank E X.K := Module.finrank_pos
  rw [fX, iX] at tw hpos
  rw [fY, iY, ← rel] at tw
  exact Nat.eq_of_mul_eq_mul_right hpos (by rw [mul_comm] at tw; exact tw)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section
namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem indexComap : IndexComap := by
  intro Γ Γ' _ _ f H H' hc hle hp ⟨τ, hτ, hτ'⟩
  have hN : H'.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ * n⁻¹ ∈ H' :=
      hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))
    have h2 : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact H'.mul_mem h1 hn
  rw [Subgroup.relIndex_comap]
  set J := (H.comap f).map f with hJ
  have hJH : J ≤ H := Subgroup.map_comap_le _ _
  have hmul : H'.relIndex (H' ⊔ J) * (H' ⊔ J).relIndex H = H'.relIndex H :=
    Subgroup.relIndex_mul_relIndex _ _ _ le_sup_left (sup_le hle hJH)
  rw [Subgroup.relIndex_sup_left] at hmul
  have hne : H'.relIndex J ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    exact hτ' (h ⟨τ, hτ, rfl⟩)
  exact (hp.eq_one_or_self_of_dvd _ ⟨_, hmul.symm⟩).resolve_left hne

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.layerOf :
    InclOf → IndexComap → LayerOf := by
  intro hIncl hIdx
  unfold LayerOf
  intro E Ω _ _ _ _ _ _ S H H' hH' hle hp X Y hX hY u hS hDec hτex
  obtain ⟨A, hA, τ, hτ, hτ'⟩ := hτex
  unfold Cuts at hX hY
  have overUnder : ∀ (B : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)), IsPlaceOver B w →
      IsPlaceOver B (w.under (𝓞 (maximalRealSubfield E))) := by
    intro B w hB x
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, ← hB]
    rfl
  have resLift : ∀ (g : G (maximalRealSubfield E) Ω) (hg : Fixes E g),
      AlgEquiv.restrictScalarsHom (maximalRealSubfield E) (GlobalTheory.AboveL.DecRes.lift (E := E) g hg) = g :=
    fun g hg => AlgEquiv.ext fun x => rfl
  have hτD := Ine_le_Dec A hτ
  obtain ⟨hτE, hτH⟩ := hDec A hA τ hτD
  obtain ⟨τ', hres⟩ : ∃ τ' : G E Ω, AlgEquiv.restrictScalarsHom (maximalRealSubfield E) τ' = τ :=
    ⟨_, resLift τ hτE⟩
  have fY : fixGrp E Ω Y.K = H'.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hY g
  have fX : fixGrp E Ω X.K = H.comap (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) :=
    Subgroup.ext fun g => hX g
  have hidx := hIdx (G (maximalRealSubfield E) Ω) (G E Ω)
    (AlgEquiv.restrictScalarsHom (maximalRealSubfield E)) H H' hH'.comm hle hp
    ⟨τ', by rw [hres]; exact hτH, by rw [hres]; exact hτ'⟩
  obtain ⟨x0, t0E, t0Ω, hgal, hfin⟩ := hIncl E Ω X Y (by rw [fY, fX]; exact Subgroup.comap_mono hle)
  rw [fY, fX, hidx] at hfin
  obtain ⟨w, hw⟩ := GlobalTheory.AbOverSubfield.exists_place_between (F := maximalRealSubfield E) (K := E) hA
  have hwu : w.under (𝓞 (maximalRealSubfield E)) = u := eq_of_isPlaceOver (overUnder A w hw) hA
  have hfixX : Fixes X.K τ' := (hX τ').2 (by rw [hres]; exact hτH)
  refine ⟨⟨x0, t0E, t0Ω, hgal, by rw [hfin]; exact hp, w, ?_, ?_, A, hw,
    GlobalTheory.AboveL.DecRes.lift (E := X.K) τ' hfixX, ?_, ?_⟩, ?_⟩
  · intro hwS
    exact hS w hwS hwu
  · intro B hB g hg
    have hBu : IsPlaceOver B u := by
      rw [← hwu]
      exact overUnder B w hB
    obtain ⟨hgE, hgH⟩ := hDec B hBu g hg
    refine ⟨hgE, ?_⟩
    have h1 := (hX (GlobalTheory.AboveL.DecRes.lift (E := E) g hgE)).2 (by rw [resLift]; exact hgH)
    exact h1
  · subst hres
    rw [mem_Ine]
    have hτI := (mem_Ine (A := A)).1 hτ
    exact ⟨(GlobalTheory.AboveL.mem_dec_congr A _ _ (fun x => rfl)).2 hτI.1, hτI.2⟩
  · intro hfix
    exact hτ' (by rw [← hres]; exact (hY τ').1 hfix)
  · intro x1 t1
    have hx : x1 = x0 := by
      refine Algebra.algebra_ext _ _ fun r => (algebraMap Y.K Ω).injective ?_
      rw [← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x1 _ _ t1 r,
        ← @IsScalarTower.algebraMap_apply X.K Y.K Ω _ _ _ x0 _ _ t0Ω r]
    subst hx
    exact hfin
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.infOf :
    InfOf := by
  intro F Ω _ _ _ _ _ P hP hfin
  have hopen : ∀ Q : QCM F Ω, IsOpen ((Q.K.fixingSubgroup : Subgroup (G F Ω)) : Set (G F Ω)) := by
    intro Q
    haveI : FiniteDimensional F ↥Q.K :=
      Module.finite_of_finrank_pos (by rw [Q.two]; exact two_pos)
    exact IntermediateField.fixingSubgroup_isOpen Q.K
  have hS : (⋃ Q ∈ {Q | P Q}, {u : HeightOneSpectrum (𝓞 F) | ∃ A : ValuationSubring Ω,
      IsPlaceOver A u ∧ ¬ Ine (F := F) A ≤ Q.K.fixingSubgroup}).Finite :=
    Set.Finite.biUnion hfin fun Q _ => GlobalTheory.T.finite_places_inertia_not_le_openSubgroup Ω F Q.K.fixingSubgroup (hopen Q)
  obtain ⟨Q, hQ, u, hu, A, hA, τ, hτ, hfix⟩ := hP _ hS
  refine hu (Set.mem_biUnion (show Q ∈ {Q | P Q} from hQ) ⟨A, hA, fun hle => hfix ?_⟩)
  intro x
  exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hle hτ) _ x.2
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.sqrtFix :
    SqrtFix := by
  intro F Ω _ _ _ _ A x a hx
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  have hsq : ∀ g : G F Ω, g x = x ∨ g x = -x := by
    intro g
    have hgx : (g x) ^ 2 = x ^ 2 := by rw [← map_pow, hx, map_intCast]
    have h0 : (g x - x) * (g x + x) = 0 := by linear_combination hgx
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  have hint : ∀ k : ℤ, A.valuation (k : Ω) ≤ 1 := fun k => by
    exact_mod_cast A.valuation_le_one (k : A)
  refine ⟨?_, ?_⟩
  · intro t _ hvt hdiv g hg
    rcases hsq g with h | h
    · exact h
    · exfalso
      obtain ⟨k, hk⟩ := hdiv
      have hk' : (a : Ω) - 1 = 8 * (t : Ω) * (k : Ω) := by
        have hc := congrArg (fun z : ℤ => (z : Ω)) hk
        push_cast at hc
        linear_combination hc
      set y : Ω := (x - 1) / 2 with hy
      set y' : Ω := (-x - 1) / 2 with hy'
      have hgy : g y = y' := by
        rw [hy, hy', map_div₀, map_sub, map_one, map_ofNat, h]
      have hsum : y + y' = -1 := by
        rw [hy, hy']
        ring
      have hprod : y * y' = ((-2 * k : ℤ) : Ω) * (t : Ω) := by
        rw [hy, hy']
        push_cast
        linear_combination (-1 / 4 : Ω) * hx - (1 / 4 : Ω) * hk'
      have hvp : A.valuation (y * y') < 1 := by
        rw [hprod, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _)) hvt
      have hvs : A.valuation (y + y') = 1 := by
        rw [hsum, Valuation.map_neg, Valuation.map_one]
      have hiff := valuation_apply_lt_one_iff hg y
      rw [hgy] at hiff
      by_cases hyl : A.valuation y < 1
      · have hs := Valuation.map_add_lt A.valuation hyl (hiff.2 hyl)
        rw [hvs] at hs
        exact lt_irrefl _ hs
      · have hyl' : ¬ A.valuation y' < 1 := fun h' => hyl (hiff.1 h')
        push_neg at hyl hyl'
        have hge : 1 ≤ A.valuation (y * y') := by
          rw [map_mul]
          exact one_le_mul hyl hyl'
        exact absurd hvp (not_lt.2 hge)
  · intro h2a τ hτ
    obtain ⟨-, hI⟩ : τ ∈ ValuationSubring.decompositionSubgroup F A ∧
        ∀ (y : Ω), A.valuation y ≤ 1 → A.valuation (τ y - y) < 1 := hτ
    rcases hsq τ with h | h
    · exact h
    · exfalso
      have hv2 : A.valuation (2 : Ω) ≤ 1 := by simpa using hint 2
      have hva : A.valuation (a : Ω) ≤ 1 := hint a
      have e2a : A.valuation (2 : Ω) * A.valuation (a : Ω) = 1 := by
        rw [← map_mul]
        push_cast at h2a
        exact h2a
      have hv2' : A.valuation (2 : Ω) = 1 :=
        le_antisymm hv2 (e2a ▸ mul_le_of_le_one_right' hva)
      have hva' : A.valuation (a : Ω) = 1 :=
        le_antisymm hva (e2a ▸ mul_le_of_le_one_left' hv2)
      have hvx2 : A.valuation x ^ 2 = 1 := by
        rw [← Valuation.map_pow, hx, hva']
      have hvx : A.valuation x = 1 := by
        rcases lt_trichotomy (A.valuation x) 1 with hl | he | hg
        · exact absurd hvx2 (ne_of_lt (pow_lt_one' hl two_ne_zero))
        · exact he
        · exact absurd hvx2 (ne_of_gt (one_lt_pow' hg two_ne_zero))
      have key := hI x hvx.le
      rw [h, show -x - x = -(2 * x) by ring, Valuation.map_neg, map_mul, hv2', hvx, one_mul] at key
      exact lt_irrefl _ key
end

section
noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem natCast_notMem_sq {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) (w : HeightOneSpectrum (𝓞 K)) : (p : 𝓞 K) ∉ w.asIdeal ^ 2 := by
  intro h
  have hv : (p : 𝓞 K) ∈ w.asIdeal := Ideal.pow_le_self two_ne_zero h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

theorem unrLarge : UnrLarge := by
  intro K _ _
  refine ⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩
  have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp hd
  have h2 : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  exact absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.UnitaryBC
open scoped Pointwise

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem apply_eq_of_not_fixes {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    {s t : G (maximalRealSubfield L) Ω} (hs : ¬ Fixes L s) (ht : ¬ Fixes L t) (y : L) :
    s (algebraMap L Ω y) = t (algebraMap L Ω y) := by
  haveI : IsGalois (maximalRealSubfield L) L := Algebra.IsQuadraticExtension.isGalois _ _
  have hcard : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank]
    exact Algebra.IsQuadraticExtension.finrank_eq_two _ _
  have hne : ∀ r : G (maximalRealSubfield L) Ω, ¬ Fixes L r → r.restrictNormal L ≠ 1 := by
    intro r hr h1
    apply hr
    intro x
    rw [← AlgEquiv.restrictNormal_commutes r L x, h1]
    rfl
  have heq : s.restrictNormal L = t.restrictNormal L :=
    ((Nat.card_eq_two_iff' 1).1 hcard).unique (hne s hs) (hne t ht)
  rw [← AlgEquiv.restrictNormal_commutes s L y, ← AlgEquiv.restrictNormal_commutes t L y, heq]

theorem splitIff : SplitIff := by
  intro L Ω _ _ _ _ _ _ A w hA
  show IsSplitAt w ↔ ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g
  have up : ∀ (B : ValuationSubring Ω) (u : HeightOneSpectrum (𝓞 L)), IsPlaceOver B u →
      IsPlaceOver B (HeightOneSpectrum.under (𝓞 (maximalRealSubfield L)) u) := by
    intro B u hB x
    have e : algebraMap (maximalRealSubfield L) Ω (x : maximalRealSubfield L) =
        algebraMap L Ω ((algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x : 𝓞 L) : L) := by
      rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
      rfl
    rw [e, hB]
    simp [HeightOneSpectrum.under]
  have hv := up A w hA
  have val : ∀ (σ : G (maximalRealSubfield L) Ω) (y : Ω),
      (σ • A).valuation y < 1 ↔ A.valuation (σ⁻¹ y) < 1 := by
    intro σ y
    rw [valuation_lt_one_iff', valuation_lt_one_iff',
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
      ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  constructor
  · rintro ⟨u, hu, huw⟩ g hg
    by_contra hgL
    obtain ⟨A', hA'⟩ := exists_isPlaceOver Ω u
    obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isPlaceOver hv (huw ▸ up A' u hA')
    apply hu
    refine eq_of_isPlaceOver hA' ?_
    intro x
    rw [val, ← hA x]
    by_cases hσ : Fixes L σ⁻¹
    · rw [hσ]
    · rw [apply_eq_of_not_fixes hσ hgL, valuation_apply_lt_one_iff hg]
  · intro h
    refine UpperTheory.isSplitAt_of_decomposition_le_restriction_range L Ω A _ hv ?_ w rfl
    intro g hg
    refine ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) (fun x => h g hg x), ?_⟩
    ext x
    rfl

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem unramifiedAt_of_dec_fixes (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω]
    [IsAlgClosure L Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (hA : IsPlaceOver A w)
    (hfix : ∀ g ∈ Dec (F := maximalRealSubfield L) A, Fixes L g) :
    Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal := by
  haveI : IsAlgClosure (maximalRealSubfield L) Ω :=
    ⟨IsAlgClosure.isAlgClosed L, Algebra.IsAlgebraic.trans _ L Ω⟩
  have hAv : IsPlaceOver A (w.under (𝓞 (maximalRealSubfield L))) := fun x => by
    rw [IsScalarTower.algebraMap_apply (maximalRealSubfield L) L Ω]
    exact hA (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) x)
  obtain ⟨-, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 (maximalRealSubfield L))) w hAv hA
    fun σ hσ => hfix σ (Ine_le_Dec A hσ)
  exact Ideal.ramificationIdx_eq_one_iff.1 he

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.allUnr :
    SplitIff → AllUnr := by
  intro hS Y Ω _ _ _ _ _ T Q hQ w
  by_cases hw : IsSplitAt w
  · obtain ⟨A, hA⟩ := exists_isPlaceOver Ω w
    exact unramifiedAt_of_dec_fixes ↥Q.K Ω A w hA ((hS ↥Q.K Ω A w hA).1 hw)
  · exact (hQ.2.2.2.1 w hw).2.1
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published GlobalTheory.RealGal GlobalTheory.UnitaryBC
open UpperTheory.Gal.UnramifiedFromSplittingCriterion

private theorem exists_real_lift (K M : Type) [Field K] [NumberField K] [IsCMField K] [Field M] [NumberField M] [IsCMField M]
    [Algebra K M] (x : 𝓞 (maximalRealSubfield K)) :
    ∃ y : 𝓞 (maximalRealSubfield M), algebraMap (𝓞 (maximalRealSubfield M)) (𝓞 M) y =
      algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) := by
  set y₀ : 𝓞 M := algebraMap (𝓞 K) (𝓞 M) (algebraMap (𝓞 (maximalRealSubfield K)) (𝓞 K) x) with hy₀
  have hz : (y₀ : M) = algebraMap K M (((x : maximalRealSubfield K)) : K) := rfl
  have hmem : (y₀ : M) ∈ maximalRealSubfield M := by
    rw [hz]
    exact (mem_maximalRealSubfield_iff _).2 fun φ =>
      (mem_maximalRealSubfield_iff _).1 (x : maximalRealSubfield K).2 (φ.comp (algebraMap K M))
  have hint : IsIntegral ℤ (⟨(y₀ : M), hmem⟩ : maximalRealSubfield M) :=
    (isIntegral_algebraMap_iff (B := M) (algebraMap (maximalRealSubfield M) M).injective).1
      (RingOfIntegers.isIntegral_coe y₀)
  exact ⟨⟨⟨(y₀ : M), hmem⟩, hint⟩, RingOfIntegers.ext rfl⟩

theorem UpperTheory.Gal.UnramifiedFromSplittingCriterion.apartUp :
    ApartUp := by
  intro K M _ _ _ _ _ _ _
  refine ⟨fun w₁ w₂ hap h => hap ?_, fun v => ?_⟩
  · apply HeightOneSpectrum.ext
    apply Ideal.ext
    intro x
    obtain ⟨y, hy⟩ := exists_real_lift K M x
    have h' : y ∈ (w₁.under (𝓞 (maximalRealSubfield M))).asIdeal ↔
        y ∈ (w₂.under (𝓞 (maximalRealSubfield M))).asIdeal := by rw [h]
    simp only [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap, hy] at h' ⊢
    exact h'
  · have hinj : Function.Injective (algebraMap (𝓞 K) (𝓞 M)) := FaithfulSMul.algebraMap_injective _ _
    have hker : RingHom.ker (algebraMap (𝓞 K) (𝓞 M)) ≤ v.asIdeal := by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 hinj]
      exact bot_le
    haveI := v.isMaximal
    obtain ⟨Q, hQ, hQm⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 M) v.asIdeal hker
    have hne : Q ≠ ⊥ := by
      rintro rfl
      apply v.ne_bot
      rw [← hQm, ← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1 hinj]
    refine ⟨⟨Q, hQ.isPrime, hne⟩, ?_⟩
    apply HeightOneSpectrum.ext
    rw [HeightOneSpectrum.under_asIdeal]
    exact hQm
end

section
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem satSplit : SatSplit := by
  intro K M Ω _ _ _ _ _ _ _ _ _ _ _ _ A v w hv hw hD a π P hP B hB
  obtain ⟨i, hi, hi', hiv⟩ := splitIso_holds K M Ω A v w hv hw hD
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL K a π v
  obtain ⟨σ', hσ', -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp UpperTheory.V.Af.formsFiniteGL M a P w
  obtain ⟨e, he⟩ := hP v w i hi hi' σ σ' hσ hσ'
  obtain ⟨φ, hφ⟩ := exists_isFrob hv
  have hq : normV w = normV v ^ 1 := degOf K M Ω A v w hv hw (fun τ hτ => hD τ (Ine_le_Dec A hτ)) φ 1 one_pos hφ
    fun k => ⟨fun _ => one_dvd k, fun _ => hD _ (pow_mem (show φ ∈ Dec (F := K) A from hφ.1) k)⟩
  rw [pow_one] at hq
  refine ((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake M a P w σ' hσ').1 B).2 (GlobalTheory.IsoPull.hasSatGL_of_ringEquiv i hiv ?_ e (fun g x => (he g x).symm)
    (((GlobalTheory.T.cuspRep_satake_iff_localComponent_satake K a π v σ hσ).1 B).1 hB))
  first | exact hq | (unfold normV at hq; simp only [Formalism.UG.qV, Ideal.absNorm_apply, Submodule.cardQuot_apply]; exact hq)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end

section
namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

theorem freshChar_holds : FreshChar := freshChar powChar inertiaGen decPow (freshPrime splitPlace rootMod)
theorem layerOf_holds : LayerOf := layerOf inclOf indexComap
theorem noSelfTwist_holds : NoSelfTwist := noSelfTwist_of normRam
theorem infinitely_many_real_quadratic_steps : Quad0 := quadraticCharTwist_of_exists_of_infinity (quad0Ex sqrtFix mkQ unrLarge) infOf
theorem allUnr_holds : AllUnr := allUnr splitIff
theorem threeApart_holds : ThreeApart := threeApart_of double apartUp
theorem satSplit_holds : SatSplit := satSplit

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
end
