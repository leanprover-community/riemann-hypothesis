import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeSpanSupPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletionIsDomainAndIsIntegrallyClosed
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteOfFiniteQuotMapOfIsPrecomplete
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

section
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Izumi

theorem exists_point_of_isLocalHom {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (x : M.Z)
    {p : ℕ} [Fact p.Prime] (χ : M.O x →+* OO p) [IsLocalHom χ] :
    ∃ y : Sp (OO p) ⟶ M.Z, y (cPt p) = x ∧ ∀ a : M.O x,
      M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  let χ' : M.Z.presheaf.stalk x ⟶ CommRingCat.of (OO p) :=
    CommRingCat.ofHom (χ.comp (M.stalkEquiv x).toRingHom)
  haveI : IsLocalHom χ'.hom := by
    refine ⟨fun a ha => ?_⟩
    have h1 : IsUnit (M.stalkEquiv x a) := isUnit_of_map_unit χ _ ha
    exact (MulEquiv.isUnit_map (M.stalkEquiv x).toMulEquiv).1 h1
  set y : Sp (OO p) ⟶ M.Z := Spec.map χ' ≫ M.Z.fromSpecStalk x with hy
  have hc : y (cPt p) = x := by
    rw [hy, Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  have key : ∀ h : y (cPt p) ⤳ x, M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo y = χ' := by
    intro h
    refine TopCat.Presheaf.stalk_hom_ext _ fun W hxW => ?_
    rw [← Category.assoc, TopCat.Presheaf.germ_stalkSpecializes]
    exact Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk χ' W _
  refine ⟨y, hc, fun a => ?_⟩
  rw [RatModel.val_gPt hc a]
  change (((M.Z.presheaf.stalkSpecializes _ ≫ Scheme.stalkClosedPointTo y).hom
    ((M.stalkEquiv x).symm a) : OO p) : PadicAlgCl p) = _
  rw [key]
  exact congrArg (fun b => ((χ b : OO p) : PadicAlgCl p)) ((M.stalkEquiv x).apply_symm_apply a)

theorem exists_ne_zero_forall_exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω)
    (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) (x : M.Z) :
    ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 →
      ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  obtain ⟨w, hwU, hwV⟩ := M.nonempty_inf hU ⟨x, hxV⟩
  obtain ⟨t, htU, hwt⟩ := hV.exists_basicOpen_le (V := U) ⟨w, hwU⟩ hwV
  have ht0 : valF M.pt V t ≠ 0 :=
    ((RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hwV t).2 hwt)).1
  refine ⟨⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩, fun h => ht0 (congrArg Subtype.val h), ?_⟩
  intro p _ χ hχ hs
  obtain ⟨y, hc, hval⟩ := exists_point_of_isLocalHom M x χ
  refine ⟨y, ⟨hc, ?_⟩, hval⟩
  rintro _ ⟨w', rfl⟩
  have hz : (gPt p ≫ y) w' ∈ V := (RatModel.gPt_specializes hc w').mem_open V.isOpen hxV
  have hne : M.val (gPt p ≫ y) (valF M.pt V t) ≠ 0 := by
    have e := hval ⟨valF M.pt V t, RatModel.valF_mem_O hxV t⟩
    rw [e]
    intro h0
    exact hs (Subtype.ext h0)
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton _ w')
    ⟨valF M.pt V t, RatModel.valF_mem_O hz t⟩).1 hne
  exact htU ((RatModel.isUnit_valF_iff hz t).1 hu)

end GlobalTheory.Izumi
end
end

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ x : M.Z, ∃ s : M.O x, s ≠ 0 ∧ ∀ (p : ℕ) [Fact p.Prime] (χ : M.O x →+* OO p), IsLocalHom χ → χ s ≠ 0 → ∃ y : Sp (OO p) ⟶ M.Z, M.Cen U x y ∧ ∀ a : M.O x, M.val (gPt p ≫ y) a = ((χ a : OO p) : PadicAlgCl p) := by
  atlas_forward_decl GlobalTheory.Izumi.exists_ne_zero_forall_exists_cen
end

section
section
open IsLocalRing Polynomial

namespace GlobalTheory.Izumi

theorem exists_dominating_of_residue_map {R S : Type} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsDomain S] [IsNoetherianRing S] (j : R →+* S) (hj : Function.Injective j)
    (φ : S →+* ResidueField R) (hφ : ∀ r, φ (j r) = residue R r) (f G : R) (u : S)
    (hu : φ u = 0) (hf : j f = j G * u) :
    ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
      (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
      (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  have hsurj : Function.Surjective φ := fun y => by
    obtain ⟨r, rfl⟩ := residue_surjective y
    exact ⟨j r, hφ r⟩
  haveI hmax : (RingHom.ker φ).IsMaximal := RingHom.ker_isMaximal_of_surjective φ hsurj
  let B := Localization.AtPrime (RingHom.ker φ)
  have hmem : ∀ s : S, algebraMap S B s ∈ maximalIdeal B ↔ φ s = 0 := fun s => by
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff B (RingHom.ker φ), RingHom.mem_ker]
  haveI : IsNoetherianRing B :=
    IsLocalization.isNoetherianRing (RingHom.ker φ).primeCompl B inferInstance
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    (algebraMap S B).comp j, ?_, ⟨fun r hr => ?_⟩, fun b => ?_, algebraMap S B u,
    (hmem u).2 hu, ?_⟩
  · exact (IsLocalization.injective B (RingHom.ker φ).primeCompl_le_nonZeroDivisors).comp hj
  · by_contra h
    have h1 : φ (j r) = 0 := by
      rw [hφ, residue_eq_zero_iff]; exact h
    exact (hmem _).2 h1 hr
  · obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker φ).primeCompl b
    have ht : φ t ≠ 0 := t.2
    obtain ⟨r, hr⟩ := residue_surjective (φ s / φ t)
    refine ⟨r, ?_⟩
    have hunit : IsUnit (algebraMap S B t) := IsLocalization.map_units B t
    rw [← Ideal.unit_mul_mem_iff_mem _ hunit, mul_sub]
    dsimp only
    rw [IsLocalization.mk'_spec', RingHom.comp_apply, ← map_mul, ← map_sub, hmem, map_sub,
      map_mul, hφ, hr, mul_div_cancel₀ _ ht, sub_self]
  · simp [hf]

theorem coeff_zero_mem_maximalIdeal_of_aeval_div {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [IsIntegrallyClosed R] (f G : R) (h : G ∉ Ideal.span {f}) (P : R[X])
    (hP : aeval (algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G) P = 0) :
    P.coeff 0 ∈ maximalIdeal R := by
  by_contra hc
  have hunit : IsUnit (P.coeff 0) := by
    simpa [mem_maximalIdeal] using hc
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  have hf : f ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div, ← coeff_zero_eq_aeval_zero'] at hP
    exact hunit.ne_zero ((map_eq_zero_iff _ hinj).1 hP)
  have hf' : algebraMap R (FractionRing R) f ≠ 0 := (map_ne_zero_iff _ hinj).2 hf
  set u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G with hu
  have hu0 : u ≠ 0 := div_ne_zero hf' hG'
  letI := invertibleOfNonzero hu0
  have hrev : aeval (⅟u) P.reverse = 0 := by
    rw [aeval_def, eval₂_reverse_eq_zero_iff]; exact hP
  have hint := isIntegral_leadingCoeff_smul P.reverse (⅟u) hrev
  rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero hunit.ne_zero] at hint
  obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  apply h
  rw [← Ideal.unit_mul_mem_iff_mem _ hunit, Ideal.mem_span_singleton']
  refine ⟨r, hinj ?_⟩
  rw [map_mul, map_mul, hr, invOf_eq_inv, hu, Algebra.smul_def]
  field_simp

theorem exists_dominating_eq_mul_of_not_mem_span :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
      [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} →
      ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B)
        (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧
        (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  intro R _ _ _ _ _ f G h
  have hinj := IsFractionRing.injective R (FractionRing R)
  have hG : G ≠ 0 := by rintro rfl; exact h (zero_mem _)
  have hG' : algebraMap R (FractionRing R) G ≠ 0 := (map_ne_zero_iff _ hinj).2 hG
  let u := algebraMap R (FractionRing R) f / algebraMap R (FractionRing R) G
  let e : R[X] →+* FractionRing R := (aeval u : R[X] →ₐ[R] FractionRing R)
  have he : ∀ P, e P = aeval u P := fun _ => rfl
  haveI : (RingHom.ker e).IsPrime := RingHom.ker_isPrime e
  let φ : (R[X] ⧸ RingHom.ker e) →+* ResidueField R :=
    Ideal.Quotient.lift _ ((residue R).comp constantCoeff) fun P hP => by
      rw [RingHom.comp_apply, residue_eq_zero_iff]
      exact coeff_zero_mem_maximalIdeal_of_aeval_div f G h P hP
  refine exists_dominating_of_residue_map ((Ideal.Quotient.mk (RingHom.ker e)).comp C) ?_ φ ?_
    f G (Ideal.Quotient.mk _ X) ?_ ?_
  · rw [injective_iff_map_eq_zero]
    intro r hr
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker, he, aeval_C] at hr
    exact (map_eq_zero_iff _ hinj).1 hr
  · intro r; simp [φ]
  · simp [φ]
  · rw [RingHom.comp_apply, RingHom.comp_apply, ← map_mul, Ideal.Quotient.eq, RingHom.mem_ker, he]
    simp only [map_sub, map_mul, aeval_C, aeval_X, u]
    field_simp
    ring

end GlobalTheory.Izumi
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f G : R), G ∉ Ideal.span {f} → ∃ (B : Type) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B) (_ : IsNoetherianRing B) (ι : R →+* B), Function.Injective ι ∧ IsLocalHom ι ∧ (∀ b : B, ∃ r : R, b - ι r ∈ maximalIdeal B) ∧ ∃ u ∈ maximalIdeal B, ι f = ι G * u := by
  atlas_forward_decl GlobalTheory.Izumi.exists_dominating_eq_mul_of_not_mem_span
end

section
section
open IsLocalRing

namespace GlobalTheory

theorem exists_prime_not_mem_forall_gt_eq_maximalIdeal (C : Type) [CommRing C] [IsDomain C]
    [IsLocalRing C] [IsNoetherianRing C] (x : C) (hx : x ≠ 0) (hxm : x ∈ maximalIdeal C) :
    ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  classical

  have hnil : ¬ IsNilpotent x := fun h => hx (IsNilpotent.eq_zero h)
  haveI : Nontrivial (Localization.Away x) :=
    (IsLocalization.injective (Localization.Away x)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hx)).nontrivial
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (Localization.Away x)
  set q : Ideal C := M.comap (algebraMap C (Localization.Away x)) with hqdef
  have hMp : M.IsPrime := hM.isPrime
  have hqd := (IsLocalization.isPrime_iff_isPrime_disjoint (Submonoid.powers x)
    (Localization.Away x) M).mp hMp
  have hqp : q.IsPrime := hqd.1
  have hxq : x ∉ q := fun h =>
    Set.disjoint_left.mp hqd.2 (Submonoid.mem_powers x) h

  have habove : ∀ P : Ideal C, P.IsPrime → q < P → x ∈ P := by
    intro P hP hlt
    by_contra hxP
    have hdisj : Disjoint (Submonoid.powers x : Set C) P := by
      rw [Set.disjoint_left]
      rintro _ ⟨n, rfl⟩ h
      exact hxP (hP.mem_of_pow_mem n h)
    have hPL := IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) P hP hdisj
    have hcomap := IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers x)
      (Localization.Away x) hP hdisj
    have hMle : M ≤ P.map (algebraMap C (Localization.Away x)) := by
      rw [← IsLocalization.map_comap (Submonoid.powers x) (Localization.Away x) M]
      exact Ideal.map_mono hlt.le
    have heq := hM.eq_of_le hPL.ne_top hMle
    have : q = P := by rw [hqdef, heq]; exact hcomap
    exact hlt.ne this
  refine ⟨q, hqp, hxq, fun P hP hlt => ?_⟩

  set f := Ideal.Quotient.mk q with hfdef
  have hsurj : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = q := Ideal.mk_ker
  haveI : IsDomain (C ⧸ q) := Ideal.Quotient.isDomain q
  set m' : Ideal (C ⧸ q) := (maximalIdeal C).map f with hm'
  have hqm : q ≤ maximalIdeal C := le_maximalIdeal hqp.ne_top
  have hm'p : m'.IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hqm)
  have hx0 : f x ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hxq
  have hht : m'.height ≤ 1 := by
    refine height_le_one_of_forall_mem m' hx0 ?_
    intro p' hp' hp'0 _
    have hcp : (p'.comap f).IsPrime := Ideal.comap_isPrime f p'
    have hqc : q < p'.comap f := by
      refine lt_of_le_of_ne ?_ ?_
      · intro a ha
        simp [Ideal.mem_comap, hfdef, Ideal.Quotient.eq_zero_iff_mem.mpr ha]
      · intro e
        apply hp'0
        rw [← Ideal.map_comap_of_surjective f hsurj p', ← e]
        exact (Ideal.map_eq_bot_iff_le_ker _).mpr hker.ge
    exact habove _ hcp hqc
  have hPp' : (P.map f).IsPrime := Ideal.map_isPrime_of_surjective hsurj (hker.symm ▸ hlt.le)
  have hP0 : P.map f ≠ ⊥ := by
    intro e
    rw [Ideal.map_eq_bot_iff_le_ker, hker] at e
    exact hlt.ne (le_antisymm hlt.le e)
  have hPm : P.map f ≤ m' := Ideal.map_mono (le_maximalIdeal hP.ne_top)
  have hPeq : P.map f = m' := by
    by_contra hne
    have h1 := Ideal.height_add_one_le_of_lt_of_isPrime (bot_lt_iff_ne_bot.mpr hP0)
    have h2 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hPm hne)
    have h3 : (⊥ : Ideal (C ⧸ q)).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hht)
    simp at h3
    exact absurd h3 (by decide)
  have hPc : P = (P.map f).comap f := by
    rw [Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hlt.le]
  have hmc : maximalIdeal C = m'.comap f := by
    rw [hm', Ideal.comap_map_of_surjective' f hsurj, hker, sup_eq_left.mpr hqm]
  rw [hPc, hPeq, ← hmc]

end GlobalTheory
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' : ∀ (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C] (x : C), x ≠ 0 → x ∈ maximalIdeal C → ∃ q : Ideal C, q.IsPrime ∧ x ∉ q ∧ ∀ P : Ideal C, P.IsPrime → q < P → P = maximalIdeal C := by
  atlas_forward_decl GlobalTheory.exists_prime_not_mem_forall_gt_eq_maximalIdeal
end

section
namespace GlobalTheory.InjectiveAlgebraMapTorsionFree

variable (p : ℕ) [Fact (Nat.Prime p)]

theorem algebraMap_injective_of_ne (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by
  by_contra hinj
  have hker : RingHom.ker (algebraMap ℤ_[p] D) ≠ ⊥ := fun h =>
    hinj ((RingHom.injective_iff_ker_eq_bot _).mpr h)
  obtain ⟨n, hn⟩ := PadicInt.ideal_eq_span_pow_p hker
  have hmem : (p : ℤ_[p]) ^ n ∈ RingHom.ker (algebraMap ℤ_[p] D) := by
    rw [hn]
    exact Ideal.mem_span_singleton_self _
  rw [RingHom.mem_ker, map_pow, map_natCast] at hmem
  exact hp (pow_eq_zero_iff'.mp hmem).1

theorem isTorsionFree_of_injective {R S : Type} [CommRing R] [CommRing S] [IsDomain R]
    [IsDomain S] [Algebra R S] (h : Function.Injective (algebraMap R S)) :
    Module.IsTorsionFree R S :=
  Module.isTorsionFree_iff_algebraMap_injective.mpr h

theorem norm_algebraMap_le (a : ℤ_[p]) : ‖algebraMap ℤ_[p] (PadicAlgCl p) a‖ ≤ 1 := by
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), PadicAlgCl.norm_extends]
  simpa using PadicInt.norm_le_one a

theorem norm_le_one_of_isIntegral (x : PadicAlgCl p) (hx : IsIntegral ℤ_[p] x) : ‖x‖ ≤ 1 := by
  haveI : IsUltrametricDist (PadicAlgCl p) :=
    IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm (PadicAlgCl.isNonarchimedean p)
  by_contra h
  push_neg at h
  obtain ⟨q, hqm, hq⟩ := hx
  rw [hqm.as_sum, Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum] at hq
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hq
  have hxn : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_left hq
  rcases Nat.eq_zero_or_pos q.natDegree with h0 | hn
  · rw [h0] at hxn
    simp at hxn
  have hx1 : 1 ≤ ‖x‖ := h.le
  have hle : ‖∑ i ∈ Finset.range q.natDegree, algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i) * x ^ i‖ ≤
      ‖x‖ ^ (q.natDegree - 1) := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg (norm_nonneg _) _)
    intro i hi
    rw [norm_mul, norm_pow]
    have hi' := Finset.mem_range.mp hi
    calc ‖algebraMap ℤ_[p] (PadicAlgCl p) (q.coeff i)‖ * ‖x‖ ^ i ≤ 1 * ‖x‖ ^ (q.natDegree - 1) :=
          mul_le_mul (norm_algebraMap_le p _) (pow_le_pow_right₀ hx1 (by omega))
            (pow_nonneg (norm_nonneg _) _) zero_le_one
      _ = ‖x‖ ^ (q.natDegree - 1) := one_mul _
  have h1 : ‖x‖ ^ q.natDegree ≤ ‖x‖ ^ (q.natDegree - 1) := by
    rw [← norm_pow, hxn, norm_neg]
    exact hle
  have h2 : ‖x‖ ^ (q.natDegree - 1) < ‖x‖ ^ q.natDegree := pow_lt_pow_right₀ h (by omega)
  linarith

theorem exists_injective_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by
  have hM : Function.Injective (algebraMap ℤ_[p] (PadicAlgCl p)) := by
    apply algebraMap_injective_of_ne
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  haveI := isTorsionFree_of_injective (algebraMap_injective_of_ne p D hp)
  haveI := isTorsionFree_of_injective hM
  let φ : D →ₐ[ℤ_[p]] PadicAlgCl p := IsAlgClosed.lift
  refine ⟨φ.toRingHom, ?_, fun d => ?_⟩
  · rw [RingHom.injective_iff_ker_eq_bot]
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [eq_bot_iff]
    intro a ha
    rw [Ideal.mem_comap, RingHom.mem_ker] at ha
    have : algebraMap ℤ_[p] (PadicAlgCl p) a = 0 := by
      rw [← φ.commutes]; exact ha
    exact (map_eq_zero_iff _ hM).mp this
  · exact norm_le_one_of_isIntegral p _ ((Algebra.IsIntegral.isIntegral d).map φ)

end GlobalTheory.InjectiveAlgebraMapTorsionFree
end

section
section
open IsLocalRing

namespace GlobalTheory.PadicEmb

theorem exists_embedding : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D]
    [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 →
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  first
  | exact @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
  | (apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one ..)

end GlobalTheory.PadicEmb
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain : ∀ (p : ℕ) [Fact p.Prime] (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D], (p : D) ≠ 0 → ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d, ‖φ d‖ ≤ 1 := by
  atlas_forward_decl GlobalTheory.PadicEmb.exists_embedding
end

section
section
open IsLocalRing

namespace GlobalTheory.CompletionEmbed

variable (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsLocalRing C]

noncomputable def levelMap (hpm : (p : C) ∈ maximalIdeal C) (n : ℕ) :
    ℤ_[p] →+* C ⧸ maximalIdeal C ^ n :=
  have h : ((p ^ n : ℕ) : C ⧸ maximalIdeal C ^ n) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk (maximalIdeal C ^ n)), Ideal.Quotient.eq_zero_iff_mem,
      Nat.cast_pow]
    exact Ideal.pow_mem_pow hpm n
  (ZMod.castHom (ringChar.dvd h) (C ⧸ maximalIdeal C ^ n)).comp (PadicInt.toZModPow n)

theorem levelMap_compat (hpm : (p : C) ∈ maximalIdeal C) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow (maximalIdeal C) hle).comp (levelMap p C hpm n) =
      levelMap p C hpm m := by
  unfold levelMap
  rw [← PadicInt.zmod_cast_comp_toZModPow m n hle, ← RingHom.comp_assoc, ← RingHom.comp_assoc]
  congr 1
  exact Subsingleton.elim _ _

noncomputable def toCompletion (hpm : (p : C) ∈ maximalIdeal C) :
    ℤ_[p] →+* AdicCompletion (maximalIdeal C) C :=
  AdicCompletion.liftRingHom (maximalIdeal C) (levelMap p C hpm)
    (fun hle => levelMap_compat p C hpm hle)

theorem algebraMap_injective [IsNoetherianRing C] :
    Function.Injective (algebraMap C (AdicCompletion (maximalIdeal C) C)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ ⨅ n : ℕ, maximalIdeal C ^ n := by
    rw [Submodule.mem_iInf]
    intro n
    have := congrArg (AdicCompletion.evalₐ (maximalIdeal C) n) hx
    rw [map_zero] at this
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using this
  rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal C).ne_top] at hmem
  exact hmem

theorem exists_pow_le_span [IsNoetherianRing C] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
  rw [Ideal.radical_eq_sInf]
  refine le_sInf fun Q ⟨hle, hQ⟩ => ?_
  have hQ0 : Q ≠ ⊥ := fun h => hp0 (by
    have := hle (Ideal.mem_span_singleton_self _)
    rw [h] at this
    exact (Ideal.mem_bot).mp this)
  rw [hprime Q hQ hQ0]

theorem finite_quot_span [IsNoetherianRing C] [Finite (ResidueField C)] (hp0 : (p : C) ≠ 0)
    (hprime : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) :
    Finite (AdicCompletion (maximalIdeal C) C ⧸
      Ideal.span {(p : AdicCompletion (maximalIdeal C) C)}) := by
  set A := AdicCompletion (maximalIdeal C) C
  have fg : (maximalIdeal C).FG := IsNoetherian.noetherian _
  haveI : Finite (C ⧸ maximalIdeal C) := ‹Finite (ResidueField C)›
  haveI : Finite (A ⧸ (maximalIdeal C).map (algebraMap C A)) := by
    have h := Finite.of_injective _
      (RingHom.kerLift_injective (AdicCompletion.evalOneₐ (maximalIdeal C)).toRingHom)
    rw [AdicCompletion.ker_evalOneₐ_eq_map _ fg] at h
    exact h
  obtain ⟨N, hN⟩ := exists_pow_le_span p C hp0 hprime
  haveI : Finite (A ⧸ ((maximalIdeal C).map (algebraMap C A)) ^ N) :=
    Ideal.finite_quotient_pow (fg.map _) N
  have hle : ((maximalIdeal C).map (algebraMap C A)) ^ N ≤ Ideal.span {(p : A)} := by
    rw [← Ideal.map_pow]
    calc _ ≤ (Ideal.span {(p : C)}).map (algebraMap C A) := Ideal.map_mono hN
      _ = _ := by rw [Ideal.map_span, Set.image_singleton, map_natCast]
  exact Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)

end GlobalTheory.CompletionEmbed

open IsLocalRing GlobalTheory.CompletionEmbed in

theorem GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain :
    ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C]
      [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C →
      (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D),
        Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  intro p _ C _ _ _ _ hfin hp0 hpm hprime
  set A := AdicCompletion (maximalIdeal C) C
  haveI : IsNoetherianRing A := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion C _
  letI : Algebra ℤ_[p] A := (toCompletion p C hpm).toAlgebra
  have hJ : (maximalIdeal ℤ_[p]).map (algebraMap ℤ_[p] A) = Ideal.span {(p : A)} := by
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast]
  haveI : Finite (A ⧸ Ideal.span {(p : A)}) := finite_quot_span p C hp0 hprime
  have hne : Ideal.span {(p : A)} ≠ ⊤ := by
    intro h
    have hu : IsUnit (p : A) := Ideal.span_singleton_eq_top.mp h
    have hu' := hu.map (AdicCompletion.evalOneₐ (maximalIdeal C))
    rw [map_natCast, ← map_natCast (Ideal.Quotient.mk (maximalIdeal C)),
      Ideal.Quotient.eq_zero_iff_mem.mpr hpm] at hu'
    exact not_isUnit_zero hu'
  haveI : Module.Finite ℤ_[p] A := by
    refine GlobalTheory.finite_of_finite_quot_map_of_isPrecomplete ℤ_[p] A (maximalIdeal ℤ_[p]) ?_ ?_
    · rw [hJ]; exact hne
    · rw [hJ]; exact Module.Finite.of_finite
  have hnil : ¬ IsNilpotent (p : A) := by
    rintro ⟨n, hn⟩
    have h : algebraMap C A ((p : C) ^ n) = 0 := by rw [map_pow, map_natCast]; exact hn
    have h3 := (injective_iff_map_eq_zero _).mp (algebraMap_injective C) _ h
    exact hp0 (IsNilpotent.eq_zero ⟨n, h3⟩)
  obtain ⟨Q, hQ, hpQ⟩ : ∃ Q : Ideal A, Q.IsPrime ∧ (p : A) ∉ Q := by
    by_contra h
    push_neg at h
    exact hnil (nilpotent_iff_mem_prime.mpr h)
  haveI := hQ
  refine ⟨A ⧸ Q, inferInstance, inferInstance, inferInstance, ?_,
    (Ideal.Quotient.mk Q).comp (algebraMap C A), ?_⟩
  · exact Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ_[p] Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ_[p] Q)
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have hbot : Q.comap (algebraMap C A) = ⊥ := by
      by_contra hb
      have h1 := hprime _ (Ideal.comap_isPrime _ _) hb
      apply hpQ
      have h2 : (p : C) ∈ Q.comap (algebraMap C A) := by
        rw [h1]; exact hpm
      rw [Ideal.mem_comap, map_natCast] at h2
      exact h2
    have hx' : x ∈ Q.comap (algebraMap C A) := by
      rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem]
      exact hx
    rw [hbot] at hx'
    exact (Ideal.mem_bot).mp hx'
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_padicInt_domain_embedding : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [CommRing C] [IsDomain C] [IsLocalRing C] [IsNoetherianRing C], Finite (ResidueField C) → (p : C) ≠ 0 → (p : C) ∈ maximalIdeal C → (∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : Algebra ℤ_[p] D), Module.Finite ℤ_[p] D ∧ ∃ ι : C →+* D, Function.Injective ι := by
  atlas_forward_decl GlobalTheory.CompletionEmbed.exists_finite_padicInt_domain
end

section
section
open IsLocalRing

namespace GlobalTheory.CurvePoint

theorem exists_ringHom_padicAlgCl_ne_zero : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  intro B _ _ _ _ _ hfin h hh

  set p := ringChar (ResidueField B) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (ResidueField B) 0 := by rw [← h0]; exact ringChar.charP _
    haveI : CharZero (ResidueField B) := CharP.charP_to_charZero _
    exact not_finite (ResidueField B)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right hp0
  haveI hF : Fact p.Prime := ⟨hp⟩
  have hpm : (p : B) ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.2 hp0

  obtain ⟨q, hq, hxq, hmax⟩ := GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' B (h * p) (mul_ne_zero hh hpB) (Ideal.mul_mem_left _ _ hpm)
  have hhq : h ∉ q := fun hq' => hxq (Ideal.mul_mem_right _ _ hq')
  have hpq : (p : B) ∉ q := fun hq' => hxq (Ideal.mul_mem_left _ _ hq')
  have hqm : q ≤ maximalIdeal B := le_maximalIdeal hq.ne_top
  set C := B ⧸ q
  haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.2 hq.ne_top
  haveI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let π : B →+* C := Ideal.Quotient.mk q
  have hπm : ∀ b ∈ maximalIdeal B, π b ∈ maximalIdeal C := by
    intro b hb hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : b * c' - 1 ∈ q := Ideal.Quotient.eq.1 (by simpa [π] using hc)
    have h2 : b * c' - 1 ∈ maximalIdeal B := hqm h1
    have h3 : b * c' ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hb
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ h3 h2))
  have hmC : ∀ c ∈ maximalIdeal C, ∃ b ∈ maximalIdeal B, π b = c := by
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, fun hb => hc ?_, rfl⟩
    exact hb.map π
  have hfinC : Finite (ResidueField C) := by
    let f : ResidueField B → ResidueField C :=
      Ideal.Quotient.lift (maximalIdeal B) ((residue C).comp π) (fun b hb => by
        rw [RingHom.comp_apply, residue_eq_zero_iff]; exact hπm b hb)
    refine Finite.of_surjective f ?_
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨residue B b, rfl⟩
  have hpC : (p : C) ≠ 0 := by
    rw [← map_natCast π, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hpq
  have hpmC : (p : C) ∈ maximalIdeal C := by rw [← map_natCast π]; exact hπm _ hpm
  have hdim : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C := by
    intro P hP hP0
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    have hlt : q < P.comap π := by
      refine lt_of_le_of_ne (fun b hb => ?_) (fun he => hP0 ?_)
      · show π b ∈ P; rw [Ideal.Quotient.eq_zero_iff_mem.2 hb]; exact P.zero_mem
      · rw [eq_bot_iff]; intro c hc
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        have : b ∈ q := he ▸ hc
        exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 this)
    have hc := hmax _ (Ideal.comap_isPrime π P) hlt
    intro c hc'
    obtain ⟨b, hb, rfl⟩ := hmC c hc'
    have : b ∈ P.comap π := hc ▸ hb
    exact this

  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hle, hP⟩ => ?_
    have hP0 : P ≠ ⊥ := fun h0 => hpC (by rw [h0] at hle; exact (Submodule.mem_bot _).1 (hle (Ideal.mem_span_singleton_self _)))
    exact (hdim P hP hP0).ge
  obtain ⟨D, _, _, _, hDfin, ι, hι⟩ := GlobalTheory.T.exists_finite_padicInt_domain_embedding p C hfinC hpC hpmC hdim
  have hpD : (p : D) ≠ 0 := by
    rw [← map_natCast ι]; exact fun h0 => hpC (hι (by rw [h0, map_zero]))
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain p D hpD
  refine ⟨p, hF, (φ.comp ι).comp π, fun b => hφ1 _, fun b hb => ?_, ?_⟩
  · have hc := hπm b hb
    have hcN : π b ^ N ∈ Ideal.span {(p : C)} := hN (Ideal.pow_mem_pow hc N)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcN
    have key : ‖(φ.comp ι) (π b)‖ ^ N < 1 ^ N := by
      rw [← norm_pow, ← map_pow, ← hd, map_mul, norm_mul, one_pow, map_natCast]
      calc ‖(φ.comp ι) d‖ * ‖(p : PadicAlgCl p)‖ ≤ 1 * ‖(p : PadicAlgCl p)‖ :=
            mul_le_mul_of_nonneg_right (hφ1 _) (norm_nonneg _)
        _ < 1 := by
          rw [one_mul]
          have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p) := by simp
          rw [← e, norm_algebraMap']; exact Padic.norm_p_lt_one
    exact lt_of_pow_lt_pow_left₀ N zero_le_one key
  · intro h0
    apply hhq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hι (hφ (by simpa using h0))

end GlobalTheory.CurvePoint
end

open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  atlas_forward_decl GlobalTheory.CurvePoint.exists_ringHom_padicAlgCl_ne_zero
end

section
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.Izumi

theorem essFiniteType_int_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  intro o Ω _ _ _ hA M x
  haveI : LocallyOfFiniteType M.s := M.lft
  let y : PrimeSpectrum o := M.s x
  letI A : Algebra o ((Sp o).presheaf.stalk (M.s x)) := StructureSheaf.stalkAlgebra _ y
  haveI : @IsLocalization.AtPrime o _ ((Sp o).presheaf.stalk (M.s x)) _ A y.asIdeal _ :=
    StructureSheaf.IsLocalization.to_stalk _ y
  let φ := @algebraMap o ((Sp o).presheaf.stalk (M.s x)) _ _ A
  have h₁ : (M.s.stalkMap x).hom.EssFiniteType := LocallyOfFiniteType.stalkMap M.s x
  have h₂ : φ.EssFiniteType :=
    RingHom.essFiniteType_algebraMap.2 (Algebra.EssFiniteType.of_isLocalization _ y.asIdeal.primeCompl)
  haveI : Algebra.FiniteType ℤ o := hA.ft
  have h₀ : (algebraMap ℤ o).EssFiniteType := RingHom.essFiniteType_algebraMap.2 inferInstance
  have h₃ : (M.stalkEquiv x).toRingHom.EssFiniteType :=
    (RingHom.FiniteType.of_surjective _ (M.stalkEquiv x).surjective).essFiniteType
  have h := ((h₀.comp h₂).comp h₁)
  have h' := h.comp h₃
  rw [← RingHom.essFiniteType_algebraMap]
  convert h'
  exact RingHom.ext_int _ _

end GlobalTheory.Izumi
end

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelLocalRing_essFiniteType_int : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), Algebra.EssFiniteType ℤ (M.O x) := by
  atlas_forward_decl GlobalTheory.Izumi.essFiniteType_int_O
end

section
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc

namespace GlobalTheory.ResFin

theorem finite_residueField_O : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω)
    (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  intro o Ω _ _ _ hA M x hx
  haveI : Algebra.FiniteType ℤ o := hA.ft
  haveI : LocallyOfFiniteType (spMap (algebraMap ℤ o)) :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).2 (RingHom.finiteType_algebraMap.2 inferInstance)
  haveI : LocallyOfFiniteType M.s := M.lft
  have h := finite_residueField_of_isClosed_of_locallyOfFiniteType_int (M.s ≫ spMap (algebraMap ℤ o)) x hx
  haveI : Finite (ResidueField (M.Z.presheaf.stalk x)) := h
  exact Finite.of_equiv _ (ResidueField.mapEquiv (M.stalkEquiv x)).toEquiv

end GlobalTheory.ResFin
end

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ZH GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → Finite (ResidueField (M.O x)) := by
  atlas_forward_decl GlobalTheory.ResFin.finite_residueField_O
end

section
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi

noncomputable section
namespace GlobalTheory.Izumi

theorem algebraMap_completion_injective : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A], Function.Injective (algebraMap A (AdicCompletion (maximalIdeal A) A)) := by
  intro A _ _ _
  have h : IsHausdorff (maximalIdeal A) A := inferInstance
  intro a b hab
  exact AdicCompletion.of_injective (maximalIdeal A) A (by simpa [AdicCompletion.algebraMap_apply] using hab)

theorem exists_sub_algebraMap_mem_maximalIdeal_completion : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (b : AdicCompletion (maximalIdeal A) A), ∃ a : A, b - algebraMap A (AdicCompletion (maximalIdeal A) A) a ∈ maximalIdeal (AdicCompletion (maximalIdeal A) A) := by
  intro A _ _ _ b
  set ψ := AdicCompletion.evalₐ (maximalIdeal A) (R := A) 1
  have hψ : ∀ r : A, ψ (algebraMap A (AdicCompletion (maximalIdeal A) A) r) = Ideal.Quotient.mk _ r := fun r => ψ.commutes r
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ b)
  refine ⟨a, ?_⟩
  by_contra hn
  have hu : IsUnit (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) := by
    simpa [mem_maximalIdeal, mem_nonunits_iff] using hn
  have h0 : ψ (b - algebraMap A (AdicCompletion (maximalIdeal A) A) a) = 0 := by
    rw [map_sub, hψ, ha, sub_self]
  have h1 := hu.map ψ
  rw [h0] at h1
  haveI : Nontrivial (A ⧸ maximalIdeal A ^ 1) := by
    rw [pow_one]
    exact Ideal.Quotient.nontrivial_iff.2 (maximalIdeal.isMaximal A).ne_top
  exact not_isUnit_zero h1

theorem norm_le_of_mem_iInf_map_smallIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (U : M.Z.Opens) (x : M.Z) (f : Ω) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ∀ ψ : AdicCompletion (maximalIdeal (M.O x)) (M.O x) →+* PadicAlgCl p, (∀ g, ‖ψ g‖ ≤ 1) → (∀ a : M.O x, ψ (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) a) = M.val (gPt p ≫ y) a) → ∀ G ∈ ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))), ‖ψ G‖ ≤ ‖M.val (gPt p ≫ y) f‖ := by
  intro o Ω _ _ _ _ M U x f p _ y hy ψ hψ1 hψv G hG
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  have hadd : ∀ a b : M.O x, ‖M.val (gPt p ≫ y) ((a + b : M.O x) : Ω)‖ ≤
      max ‖M.val (gPt p ≫ y) (a : Ω)‖ ‖M.val (gPt p ≫ y) (b : Ω)‖ := norm_val_add_le M hy
  have hmul : ∀ c a : M.O x, ‖M.val (gPt p ≫ y) ((c * a : M.O x) : Ω)‖ ≤ ‖M.val (gPt p ≫ y) (a : Ω)‖ :=
    norm_val_mul_le M hy
  obtain ⟨S, hS⟩ := (IsNoetherian.noetherian (maximalIdeal (M.O x)) : (maximalIdeal (M.O x)).FG)
  set ρ : ℝ := ((S.sup fun g => ‖M.val (gPt p ≫ y) (g : Ω)‖₊ : NNReal) : ℝ) with hρdef
  have hρ0 : 0 ≤ ρ := NNReal.coe_nonneg _
  have hρ1 : ρ < 1 := by
    rw [hρdef, ← NNReal.coe_one, NNReal.coe_lt_coe, Finset.sup_lt_iff (by simp)]
    intro g hg
    have hgm : g ∈ maximalIdeal (M.O x) := hS ▸ Submodule.subset_span hg
    have h1 := (hy.norm_val_lt_one_iff g.2).2 (by simpa using hgm)
    rw [← NNReal.coe_lt_coe, coe_nnnorm]
    simpa using h1
  have hρ : ∀ h ∈ maximalIdeal (M.O x), ‖M.val (gPt p ≫ y) (h : Ω)‖ ≤ ρ := by
    intro h hh
    rw [← hS] at hh
    induction hh using Submodule.span_induction with
    | mem g hg =>
      rw [hρdef, ← coe_nnnorm, NNReal.coe_le_coe]
      exact Finset.le_sup (f := fun g : M.O x => ‖M.val (gPt p ≫ y) (g : Ω)‖₊) hg
    | zero =>
      have h0 : ((0 : M.O x) : Ω) = 0 := rfl
      rw [h0, RatModel.val_zero, norm_zero]
      exact hρ0
    | add a b _ _ ha hb => exact (hadd a b).trans (max_le ha hb)
    | smul c a _ ha => exact (hmul c a).trans ha
  have hnu : ∀ h, NonUnitAt M x h → ∀ hO : h ∈ M.O x, (⟨h, hO⟩ : M.O x) ∈ maximalIdeal (M.O x) := by
    intro h hh hO
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    rcases hh.2 with h0 | hinv
    · subst h0
      have : (⟨0, hO⟩ : M.O x) = 0 := rfl
      rw [this] at hu
      exact not_isUnit_zero hu
    · obtain ⟨w, hw⟩ := hu.exists_right_inv
      have e : h * (w : Ω) = 1 := congrArg Subtype.val hw
      apply hinv
      rw [← eq_inv_of_mul_eq_one_right e]
      exact w.2
  have hN : ∀ N, ∀ g ∈ (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))),
      ‖ψ g‖ ≤ max ‖M.val (gPt p ≫ y) f‖ (ρ ^ N) := by
    intro N g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨k, hk, rfl⟩ := hg
      rw [hψv]
      rcases (mem_smallIdeal.1 hk) p y hy with h | ⟨h, hh, hle⟩
      · exact h.trans (le_max_left _ _)
      · refine le_max_of_le_right (hle.trans ?_)
        exact pow_le_pow_left₀ (norm_nonneg _) (hρ _ (hnu h hh hh.1)) N
    | zero => rw [map_zero, norm_zero]; exact le_max_of_le_right (pow_nonneg hρ0 N)
    | add a b _ _ ha hb => rw [map_add]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
    | smul c a _ ha =>
      rw [smul_eq_mul, map_mul, norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hψ1 c)).trans ha
  by_contra hlt
  push_neg at hlt
  have hpos : 0 < ‖ψ G‖ := lt_of_le_of_lt (norm_nonneg _) hlt
  obtain ⟨N, hNlt⟩ := exists_pow_lt_of_lt_one hpos hρ1
  have h1 := hN N G (Submodule.mem_iInf _ |>.1 hG N)
  rcases le_max_iff.1 h1 with h2 | h2
  · exact absurd h2 (not_le.2 hlt)
  · exact absurd h2 (not_le.2 hNlt)

set_option maxHeartbeats 800000 in

theorem iInf_map_smallIdeal_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  intro o Ω _ _ _ _ M hN U hU x hx f hf hf0
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  haveI : IsNoetherianRing (M.O x) := RatModel.isNoetherianRing_O M x
  haveI : IsIntegrallyClosed (M.O x) := RatModel.isIntegrallyClosed_O hN x
  haveI : CharZero (M.O x) := ⟨fun a b h => by
    have := congrArg Subtype.val h
    simpa using this⟩
  haveI : Algebra.EssFiniteType ℤ (M.O x) := GlobalTheory.T.modelLocalRing_essFiniteType_int o Ω M x
  haveI : Finite (ResidueField (M.O x)) := GlobalTheory.T.modelLocalRing_residueField_finite_of_closedPoint o Ω M x hx
  set A := M.O x with hA
  set R := AdicCompletion (maximalIdeal A) A with hR
  set φ := algebraMap A R with hφ
  obtain ⟨hdom, hic⟩ := GlobalTheory.AnalyticNormality.completion_isDomain_and_isIntegrallyClosed A
  haveI : IsNoetherianRing R := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion A _
  have hinj : Function.Injective φ := algebraMap_completion_injective A
  intro G hG
  by_contra hGf
  obtain ⟨s, hs0, hs⟩ := GlobalTheory.T.exists_nonzero_classicalPoint_of_localHom_avoiding o Ω M U hU x
  obtain ⟨B, _, _, _, _, ι, hιinj, hιloc, hιres, u, hu, hfu⟩ := GlobalTheory.T.exists_dominating_local_domain_eq_mul_maximal R (φ ⟨f, hf⟩) G hGf
  have hG0 : G ≠ 0 := by
    rintro rfl
    exact hGf (Submodule.zero_mem _)
  haveI : CharZero B := ⟨fun a b h => by
    have h1 : ι (φ (a : A)) = ι (φ (b : A)) := by simpa using h
    have h2 := hinj (hιinj h1)
    exact_mod_cast h2⟩
  haveI : Finite (ResidueField B) := by
    let g : A → ResidueField B := fun a => residue B (ι (φ a))
    have hg : Function.Surjective g := by
      intro c
      obtain ⟨b, rfl⟩ := residue_surjective c
      obtain ⟨r, hr⟩ := hιres b
      obtain ⟨a, ha⟩ := exists_sub_algebraMap_mem_maximalIdeal_completion A r
      refine ⟨a, ?_⟩
      have h1 : ι r - ι (φ a) ∈ maximalIdeal B := by
        rw [← map_sub]
        exact map_nonunit ι _ ha
      show residue B (ι (φ a)) = residue B b
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
      have := Ideal.add_mem _ h1 hr
      have e : ι (φ a) - b = -((ι r - ι (φ a)) + (b - ι r)) := by ring
      rw [e]
      exact (Ideal.neg_mem_iff _).2 this
    have hker : ∀ a a' : A, a - a' ∈ maximalIdeal A → g a = g a' := by
      intro a a' h
      show residue B _ = residue B _
      rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, ← map_sub, ← map_sub]
      refine map_nonunit ι _ (map_nonunit φ _ h)
    let g' : ResidueField A → ResidueField B := fun c => g (Classical.choose (residue_surjective c))
    refine Finite.of_surjective g' fun c => ?_
    obtain ⟨a, rfl⟩ := hg c
    refine ⟨residue A a, hker _ _ ?_⟩
    rw [← residue_eq_zero_iff, map_sub, Classical.choose_spec (residue_surjective (residue A a)), sub_self]
  have hh : ι (G * φ s) ≠ 0 := by
    rw [Ne, ← map_zero ι]
    intro h
    exact mul_ne_zero hG0 ((map_ne_zero_iff φ hinj).2 hs0) (hιinj h)
  obtain ⟨p, hp, χ, hχ1, hχm, hχh⟩ := GlobalTheory.T.exists_ringHom_padicAlgCl_ne_zero' B inferInstance (ι (G * φ s)) hh
  set ψ : R →+* PadicAlgCl p := χ.comp ι with hψ
  have hψ1 : ∀ g, ‖ψ g‖ ≤ 1 := fun g => hχ1 _
  have hψG : ψ G ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hψs : ψ (φ s) ≠ 0 := by
    intro h; apply hχh; rw [map_mul, map_mul]; simp [hψ] at h; simp [h]
  have hlt : ‖ψ (φ ⟨f, hf⟩)‖ < ‖ψ G‖ := by
    have e : ψ (φ ⟨f, hf⟩) = ψ G * χ u := by
      simp only [hψ, RingHom.comp_apply, hfu, map_mul]
    rw [e, norm_mul]
    have h1 : ‖χ u‖ < 1 := hχm u hu
    have h2 : 0 < ‖ψ G‖ := norm_pos_iff.2 hψG
    nlinarith [norm_nonneg (χ u)]
  let χ0 : A →+* OO p := (ψ.comp φ).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hψ1 _)
  have hloc : IsLocalHom χ0 := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hm : a ∈ maximalIdeal A := hna
    have h1 : ι (φ a) ∈ maximalIdeal B := map_nonunit ι _ (map_nonunit φ _ hm)
    have e : ((χ0 a : OO p) : PadicAlgCl p) = χ (ι (φ a)) := rfl
    have h2 : ‖((χ0 a : OO p) : PadicAlgCl p)‖ < 1 := by rw [e]; exact hχm _ h1
    exact (not_isUnit_OO_iff (χ0 a)).2 h2 ha
  have hχ0s : χ0 s ≠ 0 := fun h => hψs (congrArg Subtype.val h)
  obtain ⟨y, hy, hval⟩ := hs p χ0 hloc hχ0s
  have hb := norm_le_of_mem_iInf_map_smallIdeal o Ω M U x f p y hy ψ hψ1 (fun a => (hval a).symm) G hG
  have hf' := hval ⟨f, hf⟩
  simp only at hf'
  rw [hf'] at hb
  exact absurd hb (not_le.2 hlt)

end GlobalTheory.Izumi
end
end

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
open GlobalTheory.Izumi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ (f : Ω) (hf : f ∈ M.O x), f ≠ 0 → ⨅ N, (smallIdeal M U x f N).map (algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x))) ≤ Ideal.span {algebraMap (M.O x) (AdicCompletion (maximalIdeal (M.O x)) (M.O x)) ⟨f, hf⟩} := by
  atlas_forward_decl GlobalTheory.Izumi.iInf_map_smallIdeal_le_span
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

namespace GlobalTheory.Izumi

theorem small_mod_principal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  intro o Ω _ _ _ _ M hn U hU x hx f hf hf0
  haveI : IsDedekindDomain o := ArithBase.ded Ω
  haveI : IsNoetherianRing (M.O x) := M.isNoetherianRing_O x
  have hB := GlobalTheory.T.iInf_izumiSmallValueIdeal_map_le_span o Ω M hn U hU x hx f hf hf0
  choose C hC using exists_le_span_sup_pow (M.O x) (smallIdeal M U x f) ⟨f, hf⟩
    (smallIdeal_antitone U x f) (self_mem_smallIdeal U hf) hB
  refine ⟨C, fun e F hF => ?_⟩
  have hmem : F ∈ Ideal.span {(⟨f, hf⟩ : M.O x)} ⊔ maximalIdeal (M.O x) ^ e := hC e (mem_smallIdeal.2 hF)
  obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.1 hmem
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hm : Ideal.span {c : M.O x | ¬ IsUnit c} = maximalIdeal (M.O x) := Ideal.span_eq (maximalIdeal (M.O x))
  refine ⟨a, b, rfl, ?_⟩
  rw [hm]
  exact hb

end GlobalTheory.Izumi
end
end

open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.izumi_bound_mod_principal_ideal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (U : M.Z.Opens), (U : Set M.Z).Nonempty → ∀ (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ f ∈ M.O x, f ≠ 0 → ∃ C : ℕ → ℕ, ∀ (e : ℕ) (F : M.O x), (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U x y → ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) f‖ ∨ ∃ h, NonUnitAt M x h ∧ ‖M.val (gPt p ≫ y) F‖ ≤ ‖M.val (gPt p ≫ y) h‖ ^ C e) → ∃ a b : M.O x, (F : Ω) = a * f + b ∧ b ∈ Ideal.span {c : M.O x | ¬ IsUnit c} ^ e := by
  atlas_forward_decl GlobalTheory.Izumi.small_mod_principal
end
