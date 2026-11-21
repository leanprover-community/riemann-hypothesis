import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.ExistsCartierWithMultiplicities
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescentDataChartsCommon
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyDescentSeparatedEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpLawAndUnitAgreeOfOpenInDescentModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldPt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsCommMonObjOfDominant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalSmoothGroupOverNbhd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMemIdentityComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSemiStable
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IdentityComponentOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSection
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AmpleDivIffIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RaynaudLineBundleRelAmpleOfGenericSemiAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDivisorDominantPullbackWithClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformisationFiniteExtSameMumfordBundle

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.ChartPart

theorem flat_preimage_of_stalk {R Rc : Type} [CommRing R] [CommRing Rc] [IsLocalRing Rc] (ξ : Sp Rc ⟶ Sp R)
    (h : (Scheme.stalkClosedPointTo ξ).hom.Flat) : (Spec.preimage ξ).hom.Flat := by
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of Rc) ξ
  have h2 : Flat (Spec.map (Scheme.stalkClosedPointTo ξ)) := HasRingHomProperty.Spec_iff.mpr h
  have h3 : Flat ξ := by
    rw [← h1]
    exact MorphismProperty.comp_mem @Flat _ _ h2 (GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk _ _)
  rw [← Spec.map_preimage ξ] at h3
  exact HasRingHomProperty.Spec_iff.mp h3

theorem injective_of_flat {R Rc : Type} [CommRing R] [IsDomain R] [CommRing Rc] [Nontrivial Rc] (ρ : R →+* Rc)
    (h : ρ.Flat) : Function.Injective ρ := by
  algebraize [ρ]
  exact FaithfulSMul.algebraMap_injective R Rc

theorem isPullback_away {R Rc : Type} [CommRing R] [CommRing Rc] (ρ : R →+* Rc) (f : R) :
    IsPullback (spMap (Localization.awayMap ρ f)) (spMap (algebraMap Rc (Localization.Away (ρ f)))) (awayMap f)
      (spMap ρ) := by
  refine (IsOpenImmersion.isPullback _ _ _ _ ?_ ?_)
  · rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext r
    simp [Localization.awayMap, IsLocalization.Away.map]
  · rw [Scheme.Hom.opensRange_localizationAway (R := .of R), Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
    rfl

theorem exists_iso_preimage_basicOpen {Rc : Type} [CommRing Rc] (G : Over (Sp Rc)) (r : Rc) :
    ∃ e : (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).toScheme ≅
      pullback G.hom (spMap (algebraMap Rc (Localization.Away r))),
      e.hom ≫ pullback.fst _ _ = (G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι := by
  refine ⟨IsOpenImmersion.isoOfRangeEq _ (pullback.fst _ _) ?_, IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  rw [IsOpenImmersion.range_pullbackFst, Scheme.Hom.opensRange_localizationAway (R := .of Rc)]
  simp

theorem exists_pff_of_flat {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (hV : (V : Set Y).Nonempty)
    (φ : V.toScheme ⟶ X) [Flat φ] : ∃ θ : X.functionField →+* Y.functionField, PFF V.ι φ θ := by
  have hη : genericPoint Y ∈ V := ((genericPoint_spec Y).mem_open_set_iff V.isOpen).2 (by simpa using hV)
  have hrange : Set.range (gp Y) ⊆ Set.range V.ι := by
    rw [gp, Scheme.range_fromSpecStalk, Scheme.Opens.range_ι]
    exact fun y hy => hy.mem_open V.isOpen hη
  let l := IsOpenImmersion.lift V.ι (gp Y) hrange
  have hl : l ≫ V.ι = gp Y := IsOpenImmersion.lift_fac _ _ _
  have hl0 : V.ι (l (closedPoint Y.functionField)) = genericPoint Y := by
    have : (l ≫ V.ι) (closedPoint Y.functionField) = genericPoint Y := by
      rw [hl]; exact Scheme.fromSpecStalk_closedPoint
    exact this
  have hx : (l ≫ φ) (closedPoint Y.functionField) = genericPoint X := by
    obtain ⟨v, hv, hφv⟩ := Flat.generalizingMap φ
      (genericPoint_specializes (φ (l (closedPoint Y.functionField))))
    have h1 : V.ι v ⤳ genericPoint Y := hl0 ▸ hv.map V.ι.continuous
    have h2 : V.ι v = genericPoint Y := (h1.antisymm (genericPoint_specializes _)).eq
    have h3 : v = l (closedPoint Y.functionField) := V.ι.isOpenEmbedding.injective (h2.trans hl0.symm)
    subst h3
    exact hφv
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := Y.functionField) (l ≫ φ)
  revert hφ
  generalize Scheme.stalkClosedPointTo (R := Y.functionField) (l ≫ φ) = ψ
  revert ψ
  rw [show (l ≫ φ) (closedPoint Y.functionField) = genericPoint X from hx]
  intro ψ hψ
  exact ⟨ψ.hom, l, hl, hψ.symm⟩

end GlobalTheory.Desc.ChartPart

namespace GlobalTheory.Desc

open GlobalTheory.Desc.ChartPart in

theorem chart_part : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ [IsIntegral A.left] (x : Sp R) (C : Chart (awayMap f) A x) [IsIntegral C.G.left], ∃ (ρ : R →+* C.R) (V : C.G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* C.G.left.functionField), C.ξ = spMap ρ ∧ ρ.Flat ∧ (∀ z : C.G.left, z ∈ V ↔ ρ f ∉ (C.G.hom z).asIdeal) ∧ IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) ∧ (∀ (T : Scheme.{0}) (t : T ⟶ pullback C.G.hom (jK C.R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ C.α = t' ≫ φ) ∧ PFF V.ι φ θ := by
  intro R _ _ _ f hf0 A _ hAb _ x C _
  set ρ : R →+* C.R := (Spec.preimage C.ξ).hom with hρdef
  have hξ : C.ξ = spMap ρ := by
    rw [hρdef]; exact (Spec.map_preimage C.ξ).symm
  have hflat : ρ.Flat := flat_preimage_of_stalk C.ξ C.etc.1
  have hρf : ρ f ≠ 0 := fun h => hf0 (injective_of_flat ρ hflat (h.trans (map_zero ρ).symm))
  obtain ⟨_, hnorm⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing C.R

  let Rf := Localization.Away (ρ f)
  have hle : Submonoid.powers (ρ f) ≤ nonZeroDivisors C.R := powers_le_nonZeroDivisors_of_noZeroDivisors hρf
  haveI : IsDomain Rf := IsLocalization.isDomain_localization hle
  haveI : IsNoetherianRing Rf := IsLocalization.isNoetherianRing (Submonoid.powers (ρ f)) Rf inferInstance
  haveI : IsIntegrallyClosed Rf := isIntegrallyClosed_of_isLocalization Rf _ hle
  let ιf : C.R →+* Rf := algebraMap C.R Rf
  let g : Sp Rf ⟶ Sp (Localization.Away f) := spMap (Localization.awayMap ρ f)
  have sq2 := isPullback_away ρ f

  let K := FractionRing C.R
  have hu : IsUnit (algebraMap C.R K (ρ f)) :=
    IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective C.R K)).mpr hρf)
  letI : Algebra Rf K := (Localization.awayLift (algebraMap C.R K) (ρ f) hu).toAlgebra
  haveI : IsScalarTower C.R Rf K := IsScalarTower.of_algebraMap_eq fun r => by
    show algebraMap C.R K r = Localization.awayLift (algebraMap C.R K) (ρ f) hu (algebraMap C.R Rf r)
    exact (IsLocalization.Away.lift_eq (ρ f) hu r).symm
  haveI : IsFractionRing Rf K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (ρ f)) Rf K
  let j : Sp K ⟶ Sp Rf := spMap (algebraMap Rf K)
  have hjK : j ≫ spMap ιf = jK C.R := by
    simp only [j, spMap, ← Spec.map_comp]; congr 1; ext r
    exact (IsScalarTower.algebraMap_apply C.R Rf K r).symm
  have hy' : j ≫ g = C.y := by
    rw [← cancel_mono (awayMap f), Category.assoc, sq2.w, ← Category.assoc, hjK, C.hy, hξ]

  let GK := (Over.pullback (jK C.R)).obj C.G
  letI : GrpObj GK := Functor.grpObjObj
  let G₁ := (Over.pullback (spMap ιf)).obj C.G
  letI : GrpObj G₁ := Functor.grpObjObj
  have hG₁ : IsSemiAbelian G₁ := IsSemiAbelian.pullback (spMap ιf) C.G C.semi
  let H₁ := (Over.pullback g).obj A
  letI : GrpObj H₁ := Functor.grpObjObj
  have hH₁ : IsSemiAbelian H₁ :=
    IsSemiAbelian.pullback g A (isSemiAbelian_of_isAbelianScheme A hAb)
  let i₁ : GK.left ⟶ G₁.left := pullback.lift (pullback.fst C.G.hom (jK C.R)) (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hjK]; exact pullback.condition)
  have h₁ : IsGrpPullback GK G₁ j i₁ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback C.G (spMap ιf)) ?_ (pullback.lift_snd _ _ _)
    exact (isGrpPullback_pullback C.G (jK C.R)).congr hjK.symm (pullback.lift_fst _ _ _).symm
  let i₂ : GK.left ⟶ H₁.left := pullback.lift C.α (pullback.snd _ _ ≫ j)
    (by rw [Category.assoc, hy']; exact C.gen.1.w)
  have h₂ : IsGrpPullback GK H₁ j i₂ := by
    refine IsGrpPullback.cancel (isGrpPullback_pullback A g) ?_ (pullback.lift_snd _ _ _)
    exact C.gen.congr hy'.symm (pullback.lift_fst _ _ _).symm
  obtain ⟨E, ⟨hEm, hE⟩, -⟩ := semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions
    (GlobalTheory.IsNormalScheme.pred _) (IsGenericPointHom.fractionField Rf K) hG₁ hH₁ h₁ h₂

  haveI : IsMonHom E.hom := hEm
  let φ₁ : G₁.left ⟶ A.left := E.hom.left ≫ pullback.fst A.hom g
  have sq1 : IsPullback φ₁ G₁.hom A.hom g :=
    (((isGrpPullback_of_iso E).comp (isGrpPullback_pullback A g)).congr (Category.id_comp g) rfl).1

  let V : C.G.left.Opens := C.G.hom ⁻¹ᵁ PrimeSpectrum.basicOpen (ρ f)
  obtain ⟨e, he⟩ := exists_iso_preimage_basicOpen C.G (ρ f)
  let φ : V.toScheme ⟶ A.left := e.hom ≫ φ₁
  have sq0 : IsPullback e.hom (V.ι ≫ C.G.hom) (G₁.hom ≫ spMap ιf) (𝟙 _) := by
    refine IsPullback.of_horiz_isIso ⟨?_⟩
    show e.hom ≫ pullback.snd _ _ ≫ spMap ιf = (V.ι ≫ C.G.hom) ≫ 𝟙 _
    rw [Category.comp_id, ← pullback.condition, ← Category.assoc, he]
  have hcart : IsPullback φ (V.ι ≫ C.G.hom) (A.hom ≫ awayMap f) (spMap ρ) := by
    have := sq0.paste_horiz (sq1.paste_vert sq2)
    rwa [Category.id_comp] at this
  haveI : Flat (spMap ρ) := HasRingHomProperty.Spec_iff.mpr hflat
  haveI : Flat φ := MorphismProperty.of_isPullback hcart.flip inferInstance

  have hVne : (V : Set C.G.left).Nonempty := by
    let s : Sp C.R ⟶ C.G.left := (η[C.G] : 𝟙_ (Over (Sp C.R)) ⟶ C.G).left
    have hs : s ≫ C.G.hom = 𝟙 _ := Over.w η[C.G]
    let p : Sp C.R := (⊥ : PrimeSpectrum C.R)
    refine ⟨s p, ?_⟩
    show ρ f ∉ (C.G.hom (s p)).asIdeal
    rw [← Scheme.Hom.comp_apply, hs]
    exact fun h => hρf (Ideal.mem_bot.1 h)
  obtain ⟨θ, hθ⟩ := exists_pff_of_flat V hVne φ
  refine ⟨ρ, V, φ, θ, hξ, hflat, fun z => Iff.rfl, hcart, ?_, hθ⟩
  intro T t t' htt'
  have key : t ≫ i₁ = t' ≫ e.hom := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, htt', Category.assoc, he]
    · rw [← cancel_mono (spMap ιf)]
      have l : t ≫ i₁ ≫ pullback.snd _ _ ≫ spMap ιf = t ≫ pullback.fst _ _ ≫ C.G.hom := by
        simp only [i₁, pullback.lift_snd_assoc, Category.assoc, hjK]; rw [pullback.condition]
      have r : t' ≫ e.hom ≫ pullback.snd _ _ ≫ spMap ιf = t' ≫ V.ι ≫ C.G.hom := by
        rw [← pullback.condition, ← Category.assoc e.hom, he]
      simp only [Category.assoc]
      rw [l, r, ← Category.assoc t, htt', Category.assoc]
  have : t ≫ C.α = t ≫ i₂ ≫ pullback.fst A.hom g := by rw [pullback.lift_fst]
  rw [this, ← hE, Category.assoc, ← Category.assoc t, key, Category.assoc]

end GlobalTheory.Desc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.ExtDiv

open TopologicalSpace CartierDiv

theorem unitAt_map {Y V X : Scheme.{0}} [IsIntegral Y] [IsIntegral X] (i : V ⟶ Y) [IsOpenImmersion i]
    (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField) (h : PFF i φ θ) (v : V)
    {u : X.functionField} (hu : UnitAt (φ v) u) : UnitAt (i v) (θ u) := by
  obtain ⟨l, h₁, h₂⟩ := h
  obtain ⟨a, ha, rfl⟩ := hu
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes (i v))
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (φ v))
  have e₁ : Spec.map (inv (i.stalkMap v) ≫ sY) ≫ V.fromSpecStalk v = l := by
    rw [← cancel_mono i, h₁, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id_assoc]
    exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : φ.stalkMap v ≫ inv (i.stalkMap v) ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (φ v)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  refine ⟨(φ.stalkMap v ≫ inv (i.stalkMap v)).hom a, ha.map _, ?_⟩
  exact congrArg (fun f => CommRingCat.Hom.hom f a) e₂

variable {Y : Scheme.{0}} [IsIntegral Y] [IsLocallyNoetherian Y]

theorem finite_mult (D : CartierDiv Y) (U : Set Y) [NoetherianSpace U] :
    {z | z ∈ U ∧ D.mult z ≠ 0}.Finite := by
  classical
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible
    (D.supp.isClosed.preimage (continuous_subtype_val (p := (· ∈ U))))
  refine (hS.image fun T => if h : IsIrreducible ((Subtype.val : U → Y) '' T) then h.genericPoint
    else genericPoint Y).subset fun z hz => ?_
  obtain ⟨T, hT, hzT⟩ := Set.mem_sUnion.1 (hU.le
    (show (⟨z, hz.1⟩ : U) ∈ Subtype.val ⁻¹' (D.supp : Set Y) from mem_supp_of_mult_ne_zero hz.2))
  have hi' : IsIrreducible ((Subtype.val : U → Y) '' T) :=
    (hi T hT).image _ continuous_subtype_val.continuousOn
  refine ⟨T, hT, ?_⟩
  simp only [dif_pos hi']
  have hg := hi'.isGenericPoint_genericPoint_closure
  have h₁ : z ≤ hi'.genericPoint := hg.specializes (subset_closure ⟨_, hzT, rfl⟩)
  have hsub : closure ((Subtype.val : U → Y) '' T) ⊆ D.supp :=
    closure_minimal (by rintro _ ⟨t, ht, rfl⟩; exact hU.ge (Set.mem_sUnion.2 ⟨T, hT, ht⟩))
      D.supp.isClosed
  have h₂ : hi'.genericPoint < genericPoint Y := by
    refine lt_of_le_not_ge (genericPoint_specializes _) fun e => ?_
    have e' : _ = genericPoint Y := (Specializes.antisymm e (genericPoint_specializes _)).eq
    exact D.genericPoint_notMem_supp (e' ▸ hsub hg.mem)
  by_contra hne
  have h₃ := Order.coheight_add_one_le (lt_of_le_not_ge h₁ fun e =>
    hne (Specializes.antisymm h₁ e).eq)
  have h₄ := Order.coheight_add_one_le h₂
  rw [coheight_eq_one_of_mult_ne_zero hz.2] at h₃
  have h₅ : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add_left (le_add_self.trans h₄) 1).trans h₃
  exact absurd h₅ (by decide)

theorem locally_finite (O : Set Y) (c : Y → ℤ) (h0 : ∀ z, z ∉ O → c z = 0)
    (hc : ∀ z ∈ O, ∃ N : Set Y, IsOpen N ∧ z ∈ N ∧ ∃ E : CartierDiv Y, ∀ w ∈ N, c w = E.mult w)
    (y : Y) : ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite := by
  obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hy, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ y) isOpen_univ
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.1 (IsAffineOpen.isCompact hU)
  have : IsNoetherian U.toScheme := {}
  have : NoetherianSpace (U : Set Y) := inferInstanceAs (NoetherianSpace U.toScheme)
  choose! N hN hzN E hE using hc
  have hK : IsCompact ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)) :=
    (NoetherianSpace.isCompact _).image continuous_subtype_val
  have hKO : ∀ z ∈ ((Subtype.val : ↥(U : Set Y) → Y) '' ((Subtype.val : ↥(U : Set Y) → Y) ⁻¹' O)), z ∈ O := by
    rintro _ ⟨t, ht, rfl⟩; exact ht
  obtain ⟨t, ht, hcov⟩ := hK.elim_nhds_subcover N fun z hz =>
    (hN z (hKO z hz)).mem_nhds (hzN z (hKO z hz))
  refine ⟨U, hy, (t.finite_toSet.biUnion fun z _ => finite_mult (E z) (U : Set Y)).subset fun w hw => ?_⟩
  have hwO : w ∈ O := by_contra fun h => hw.2 (h0 w h)
  obtain ⟨z, hz, hwz⟩ := Set.mem_iUnion₂.1 (hcov ⟨⟨w, hw.1⟩, hwO, rfl⟩)
  exact Set.mem_iUnion₂.2 ⟨z, hz, hw.1, hE z (hKO z (ht z hz)) w hwz ▸ hw.2⟩

theorem exists_mult_eq (hY : ∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) (c : Y → ℤ)
    (h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1)
    (hf : ∀ y, ∃ W : Y.Opens, y ∈ W ∧ {z | z ∈ W ∧ c z ≠ 0}.Finite) :
    ∃ D : CartierDiv Y, ∀ z, D.mult z = c z := by
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose W hW hfin using hf
  have hE : ∀ y, ∃ E : CartierDiv Y, ∀ z ∈ W y, E.mult z = c z := fun y => by
    obtain ⟨E, hE⟩ := exists_mult_eq_of_locallyFactorial Y hY (fun z => if z ∈ W y then c z else 0)
      ((hfin y).subset fun z hz => by
        by_cases h : z ∈ W y
        · exact ⟨h, by simpa [h] using hz⟩
        · simp [h] at hz)
      fun z hz => h1 z fun h => hz (by simp [h])
    exact ⟨E, fun z hz => by rw [hE z, if_pos hz]⟩
  choose E hE using hE
  let D : CartierDiv Y := show cartierGroup Y from ⟨fun y => (E y).germ y, fun y => by
    obtain ⟨U, hU, g, hg⟩ := (E y).exists_isEqn_nhds y
    refine ⟨U ⊓ W y, ⟨hU, hW y⟩, g, fun z hz =>
      (MultEff.eff_supp_eq_of_mult Y (E z)).2.2.2 z g fun w hw => ?_⟩
    rw [hE z w (hw.mem_open (W z).isOpen (hW z)), ← hE y w (hw.mem_open (W y).isOpen hz.2),
      (hg w (hw.mem_open U.isOpen hz.1)).mult_eq]⟩
  refine ⟨D, fun z => ?_⟩
  obtain ⟨g, hg⟩ := (E z).exists_isEqn z
  rw [(show D.IsEqn z g from hg).mult_eq, ← hg.mult_eq, hE z z (hW z)]

end GlobalTheory.Desc.ExtDiv

open GlobalTheory.Desc.ExtDiv CartierDiv in

theorem GlobalTheory.Desc.exists_cartierDiv_closure : ∀ (Y V X : Scheme.{0}) [IsIntegral Y] [IsIntegral X] [IsLocallyNoetherian Y], (∀ y : Y, UniqueFactorizationMonoid (Y.presheaf.stalk y)) → ∀ (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), Flat φ → PFF i φ θ → ∀ D : CartierDiv X, ∃ D₁ : CartierDiv Y, PPull i φ θ D D₁ ∧ ∀ y : Y, y ∉ Set.range i → ringKrullDim (Y.presheaf.stalk y) = 1 → D₁.IsEqn y 1 := by
  intro Y V X _ _ _ hY i _ φ θ _ hθ D
  classical
  have : GlobalTheory.IsNormalScheme Y := ⟨fun x => inferInstance, fun x => by have := hY x; infer_instance⟩
  choose e he using fun v : V => D.exists_isEqn (φ v)
  let c : Y → ℤ := fun z => if h : z ∈ Set.range i then Scheme.ord (θ (e h.choose)) z else 0
  have h0 : ∀ z, z ∉ Set.range i → c z = 0 := fun z hz => dif_neg hz
  have h1 : ∀ z, c z ≠ 0 → Order.coheight z = 1 := fun z hz => by
    by_contra h
    apply hz
    simp only [c]
    split_ifs
    · exact Scheme.ord_eq_zero_of_coheight_neq_one h _
    · rfl
  have hc : ∀ v (g : X.functionFieldˣ), D.IsEqn (φ v) g → c (i v) = Scheme.ord (θ g) (i v) := by
    intro v g hg
    have hv : i v ∈ Set.range i := ⟨v, rfl⟩
    have e₀ : hv.choose = v := i.isOpenEmbedding.injective hv.choose_spec
    have hu := (unitAt_map i φ θ hθ v (hg.iff_unitAt.1 (he v))).ord_eq_zero
    simp only [c, dif_pos hv, e₀]
    rw [← div_mul_cancel₀ (e v : X.functionField) g.ne_zero, map_mul,
      Scheme.ord_mul ((map_ne_zero θ).2 (div_ne_zero (e v).ne_zero g.ne_zero))
        ((map_ne_zero θ).2 g.ne_zero), hu, zero_add]
  obtain ⟨D₁, hD₁⟩ := exists_mult_eq hY c h1 (locally_finite (Set.range i) c h0 (by
    rintro _ ⟨v, rfl⟩
    obtain ⟨U, hU, g, hg⟩ := D.exists_isEqn_nhds (φ v)
    refine ⟨i '' (φ ⁻¹ᵁ U), i.isOpenEmbedding.isOpenMap _ (φ ⁻¹ᵁ U).isOpen, ⟨v, hU, rfl⟩,
      principal (Units.map θ.toMonoidHom g), ?_⟩
    rintro _ ⟨w, hw, rfl⟩
    rw [hc w g (hg _ hw), (isEqn_principal _ _).mult_eq]
    rfl))
  refine ⟨D₁, fun v g hg => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_,
    fun y hy hd => (MultEff.eff_supp_eq_of_mult Y D₁).2.2.2 _ _ fun w hw => ?_⟩
  · obtain ⟨w, rfl⟩ : w ∈ Set.range i := hw.mem_open i.isOpenEmbedding.isOpen_range ⟨v, rfl⟩
    obtain ⟨U, hU, hgU⟩ := hg.exists_nhds
    have hwv := (i.isOpenEmbedding.isInducing.specializes_iff.1 hw).map φ.continuous
    rw [hD₁, hc w g (hgU _ (hwv.mem_open U.isOpen hU))]
    rfl
  · rw [hD₁, Units.val_one, MultEff.ord_one]
    by_contra hne
    have hw1 := h1 w (Ne.symm hne)
    have hy1 : Order.coheight y = 1 := by
      rw [ringKrullDim_stalk_eq_coheight] at hd
      exact_mod_cast hd
    have hlt : y < w := lt_of_le_not_ge hw fun e =>
      hne ((Specializes.antisymm hw e).eq ▸ (h0 y hy).symm)
    have h₃ := Order.coheight_add_one_le hlt
    rw [hw1, hy1] at h₃
    exact absurd h₃ (by decide)
end

section
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionFib

theorem exists_ringHom_extend {A R Ω : Type} [CommRing A] [IsLocalRing A] [CommRing R] [IsLocalRing R] [Field Ω]
    [IsAlgClosed Ω] (φ : A →+* R) [IsLocalHom φ] (hφ : ((residue R).comp φ).Finite) (ψ : A →+* Ω) [IsLocalHom ψ] :
    ∃ u : R →+* Ω, u.comp φ = ψ := by
  letI : Algebra (ResidueField A) (ResidueField R) := (ResidueField.map φ).toAlgebra
  letI : Algebra (ResidueField A) Ω := (ResidueField.lift ψ).toAlgebra
  have hf : (ResidueField.map φ).Finite := by
    rw [← ResidueField.map_comp_residue] at hφ
    exact RingHom.Finite.of_comp_finite hφ
  haveI : Module.Finite (ResidueField A) (ResidueField R) := hf
  let l : ResidueField R →ₐ[ResidueField A] Ω := IsAlgClosed.lift
  refine ⟨l.toRingHom.comp (residue R), RingHom.ext fun a => ?_⟩
  exact l.commutes (residue A a)

theorem exists_geom_lift {X S : Scheme.{0}} {j : X ⟶ S} {A : Over X} [GrpObj A] {x : S} (C : Chart j A x) (Ω : Type)
    [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ S) (hp : p (closedPoint Ω) = x) : ∃ q : Sp Ω ⟶ Sp C.R, q ≫ C.ξ = p := by
  obtain ⟨ψ, hl, hψ⟩ : ∃ ψ : S.presheaf.stalk (C.ξ (closedPoint C.R)) ⟶ CommRingCat.of Ω,
      IsLocalHom ψ.hom ∧ Spec.map ψ ≫ S.fromSpecStalk _ = p := by
    rw [C.centre, ← hp]
    exact ⟨Scheme.stalkClosedPointTo p, inferInstance, Scheme.Spec_stalkClosedPointTo_fromSpecStalk p⟩
  obtain ⟨u, hu⟩ := exists_ringHom_extend (Scheme.stalkClosedPointTo C.ξ).hom C.etc.2.2 ψ.hom
  refine ⟨spMap u, ?_⟩
  have e : Scheme.stalkClosedPointTo C.ξ ≫ CommRingCat.ofHom u = ψ := CommRingCat.hom_ext hu
  rw [← hψ, ← e, Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]

theorem isPullback_of_mono {A P G S X : Scheme.{0}} {i : A ⟶ P} {a : A ⟶ S} {p : P ⟶ X} {j : S ⟶ X} (κ : G ⟶ P)
    [Mono κ] {e : A ⟶ G} (h : IsPullback i a p j) (he : e ≫ κ = i) : IsPullback e a (κ ≫ p) j := by
  have w : e ≫ κ ≫ p = a ≫ j := by rw [← h.w, ← he, Category.assoc]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => h.lift (s.fst ≫ κ) s.snd (by rw [Category.assoc]; exact s.condition))
    (fun s => ?_) (fun s => h.lift_snd _ _ _) (fun s t h₁ h₂ => ?_)⟩⟩
  · rw [← cancel_mono κ, Category.assoc, he]
    exact h.lift_fst _ _ _
  · apply h.hom_ext
    · rw [h.lift_fst, ← h₁, Category.assoc, he]
    · rw [h.lift_snd, h₂]

variable {σ : Setup} (E : Emb σ)

theorem rho_closedPoint (x : Sp σ.R) : spMap (σ.ρ x) (closedPoint _) = x := by
  rw [← σ.hρ]; exact (σ.C x).centre

theorem range_subset : Set.range E.ιA ⊆ E.U := by
  rintro _ ⟨a, rfl⟩
  obtain ⟨v, h1, h2⟩ := Scheme.exists_preimage_of_isPullback (σ.cart ((σ.A.hom ≫ awayMap σ.f) a)) a (closedPoint _)
    (rho_closedPoint _).symm
  refine ⟨_, (σ.V _).ι v, h2, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← E.onV, Scheme.Hom.comp_apply, h1]

theorem isPullback_chart (hC : σ.Common) {G : Scheme.{0}} (κ : G ⟶ E.P) [IsOpenImmersion κ] (hκ : Set.range κ = E.U)
    (x : Sp σ.R) : ∃ m : (σ.C x).G.left ⟶ G, m ≫ κ = E.emb x ∧
      IsPullback m (σ.C x).G.hom (κ ≫ E.p) (spMap (σ.ρ x)) := by
  obtain ⟨w, hw⟩ := E.openIn x
  let l := pullback.lift (E.emb x) (σ.C x).G.hom w
  have l1 : l ≫ pullback.fst _ _ = E.emb x := pullback.lift_fst _ _ _
  have l2 : l ≫ pullback.snd _ _ = (σ.C x).G.hom := pullback.lift_snd _ _ _
  have hr : Set.range (E.emb x) ⊆ Set.range κ := by
    rintro _ ⟨y, rfl⟩
    have e1 : pullback.fst E.p (spMap (σ.ρ x)) (l y) = E.emb x y := by rw [← Scheme.Hom.comp_apply, l1]
    rw [hκ, ← e1]
    exact (Emb.fst_mem_U_iff σ E hC x (l y)).2 ⟨y, e1.symm, by rw [← Scheme.Hom.comp_apply, l2]⟩
  refine ⟨IsOpenImmersion.lift κ _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have sq : IsPullback (IsOpenImmersion.lift κ _ hr) l κ (pullback.fst E.p (spMap (σ.ρ x))) := by
    refine IsOpenImmersion.isPullback _ _ _ _ (by rw [l1, IsOpenImmersion.lift_fac]) ?_
    ext z
    constructor
    · intro hz
      have hz' : pullback.fst E.p (spMap (σ.ρ x)) z ∈ E.U := hκ ▸ hz
      obtain ⟨x', y', hy', e⟩ := hz'
      obtain ⟨Ω, _, s, t', o, hst, hs, ht⟩ :=
        Sat.exists_field_pt (pullback.fst E.p (spMap (σ.ρ x))) (E.emb x') z y' e.symm
      obtain ⟨w', -⟩ := E.openIn x'
      obtain ⟨t, h1, h2⟩ := (Sat.transfer σ E hC x x' Ω (s ≫ pullback.snd _ _) (t' ≫ (σ.C x').G.hom) o
        (by rw [Scheme.Hom.comp_apply, ht]; exact hy')
        (by rw [Category.assoc, Category.assoc, ← pullback.condition, ← w', reassoc_of% hst])).2 t' rfl
      have : t ≫ l = s := by
        apply pullback.hom_ext
        · rw [Category.assoc, l1, h2, hst]
        · rw [Category.assoc, l2, h1]
      exact ⟨t o, by rw [← Scheme.Hom.comp_apply, this, hs]⟩
    · rintro ⟨y, rfl⟩
      exact hr ⟨y, by rw [← Scheme.Hom.comp_apply, l1]⟩
  have := sq.paste_vert (IsPullback.of_hasPullback E.p (spMap (σ.ρ x)))
  rwa [l2] at this

theorem alpha_comp (x : Sp σ.R) :
    (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
  have hr : Set.range (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) ⊆ Set.range (σ.V x).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (σ.hV x _).2 ?_
    have e : spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z)) =
        awayMap σ.f ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)) := by
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
        pullback.condition_assoc, (σ.C x).hy, σ.hρ]
    intro hm
    have h1 : σ.f ∈ (spMap (σ.ρ x) ((σ.C x).G.hom (pullback.fst (σ.C x).G.hom (jK (σ.C x).R) z))).asIdeal := hm
    rw [e] at h1
    have h2 : algebraMap σ.R (Localization.Away σ.f) σ.f ∈
      ((σ.C x).y (pullback.snd (σ.C x).G.hom (jK (σ.C x).R) z)).asIdeal := h1
    exact (PrimeSpectrum.isPrime _).ne_top (Ideal.eq_top_of_isUnit_mem _ h2 (IsLocalization.Away.algebraMap_isUnit σ.f))
  have h := σ.compat x _ (𝟙 _) (IsOpenImmersion.lift (σ.V x).ι _ hr)
    (by rw [Category.id_comp, IsOpenImmersion.lift_fac])
  rw [Category.id_comp] at h
  rw [h, Category.assoc, E.onV, IsOpenImmersion.lift_fac_assoc]

theorem isSemiAbelian_of_ext (hC : σ.Common) (G : Over (Sp σ.R)) [GrpObj G] (κ : G.left ⟶ E.P) [IsOpenImmersion κ]
    (hκ : Set.range κ = E.U) (hG : G.hom = κ ≫ E.p) [Smooth G.hom] [QuasiCompact G.hom] {e : σ.A.left ⟶ G.left}
    (he : e ≫ κ = E.ιA) (h : IsGrpPullback σ.A G (awayMap σ.f) e) : IsSemiAbelian G := by
  have := E.sep
  have hsep : IsSeparated G.hom := by rw [hG]; infer_instance
  have key : ∀ x, ∃ m, IsGrpPullback (σ.C x).G G (σ.C x).ξ m := fun x => by
    obtain ⟨m, hm, sq⟩ := isPullback_chart E hC κ hκ x
    rw [← hG, ← σ.hρ] at sq
    obtain ⟨_, _⟩ := ExtUnique.spec_fractionRing (σ.C x).R (FractionRing (σ.C x).R)
    have := (σ.C x).semi.smooth
    refine ⟨m, ZJ.isGrpPullback_of_dominant (jK (σ.C x).R) sq (((σ.C x).gen.comp h).congr (σ.C x).hy ?_)⟩
    rw [← cancel_mono κ, Category.assoc, Category.assoc, he, hm]
    exact alpha_comp E x
  have fib : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (p : Sp Ω ⟶ Sp σ.R), ∃ (x : Sp σ.R) (q : Sp Ω ⟶ Sp (σ.C x).R)
      (i : (Over.pullback q).obj (σ.C x).G ≅ (Over.pullback p).obj G), IsMonHom i.hom := fun Ω _ _ p => by
    obtain ⟨q, hq⟩ := exists_geom_lift (σ.C (p (closedPoint Ω))) Ω p rfl
    obtain ⟨m, hm⟩ := key (p (closedPoint Ω))
    obtain ⟨i, hi, -⟩ := grpPullback_iso (((isGrpPullback_pullback _ q).comp hm).congr hq rfl)
      (isGrpPullback_pullback G p)
    exact ⟨_, q, i, hi⟩
  refine ⟨?_, ‹_›, hsep, ‹_›, SemiAbelianCompare.geometricallyConnected_of_isAlgClosed _ fun Ω _ _ p => ?_,
    fun Ω _ _ p => ?_⟩
  · have := σ.ab.comm
    have : IsSchemeTheoreticallyDominant (awayMap σ.f) :=
      ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _
        (IsLocalization.injective (Localization.Away σ.f) (powers_le_nonZeroDivisors_of_noZeroDivisors σ.hf))
    exact SplitExtComm.isCommMonObj_of_dominant h
  · obtain ⟨x, q, i, -⟩ := fib Ω p
    have := (σ.C x).semi.geomConnected
    have : ConnectedSpace ((Over.pullback q).obj (σ.C x).G).left :=
      GeometricallyConnected.geometrically_connectedSpace (f := (σ.C x).G.hom) q _ _ (IsPullback.of_hasPullback _ _)
    have := isIso_inv_left i.symm
    exact (i.symm.inv.left).surjective.connectedSpace (i.symm.inv.left).continuous
  · obtain ⟨x, q, i, hi⟩ := fib Ω p
    obtain ⟨T⟩ := (σ.C x).semi.fibres Ω q
    exact ⟨torusExtOfIso i T⟩

end GlobalTheory.Desc.UnionFib

namespace GlobalTheory.Desc

open UnionFib GroupGlue in

theorem Emb.hasExt_of_locGrp : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  intro σ E hC hloc
  choose g hg H iH h hL hr using hloc
  have oi : ∀ x, IsOpenImmersion (h x) := fun x => (hL x).2.2.1
  have ra : ∀ a : σ.R, Set.range (awayMap a) = {z : Sp σ.R | a ∉ z.asIdeal} := fun a =>
    PrimeSpectrum.localization_away_comap_range (Localization.Away a) a
  have hU : IsOpen E.U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    exact ⟨Set.range (h (E.p z)), by rw [hr]; exact Set.inter_subset_left, (h _).isOpenEmbedding.isOpen_range,
      by rw [hr]; exact ⟨hz, hg _⟩⟩
  let U : E.P.Opens := ⟨E.U, hU⟩
  have hι : Set.range U.ι = E.U := Scheme.Opens.range_ι U
  let G : Over (Sp σ.R) := Over.mk (U.ι ≫ E.p)
  let 𝒰 : (Sp σ.R).OpenCover := Scheme.Cover.mkOfCovers (Sp σ.R) (fun x => Sp (Localization.Away (g x)))
    (fun x => awayMap (g x)) (fun x => by
      obtain ⟨y, hy⟩ : x ∈ Set.range (awayMap (g x)) := by rw [ra]; exact hg x
      exact ⟨x, y, hy⟩)
  have hs : ∀ x, Set.range (h x) ⊆ Set.range U.ι := fun x => by rw [hι, hr]; exact Set.inter_subset_left
  let H' : ∀ i : 𝒰.I₀, Over (𝒰.X i) := H
  letI iH' : ∀ i : 𝒰.I₀, GrpObj (H' i) := iH
  let ψ : ∀ i : 𝒰.I₀, (H' i).left ⟶ G.left := fun x => IsOpenImmersion.lift U.ι (h x) (hs x)
  have hψι : ∀ x : Sp σ.R, ψ x ≫ U.ι = h x := fun x => IsOpenImmersion.lift_fac _ _ _
  have hψ : ∀ i, IsPullback (ψ i) (H' i).hom G.hom (𝒰.f i) := fun (x : Sp σ.R) => by
    have : IsOpenImmersion (ψ x ≫ U.ι) := by rw [hψι]; exact oi x
    have : IsOpenImmersion (ψ x) := IsOpenImmersion.of_comp _ U.ι
    refine (IsOpenImmersion.isPullback (H x).hom (ψ x) (awayMap (g x)) (U.ι ≫ E.p) ?_ ?_).flip
    · rw [reassoc_of% (hψι x)]; exact (hL x).2.2.2.1
    · ext z
      constructor
      · intro hz
        have hz' : E.p (U.ι z) ∈ Set.range (awayMap (g x)) := hz
        rw [ra] at hz'
        obtain ⟨y, hy⟩ : U.ι z ∈ Set.range (h x) := by rw [hr]; exact ⟨z.2, hz'⟩
        refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
        rw [← hy, ← hψι]; rfl
      · rintro ⟨y, rfl⟩
        refine ⟨(H x).hom y, ?_⟩
        rw [← Scheme.Hom.comp_apply, ← (hL x).2.2.2.1, ← hψι]; rfl
  have op : ∀ x, OpenIn (h x) (H x).hom E.p (awayMap (g x)) := fun x => by
    refine ⟨(hL x).2.2.2.1, ?_⟩
    have : IsOpenImmersion (pullback.lift (h x) (H x).hom (hL x).2.2.2.1 ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact oi x
    exact IsOpenImmersion.of_comp _ (pullback.fst E.p (awayMap (g x)))
  have hm : MulCompat ψ := fun (x y : Sp σ.R) S u v a a' b b' e₁ e₂ => by
    have := (hL x).1
    have := (hL y).1
    have k := (GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ (awayMap (g x)) (awayMap (g y)) (H x) (H y) (h x) (h y) inferInstance inferInstance
      inferInstance inferInstance (op x) (op y) (hL x).2.2.2.2 (hL y).2.2.2.2).1 S u v a a' b b'
      (by rw [← hψι, ← hψι, reassoc_of% e₁]) (by rw [← hψι, ← hψι, reassoc_of% e₂])
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, hψι, hψι]
    exact k
  obtain ⟨iG, hG⟩ := exists_grpObj hm hψ
  have hA : Set.range E.ιA ⊆ Set.range U.ι := by rw [hι]; exact range_subset E
  let e : σ.A.left ⟶ G.left := IsOpenImmersion.lift U.ι _ hA
  have he : e ≫ U.ι = E.ιA := IsOpenImmersion.lift_fac _ _ _
  have hp : IsGrpPullback σ.A G (awayMap σ.f) e := by
    refine ⟨isPullback_of_mono U.ι E.cartA he, fun T a b a₀ b₀ ha hb => ?_⟩
    refine ext_small 𝒰 (T.hom ≫ awayMap σ.f) fun (x : Sp σ.R) S k u hu => ?_
    obtain ⟨c, hc⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu a₀
    obtain ⟨d, hd⟩ := exists_rep hψ (T := Over.mk (T.hom ≫ awayMap σ.f)) hu b₀
    rw [← rep_mul hG (T := Over.mk (T.hom ≫ awayMap σ.f)) hu hc hd]
    let r : Over.mk (k ≫ T.hom) ⟶ T := Over.homMk k rfl
    have k' := (hL x).2.2.2.2 S u (k ≫ T.hom) c d (r ≫ a) (r ≫ b)
      (by rw [← hψι, reassoc_of% hc, ha, ← he]; simp [r]) (by rw [← hψι, reassoc_of% hd, hb, ← he]; simp [r])
    rw [← MonObj.comp_mul] at k'
    rw [← cancel_mono U.ι, Category.assoc, hψι, Category.assoc, Category.assoc, he]
    exact k'.trans (Category.assoc _ _ _)
  have : IsZariskiLocalAtTarget @Smooth.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Smooth)
  have : IsZariskiLocalAtTarget @QuasiCompact.{0} := by
    set_option backward.isDefEq.respectTransparency.types false in exact inferInstance
  have : Smooth G.hom := of_charts @Smooth hψ fun x => (hL x).1
  have : QuasiCompact G.hom := of_charts @QuasiCompact hψ fun x => (hL x).2.1
  exact ⟨G, iG, e, isSemiAbelian_of_ext E hC G U.ι hι rfl he hp, hp⟩

end GlobalTheory.Desc
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_of_local_groups : ∀ (σ : Setup) (E : Emb σ), σ.Common → (∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal}) → HasExt (awayMap σ.f) σ.A := by
  atlas_forward_decl GlobalTheory.Desc.Emb.hasExt_of_locGrp
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

variable {S P : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [GrpObj H₂] {h₁ : H₁.left ⟶ P} {h₂ : H₂.left ⟶ P}
  {pS : P ⟶ S}

theorem mul_mem_range (e₁ : h₁ ≫ pS = H₁.hom) (e₂ : h₂ ≫ pS = H₂.hom) [IsOpenImmersion h₂]
    (hm : MulAgree H₁ H₂ h₁ h₂) {T : Scheme.{0}} {t : T ⟶ S} (a b : Over.mk t ⟶ H₁)
    (ha : ∀ y, h₁ (a.left y) ∈ Set.range h₂) (hb : ∀ y, h₁ (b.left y) ∈ Set.range h₂) :
    ∀ y, h₁ ((a * b).left y) ∈ Set.range h₂ := by
  have lift : ∀ c : Over.mk t ⟶ H₁, (∀ y, h₁ (c.left y) ∈ Set.range h₂) →
      ∃ c' : Over.mk t ⟶ H₂, c.left ≫ h₁ = c'.left ≫ h₂ := by
    intro c hc
    let c'' := IsOpenImmersion.lift h₂ (c.left ≫ h₁) (by rintro _ ⟨y, rfl⟩; exact hc y)
    have ec : c'' ≫ h₂ = c.left ≫ h₁ := IsOpenImmersion.lift_fac _ _ _
    refine ⟨Over.homMk c'' ?_, ec.symm⟩
    show c'' ≫ H₂.hom = t
    rw [← e₂, ← Category.assoc, ec, Category.assoc, e₁, Over.w c]
    rfl
  obtain ⟨a', ea⟩ := lift a ha
  obtain ⟨b', eb⟩ := lift b hb
  have := hm T t t a b a' b' ea eb
  intro y
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]
  exact ⟨_, rfl⟩

end GlobalTheory.OpenSubgrp

namespace GlobalTheory.OpenSubgrp

attribute [local instance] Over.cartesianMonoidalCategory

theorem comp_inv' {S : Scheme.{0}} {G : Over S} [GrpObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G) :
    ρ ≫ x⁻¹ = (ρ ≫ x)⁻¹ :=
  (Category.assoc _ _ _).symm

theorem range_subset : ∀ (S P : Scheme.{0}) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂] (h₁ : H₁.left ⟶ P)
    (h₂ : H₂.left ⟶ P), ∀ pS : P ⟶ S, h₁ ≫ pS = H₁.hom → h₂ ≫ pS = H₂.hom → IsOpenImmersion h₁ →
    IsOpenImmersion h₂ → Smooth H₁.hom → GeometricallyConnected H₁.hom → MulAgree H₁ H₂ h₁ h₂ →
    OneAgree (𝟙 S) (𝟙 S) H₁ H₂ h₁ h₂ → Set.range h₁ ⊆ Set.range h₂ := by
  intro S P H₁ H₂ _ _ h₁ h₂ pS e₁ e₂ _ _ _ _ hm ho
  have : GeometricallyIntegral H₁.hom := GlobalTheory.grpObj_geometricallyIntegral_of_smooth S H₁
  let WO : H₁.left.Opens := h₁ ⁻¹ᵁ h₂.opensRange
  have hW : ∀ x, x ∈ WO ↔ h₁ x ∈ Set.range h₂ := fun x => Iff.rfl

  have hone : ∀ s : S, ∃ y ∈ WO, H₁.hom y = s := by
    intro s
    refine ⟨(1 : Over.mk (𝟙 S) ⟶ H₁).left s, ?_, ?_⟩
    · rw [hW, ← Scheme.Hom.comp_apply, ho S (𝟙 S) (𝟙 S) rfl, Scheme.Hom.comp_apply]
      exact ⟨_, rfl⟩
    · rw [← Scheme.Hom.comp_apply, Over.w]; rfl
  let f := fst H₁ H₁
  let g := snd H₁ H₁
  let a : H₁ ⊗ H₁ ⟶ H₁ := g⁻¹ * f
  let O : (H₁ ⊗ H₁).left.Opens := a.left ⁻¹ᵁ WO ⊓ g.left ⁻¹ᵁ WO
  let Y : Over S := Over.mk (O.ι ≫ (H₁ ⊗ H₁).hom)
  let j : Y ⟶ H₁ ⊗ H₁ := Over.homMk O.ι rfl
  have e1 : (j ≫ g) * (j ≫ a) = j ≫ f := by
    rw [MonObj.comp_mul, comp_inv', mul_inv_cancel_left]
  have inW : ∀ y, h₁ ((j ≫ f).left y) ∈ Set.range h₂ := by
    rw [← e1]
    exact OpenSubgrp.mul_mem_range e₁ e₂ hm (j ≫ g) (j ≫ a) (fun y => y.2.2) (fun y => y.2.1)
  have hg : GeometricallyIrreducible f.left :=
    inferInstanceAs (GeometricallyIrreducible (pullback.fst H₁.hom H₁.hom))
  have m2 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, g.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨y, hy, e⟩ := hone (H₁.hom z)
    obtain ⟨w, hw1, hw2⟩ := Scheme.Pullback.exists_preimage_pullback z y e.symm
    exact ⟨w, by rw [← hw2] at hy; exact hy, hw1⟩
  have m1 : ∀ z : H₁.left, ∃ w : (H₁ ⊗ H₁).left, a.left w ∈ WO ∧ f.left w = z := by
    intro z
    obtain ⟨w, hw1, hw2⟩ := m2 z
    let b : H₁ ⊗ H₁ ⟶ H₁ ⊗ H₁ := lift f (f * g⁻¹)
    have b1 : b ≫ a = g := by
      rw [MonObj.comp_mul, comp_inv', lift_fst, lift_snd, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    have b2 : b ≫ f = f := lift_fst _ _
    refine ⟨b.left w, ?_, ?_⟩
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b1]; exact hw1
    · rw [← Scheme.Hom.comp_apply, ← Over.comp_left, b2]; exact hw2
  rintro _ ⟨z, rfl⟩
  have hi : IsIrreducible (f.left ⁻¹' {z}) := by
    rw [← f.left.range_fiberι, ← Set.image_univ]
    exact (IrreducibleSpace.isIrreducible_univ _).image _ (f.left.fiberι z).continuous.continuousOn
  obtain ⟨w, hw, e⟩ := m1 z
  obtain ⟨w', hw', e'⟩ := m2 z
  obtain ⟨y, hy, k₁, k₂⟩ := hi.2 _ _ (a.left ⁻¹ᵁ WO).2 (g.left ⁻¹ᵁ WO).2 ⟨w, e, hw⟩ ⟨w', e', hw'⟩
  have := inW ⟨y, k₁, k₂⟩
  convert this using 2
  exact hy.symm

end GlobalTheory.OpenSubgrp
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.CxPts GlobalTheory.Points
open scoped CategoryTheory.Obj
open GlobalTheory.MBLit

noncomputable section

namespace GlobalTheory.SemiStableId

def transportExt {K : Type} [Field K] {G₁ H : Over (Spec (.of K))} [GrpObj G₁] [GrpObj H]
    (E : TorusExtension G₁) (e : G₁ ≅ H) [IsMonHom e.hom] : TorusExtension H where
  X := E.X
  addCommGroup := E.addCommGroup
  free := E.free
  finite := E.finite
  B := E.B
  grpB := E.grpB
  isAbelian := E.isAbelian
  q := e.inv ≫ E.q
  q_hom := by have := E.q_hom; infer_instance
  q_flat := by have := E.q_flat; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Flat (e.inv.left ≫ E.q.left); infer_instance
  q_surjective := by have := E.q_surjective; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show Surjective (e.inv.left ≫ E.q.left); infer_instance
  q_quasiCompact := by
    have := E.q_quasiCompact; have : IsIso e.inv.left := inferInstanceAs (IsIso ((Over.forget _).map e.inv)); show QuasiCompact (e.inv.left ≫ E.q.left); infer_instance
  i := E.i ≫ e.hom
  i_hom := by have := E.i_hom; infer_instance
  isKernel := by
    have h2 : IsPullback e.hom E.q (e.inv ≫ E.q) (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩
    simpa using E.isKernel.paste_horiz h2

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

variable {S : Scheme.{0}} {G G₀ : Over S} [GrpObj G] (j : G₀ ⟶ G)

abbrev RangeIsId : Prop := ∀ x : G.left, x ∈ Set.range j.left ↔
  x ∈ connectedComponentIn (G.hom ⁻¹' {G.hom x}) ((η[G]).left (G.hom x))

include j in
theorem unit_mem_fibre (s : S) : (η[G]).left s ∈ G.hom ⁻¹' {s} := by
  show G.hom ((η[G]).left s) = s
  rw [← Scheme.Hom.comp_apply, Over.w]
  rfl

theorem isConnected_fibre [IsOpenImmersion j.left] (hr : RangeIsId j) (s : S) :
    _root_.IsConnected (G₀.hom ⁻¹' {s}) := by
  have hw : ∀ x, G.hom (j.left x) = G₀.hom x := fun x => by
    rw [← Scheme.Hom.comp_apply, Over.w]
  have himg : j.left '' (G₀.hom ⁻¹' {s}) = connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have := (hr (j.left x)).1 ⟨x, rfl⟩
      rwa [hw, show G₀.hom x = s from hx] at this
    · intro hy
      have hys : G.hom y = s := connectedComponentIn_subset (G.hom ⁻¹' {s}) _ hy
      obtain ⟨x, rfl⟩ := (hr y).2 (by rwa [hys])
      exact ⟨x, by rw [Set.mem_preimage, ← hw, hys]; rfl, rfl⟩
  have hc : _root_.IsConnected (connectedComponentIn (G.hom ⁻¹' {s}) ((η[G]).left s)) :=
    isConnected_connectedComponentIn_iff.mpr (unit_mem_fibre j s)
  rw [← himg] at hc
  exact ⟨hc.nonempty.of_image, j.left.isOpenEmbedding.isInducing.isPreconnected_image.1 hc.isPreconnected⟩

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId

namespace GlobalTheory.SemiStableId

end GlobalTheory.SemiStableId
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.UnionLocal

theorem awayMap_notMem {R : Type} [CommRing R] (g : R) (w : Sp (Localization.Away g)) : g ∉ (awayMap g w).asIdeal := by
  intro h
  have : algebraMap R (Localization.Away g) g ∈ w.asIdeal := h
  exact w.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ this (IsLocalization.Away.algebraMap_isUnit g))

theorem mul_left_comp {S T T' : Scheme.{0}} {H : Over S} [GrpObj H] {t : T ⟶ S} {t' : T' ⟶ S} (k : T' ⟶ T)
    (a b : Over.mk t ⟶ H) (a₁ b₁ : Over.mk t' ⟶ H) (ha : a₁.left = k ≫ a.left) (hb : b₁.left = k ≫ b.left) :
    (a₁ * b₁).left = k ≫ (a * b).left := by
  have ht : k ≫ t = t' := by
    have e1 : a.left ≫ H.hom = t := Over.w a
    have e2 : a₁.left ≫ H.hom = t' := Over.w a₁
    rw [← e1, ← e2, ha]; exact (Category.assoc _ _ _).symm
  let κ : Over.mk t' ⟶ Over.mk t := Over.homMk k ht
  have e1 : a₁ = κ ≫ a := Over.OverMorphism.ext ha
  have e2 : b₁ = κ ≫ b := Over.OverMorphism.ext hb
  rw [e1, e2, ← MonObj.comp_mul]
  rfl

theorem mulAgree_pullback {S S' S₂ P : Scheme.{0}} {H : Over S} [GrpObj H] {H' : Over S'} [GrpObj H'] {A : Over S₂} [GrpObj A]
    {t : S' ⟶ S} {π : H'.left ⟶ H.left} (hπ : IsGrpPullback H' H t π) {h : H.left ⟶ P} {i : A.left ⟶ P}
    (hm : MulAgree H A h i) : MulAgree H' A (π ≫ h) i := by
  intro T t₁ t₂ a b a' b' ha hb
  have w : ∀ c : Over.mk t₁ ⟶ H', (c.left ≫ π) ≫ H.hom = t₁ ≫ t := fun c => by
    have e : c.left ≫ H'.hom = t₁ := Over.w c
    rw [Category.assoc, hπ.1.w, ← Category.assoc, e]
  let a₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (a.left ≫ π) (w a)
  let b₀ : Over.mk (t₁ ≫ t) ⟶ H := Over.homMk (b.left ≫ π) (w b)
  have e := hπ.2 (Over.mk t₁) a b a₀ b₀ rfl rfl
  have e2 := hm T (t₁ ≫ t) t₂ a₀ b₀ a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb)
  rw [← e2, ← Category.assoc]
  exact congrArg (· ≫ h) e.symm

theorem openIn_pullback {P S₀ S S' Y : Scheme.{0}} (p : P ⟶ S₀) (u : S ⟶ S₀) [Mono u] (q : Y ⟶ S) (h : Y ⟶ P)
    [IsOpenImmersion h] (w : h ≫ p = q ≫ u) (t : S' ⟶ S) :
    OpenIn (pullback.fst q t ≫ h) (pullback.snd q t) p (t ≫ u) := by
  have w' : (pullback.fst q t ≫ h) ≫ p = pullback.snd q t ≫ t ≫ u := by
    rw [Category.assoc, w, pullback.condition_assoc]
  refine ⟨w', ?_⟩
  have hsq : CommSq (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := ⟨by rw [pullback.lift_fst]⟩
  have hc : ∀ c : PullbackCone h (pullback.fst p (t ≫ u)), c.fst ≫ q = (c.snd ≫ pullback.snd p (t ≫ u)) ≫ t := fun c => by
    rw [← cancel_mono u, Category.assoc, ← w, ← Category.assoc, c.condition, Category.assoc, pullback.condition]
    simp only [Category.assoc]
  have hp : IsPullback (pullback.fst q t) (pullback.lift _ _ w') h (pullback.fst p (t ≫ u)) := by
    refine IsPullback.of_isLimit' hsq (PullbackCone.IsLimit.mk hsq.w (fun c => pullback.lift c.fst _ (hc c))
      (fun c => pullback.lift_fst _ _ _) (fun c => ?_) (fun c m hm1 hm2 => ?_))
    · apply pullback.hom_ext
      · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, c.condition]
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
    · apply pullback.hom_ext
      · rw [pullback.lift_fst, hm1]
      · rw [pullback.lift_snd, ← hm2, Category.assoc, pullback.lift_snd]
  exact MorphismProperty.of_isPullback hp ‹_›

theorem exists_point {P S₀ S : Scheme.{0}} (p : P ⟶ S₀) (s : S ⟶ S₀) (H₁ H₂ : Over S) [GrpObj H₁] [GrpObj H₂]
    (h₁ : H₁.left ⟶ P) (h₂ : H₂.left ⟶ P) (o₁ : OpenIn h₁ H₁.hom p s) (o₂ : OpenIn h₂ H₂.hom p s)
    (hs : Smooth H₁.hom) (hc : GeometricallyConnected H₁.hom) (hm : MulAgree H₁ H₂ h₁ h₂) (ho : OneAgree s s H₁ H₂ h₁ h₂)
    (y : H₁.left) : ∃ y' : H₂.left, h₂ y' = h₁ y ∧ H₂.hom y' = H₁.hom y := by
  obtain ⟨w₁, o₁⟩ := o₁
  obtain ⟨w₂, o₂⟩ := o₂
  have key : ∀ {T : Scheme.{0}} {t₁ t₂ : T ⟶ S} (a : Over.mk t₁ ⟶ H₁) (a' : Over.mk t₂ ⟶ H₂),
      a.left ≫ pullback.lift h₁ H₁.hom w₁ = a'.left ≫ pullback.lift h₂ H₂.hom w₂ ↔ a.left ≫ h₁ = a'.left ≫ h₂ ∧ t₁ = t₂ := by
    intro T t₁ t₂ a a'
    have e1 : a.left ≫ H₁.hom = t₁ := Over.w a
    have e2 : a'.left ≫ H₂.hom = t₂ := Over.w a'
    constructor
    · intro h
      have f1 := congrArg (· ≫ pullback.fst p s) h
      have f2 := congrArg (· ≫ pullback.snd p s) h
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd] at f1 f2
      exact ⟨f1, e1.symm.trans (f2.trans e2)⟩
    · rintro ⟨h, h'⟩
      apply pullback.hom_ext
      · simpa only [Category.assoc, pullback.lift_fst] using h
      · simp only [Category.assoc, pullback.lift_snd]
        exact e1.trans (h'.trans e2.symm)
  obtain ⟨y', hy'⟩ := GlobalTheory.OpenSubgrp.range_subset S (pullback p s) H₁ H₂ (pullback.lift h₁ H₁.hom w₁) (pullback.lift h₂ H₂.hom w₂)
    (pullback.snd p s) (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) o₁ o₂ hs hc
    (fun T t₁ t₂ a b a' b' ha hb => (key _ _).2 ⟨hm T t₁ t₂ a b a' b' ((key _ _).1 ha).1 ((key _ _).1 hb).1, ((key _ _).1 ha).2⟩)
    (fun T t₁ t₂ e => by
      have e' : t₁ = t₂ := by simpa using e
      exact (key _ _).2 ⟨ho T t₁ t₂ (by rw [e']), e'⟩) ⟨y, rfl⟩
  refine ⟨y', ?_, ?_⟩
  · have := congrArg (pullback.fst p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at this
  · have := congrArg (pullback.snd p s) hy'
    rwa [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_snd, pullback.lift_snd] at this

theorem exists_connected (σ : Setup) (E : Emb σ) (g : σ.R) (H' : Over (Sp (Localization.Away g))) [GrpObj H']
    (h' : H'.left ⟶ E.P) (hl : E.LocGrp g H' h') :
    ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ GeometricallyConnected H.hom := by
  obtain ⟨hsm, hqc, hop, hp, hm⟩ := hl
  obtain ⟨H, _, j, hj, hjo, hr⟩ := GlobalTheory.identityComponentOpen _ H' hsm
  have hw : j.left ≫ H'.hom = H.hom := Over.w j
  have hsm₀ : Smooth H.hom := by rw [← hw]; infer_instance
  have : IsNoetherianRing (Localization.Away g) := IsLocalization.isNoetherianRing (Submonoid.powers g) _ inferInstance
  have : IsLocallyNoetherian H'.left := LocallyOfFiniteType.isLocallyNoetherian H'.hom
  have : CompactSpace H'.left := QuasiCompact.compactSpace_of_compactSpace H'.hom
  have : IsNoetherian H'.left := {}
  have hqc₀ : QuasiCompact H.hom := by rw [← hw]; infer_instance
  refine ⟨H, inferInstance, j.left ≫ h', ⟨hsm₀, hqc₀, inferInstance, by rw [Category.assoc, hp, ← Category.assoc, hw], ?_⟩,
    GlobalTheory.SS.NeutralPart.geometricallyConnected_of_section H.hom (η[H]).left (Over.w _)
      (GlobalTheory.SemiStableId.isConnected_fibre j hr)⟩
  intro T t₁ t₂ a b a' b' ha hb
  rw [← hm T t₁ t₂ (a ≫ j) (b ≫ j) a' b' ((Category.assoc _ _ _).trans ha) ((Category.assoc _ _ _).trans hb),
    ← MonObj.mul_comp, Over.comp_left, Category.assoc]

theorem lift_open (σ : Setup) (x : Sp σ.R) {T : Scheme.{0}} (c : T ⟶ (σ.C x).G.left) (d : T ⟶ Sp (Localization.Away σ.f))
    (e : c ≫ (σ.C x).G.hom ≫ spMap (σ.ρ x) = d ≫ awayMap σ.f) : ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c := by
  refine ⟨IsOpenImmersion.lift (σ.V x).ι c ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨τ, rfl⟩
  rw [Scheme.Opens.range_ι]
  refine (σ.hV x _).2 ?_
  have h1 := awayMap_notMem σ.f (d τ)
  rw [← Scheme.Hom.comp_apply, ← e] at h1
  exact h1

theorem chart_mul_generic (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (s : T ⟶ Sp (FractionRing (σ.C x).R))
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  obtain ⟨l, hl⟩ := lift_open σ x (pullback.fst (σ.C x).G.hom (jK (σ.C x).R)) (pullback.snd _ _ ≫ (σ.C x).y) (by
    rw [pullback.condition_assoc, Category.assoc, (σ.C x).hy, σ.hρ])
  have hα : (σ.C x).α ≫ E.ιA = pullback.fst (σ.C x).G.hom (jK (σ.C x).R) ≫ E.emb x := by
    have := σ.compat x _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rw [Category.id_comp] at this
    rw [this, Category.assoc, E.onV, ← Category.assoc, hl]
  let P : (Over.mk (s ≫ jK (σ.C x).R) ⟶ (σ.C x).G) → (Over.mk s ⟶ (Over.pullback (jK (σ.C x).R)).obj (σ.C x).G) :=
    fun c => Over.homMk (pullback.lift c.left s (Over.w c)) (pullback.lift_snd _ _ _)
  have hP : ∀ c, c.left = (P c).left ≫ pullback.fst (σ.C x).G.hom (jK (σ.C x).R) := fun c => (pullback.lift_fst _ _ _).symm
  have hA : ∀ c (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA → c'.left = (P c).left ≫ (σ.C x).α := by
    intro c c' h
    rw [← cancel_mono E.ιA, ← h, hP c]
    exact (Category.assoc _ _ _).trans ((congrArg ((P c).left ≫ ·) hα.symm).trans (Category.assoc _ _ _).symm)
  have ht : t₂ = s ≫ (σ.C x).y := by
    have e1 : a'.left ≫ σ.A.hom = t₂ := Over.w a'
    have e2 : (P a).left ≫ ((Over.pullback (jK (σ.C x).R)).obj (σ.C x).G).hom = s := Over.w (P a)
    have e3 := (σ.C x).gen.1.w
    rw [← e1, hA a a' ha]
    exact (Category.assoc _ _ _).trans ((congrArg ((P a).left ≫ ·) e3).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (σ.C x).y) e2)))
  subst ht
  have m1 := (σ.C x).gen.2 (Over.mk s) (P a) (P b) a' b' (hA a a' ha) (hA b b' hb)
  have m2 := (isGrpPullback_pullback (σ.C x).G (jK (σ.C x).R)).2 (Over.mk s) (P a) (P b) a b (hP a) (hP b)
  exact (congrArg (· ≫ E.emb x) m2).trans ((Category.assoc _ _ _).trans ((congrArg ((P a * P b).left ≫ ·) hα.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ E.ιA) m1.symm))))

theorem chart_mul_flat (σ : Setup) (E : Emb σ) (x : Sp σ.R) {T : Scheme.{0}} (t₁ : T ⟶ Sp (σ.C x).R) [Flat t₁]
    (t₂ : T ⟶ Sp (Localization.Away σ.f)) (a b : Over.mk t₁ ⟶ (σ.C x).G) (a' b' : Over.mk t₂ ⟶ σ.A)
    (ha : a.left ≫ E.emb x = a'.left ≫ E.ιA) (hb : b.left ≫ E.emb x = b'.left ≫ E.ιA) :
    (a * b).left ≫ E.emb x = (a' * b').left ≫ E.ιA := by
  have := E.sep
  obtain ⟨w, -⟩ := E.openIn x
  have p1 : ∀ c : Over.mk t₁ ⟶ (σ.C x).G, (c.left ≫ E.emb x) ≫ E.p = t₁ ≫ spMap (σ.ρ x) := fun c => by
    have e : c.left ≫ (σ.C x).G.hom = t₁ := Over.w c
    rw [Category.assoc, w, ← Category.assoc, e]
  have p2 : ∀ c : Over.mk t₂ ⟶ σ.A, (c.left ≫ E.ιA) ≫ E.p = t₂ ≫ awayMap σ.f := fun c => by
    have e : c.left ≫ σ.A.hom = t₂ := Over.w c
    rw [Category.assoc, E.cartA.w, ← Category.assoc, e]
  have : IsSchemeTheoreticallyDominant (jK (σ.C x).R) :=
    schDom_spec_map _ (IsFractionRing.injective (σ.C x).R (FractionRing (σ.C x).R))
  have : IsSchemeTheoreticallyDominant (pullback.fst t₁ (jK (σ.C x).R)) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback t₁ (jK (σ.C x).R)).flip
  refine ext_of_schDom E.p (by rw [p1, p2, ← p1 a, ← p2 a', ha]) (pullback.fst t₁ (jK (σ.C x).R)) ?_
  let k := pullback.fst t₁ (jK (σ.C x).R)
  let Q : (Over.mk t₁ ⟶ (σ.C x).G) → (Over.mk (pullback.snd t₁ (jK (σ.C x).R) ≫ jK (σ.C x).R) ⟶ (σ.C x).G) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) (Over.w c)).trans pullback.condition))
  let Q' : (Over.mk t₂ ⟶ σ.A) → (Over.mk (k ≫ t₂) ⟶ σ.A) := fun c =>
    Over.homMk (k ≫ c.left) ((Category.assoc _ _ _).trans (congrArg (k ≫ ·) (Over.w c)))
  have h := chart_mul_generic σ E x _ _ (Q a) (Q b) (Q' a') (Q' b')
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) ha).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (k ≫ ·) hb).trans (Category.assoc _ _ _).symm))
  rw [mul_left_comp k a b (Q a) (Q b) rfl rfl, mul_left_comp k a' b' (Q' a') (Q' b') rfl rfl] at h
  exact (Category.assoc _ _ _).symm.trans (h.trans (Category.assoc _ _ _))

theorem chart_mulAgree (σ : Setup) (E : Emb σ) (x : Sp σ.R) : MulAgree (σ.C x).G σ.A (E.emb x) E.ιA := by
  intro T t₁ t₂ a b a' b' ha hb
  have : IsOpenImmersion E.ιA := MorphismProperty.of_isPullback E.cartA.flip inferInstance
  have := (σ.C x).semi.smooth
  obtain ⟨w, -⟩ := E.openIn x
  have hl : ∀ (c : Over.mk t₁ ⟶ (σ.C x).G) (c' : Over.mk t₂ ⟶ σ.A), c.left ≫ E.emb x = c'.left ≫ E.ιA →
      ∃ l : T ⟶ (σ.V x).toScheme, l ≫ (σ.V x).ι = c.left ∧ l ≫ σ.φ x = c'.left := by
    intro c c' h
    obtain ⟨l, hl⟩ := lift_open σ x c.left (c'.left ≫ σ.A.hom) (by
      rw [← w, ← Category.assoc, h, Category.assoc, E.cartA.w, Category.assoc])
    refine ⟨l, hl, ?_⟩
    rw [← cancel_mono E.ιA, Category.assoc, E.onV, ← Category.assoc, hl]
    exact h
  obtain ⟨la, ha1, ha2⟩ := hl a a' ha
  obtain ⟨lb, hb1, hb2⟩ := hl b b' hb
  let q : (σ.V x).toScheme ⟶ Sp (σ.C x).R := (σ.V x).ι ≫ (σ.C x).G.hom
  have hq : la ≫ q = lb ≫ q := by
    have e1 : a.left ≫ (σ.C x).G.hom = t₁ := Over.w a
    have e2 : b.left ≫ (σ.C x).G.hom = t₁ := Over.w b
    simp only [q, ← Category.assoc, ha1, hb1]
    exact e1.trans e2.symm
  have hu : pullback.snd q q ≫ σ.φ x ≫ σ.A.hom = pullback.fst q q ≫ σ.φ x ≫ σ.A.hom := by
    rw [← cancel_mono (awayMap σ.f)]
    simp only [Category.assoc]
    rw [(σ.cart x).w]
    exact (pullback.condition_assoc (f := q) (g := q) _).symm
  let a₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.fst q q ≫ (σ.V x).ι) (Category.assoc _ _ _)
  let b₀ : Over.mk (pullback.fst q q ≫ q) ⟶ (σ.C x).G := Over.homMk (pullback.snd q q ≫ (σ.V x).ι)
    ((Category.assoc _ _ _).trans pullback.condition.symm)
  let a₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.fst q q ≫ σ.φ x) (Category.assoc _ _ _)
  let b₁ : Over.mk (pullback.fst q q ≫ σ.φ x ≫ σ.A.hom) ⟶ σ.A := Over.homMk (pullback.snd q q ≫ σ.φ x)
    ((Category.assoc _ _ _).trans hu)
  have h := chart_mul_flat σ E x (pullback.fst q q ≫ q) _ a₀ b₀ a₁ b₁
    ((Category.assoc _ _ _).trans ((congrArg (pullback.fst q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
    ((Category.assoc _ _ _).trans ((congrArg (pullback.snd q q ≫ ·) (E.onV x).symm).trans (Category.assoc _ _ _).symm))
  let k := pullback.lift la lb hq
  have k1 : k ≫ pullback.fst q q = la := pullback.lift_fst _ _ _
  have k2 : k ≫ pullback.snd q q = lb := pullback.lift_snd _ _ _
  rw [mul_left_comp k a₀ b₀ a b (ha1.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb1.symm.trans (by rw [← k2]; exact Category.assoc _ _ _)),
    mul_left_comp k a₁ b₁ a' b' (ha2.symm.trans (by rw [← k1]; exact Category.assoc _ _ _))
      (hb2.symm.trans (by rw [← k2]; exact Category.assoc _ _ _))]
  exact (Category.assoc _ _ _).trans ((congrArg (k ≫ ·) h).trans (Category.assoc _ _ _).symm)

theorem mem_range_iff (σ : Setup) (E : Emb σ) (g : σ.R) (H : Over (Sp (Localization.Away g))) [GrpObj H] (h : H.left ⟶ E.P)
    (hl : E.LocGrp g H h) (hc : GeometricallyConnected H.hom) (x : Sp σ.R) (hx : g ∉ x.asIdeal) (z : E.P) (hz : E.p z = x) :
    z ∈ Set.range h ↔ ∃ y : (σ.C x).G.left, (σ.C x).G.hom y = closedPoint _ ∧ E.emb x y = z := by
  obtain ⟨hsm, -, hop, hp, hm⟩ := hl
  have hcen : spMap (σ.ρ x) (closedPoint (σ.C x).R) = x := by rw [← σ.hρ]; exact (σ.C x).centre
  have hu : IsUnit (σ.ρ x g) := by
    by_contra hn
    apply hx
    have : g ∈ (spMap (σ.ρ x) (closedPoint (σ.C x).R)).asIdeal := hn
    rwa [hcen] at this
  let t : Sp (σ.C x).R ⟶ Sp (Localization.Away g) := spMap (IsLocalization.Away.lift g hu)
  have ht : t ≫ awayMap g = spMap (σ.ρ x) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.Away.lift_comp]
  have o₂ : OpenIn (pullback.fst H.hom t ≫ h) ((Over.pullback t).obj H).hom E.p (spMap (σ.ρ x)) :=
    ht ▸ openIn_pullback E.p (awayMap g) H.hom h hp t
  have s₂ : Smooth ((Over.pullback t).obj H).hom := inferInstanceAs (Smooth (pullback.snd H.hom t))
  have c₂ : GeometricallyConnected ((Over.pullback t).obj H).hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom t))
  have s₁ := (σ.C x).semi.smooth
  have fl : Flat (spMap (σ.ρ x)) := Flat.SpecMap_iff.2 (σ.flat x)
  have m₁ := chart_mulAgree σ E x
  have m₂ := mulAgree_pullback (isGrpPullback_pullback H t) hm
  constructor
  · rintro ⟨v, rfl⟩
    have e : H.hom v = t (closedPoint (σ.C x).R) := by
      apply (awayMap g).isOpenEmbedding.injective
      have e1 : (H.hom ≫ awayMap g) v = x := by rw [← hp]; exact hz
      have e2 : (t ≫ awayMap g) (closedPoint (σ.C x).R) = x := by rw [ht]; exact hcen
      exact e1.trans e2.symm
    obtain ⟨v₂, hv1, hv2⟩ := Scheme.Pullback.exists_preimage_pullback (f := H.hom) (g := t) v _ e
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ ((Over.pullback t).obj H) (σ.C x).G _ _ fl fl inferInstance inferInstance
      o₂ (E.openIn x) m₂ m₁
    obtain ⟨y, hy1, hy2⟩ := exists_point E.p _ ((Over.pullback t).obj H) (σ.C x).G _ _ o₂ (E.openIn x) s₂ c₂ ma oa v₂
    exact ⟨y, hy2.trans hv2, hy1.trans (congrArg h hv1)⟩
  · rintro ⟨y, -, rfl⟩
    obtain ⟨ma, oa⟩ := GlobalTheory.T.grpLaw_and_unit_agree_of_openIn_descentModel σ E _ _ _ _ (σ.C x).G ((Over.pullback t).obj H) _ _ fl fl inferInstance inferInstance
      (E.openIn x) o₂ m₁ m₂
    obtain ⟨v, hv, -⟩ := exists_point E.p _ (σ.C x).G ((Over.pullback t).obj H) _ _ (E.openIn x) o₂ s₁
      (σ.C x).semi.geomConnected ma oa y
    exact ⟨pullback.fst H.hom t v, hv⟩

theorem exists_locGrp_range_eq : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  intro σ E hC x
  obtain ⟨g, hg, H', _, h', hl', -⟩ := GlobalTheory.T.exists_local_smooth_group_over_nbhd σ E hC x
  obtain ⟨H, _, h, hl, hgc⟩ := exists_connected σ E g H' h' hl'
  refine ⟨g, hg, H, inferInstance, h, hl, ?_⟩
  ext z
  constructor
  · rintro ⟨v, rfl⟩
    have hpz : g ∉ (E.p (h v)).asIdeal := by
      rw [← Scheme.Hom.comp_apply, hl.2.2.2.1, Scheme.Hom.comp_apply]
      exact awayMap_notMem g _
    obtain ⟨y, hy, hyz⟩ := (mem_range_iff σ E g H h hl hgc _ hpz _ rfl).1 ⟨v, rfl⟩
    exact ⟨⟨_, y, hy, hyz⟩, hpz⟩
  · rintro ⟨⟨x₀, y, hy, rfl⟩, hz⟩
    have hx₀ : E.p (E.emb x₀ y) = x₀ := by
      obtain ⟨w, -⟩ := E.openIn x₀
      rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply, hy, ← σ.hρ x₀]
      exact (σ.C x₀).centre
    have hz' : g ∉ x₀.asIdeal := by rw [← hx₀]; exact hz
    exact (mem_range_iff σ E g H _ hl hgc x₀ hz' _ hx₀).2 ⟨y, hy, rfl⟩

end GlobalTheory.Desc.UnionLocal
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localGroup_range_union_closedFibres : ∀ (σ : Setup) (E : Emb σ), σ.Common → ∀ x : Sp σ.R, ∃ g : σ.R, g ∉ x.asIdeal ∧ ∃ (H : Over (Sp (Localization.Away g))) (_ : GrpObj H) (h : H.left ⟶ E.P), E.LocGrp g H h ∧ Set.range h = E.U ∩ E.p ⁻¹' {z : Sp σ.R | g ∉ z.asIdeal} := by
  atlas_forward_decl GlobalTheory.Desc.UnionLocal.exists_locGrp_range_eq
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem Setup.hasExt (σ : Setup) : HasExt (awayMap σ.f) σ.A := by
  have hc : σ.Common := GlobalTheory.T.abelianSchemeDescentData_charts_common σ
  obtain ⟨E⟩ := GlobalTheory.T.nonempty_descentSeparatedEmbedding σ hc
  exact GlobalTheory.T.extendsToSemiAbelian_of_local_groups σ E hc (GlobalTheory.T.exists_localGroup_range_union_closedFibres σ E hc)

theorem hasExt_of_setup : ∀ σ : Setup, HasExt (awayMap σ.f) σ.A := Setup.hasExt

end GlobalTheory.Desc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.GenericFibreChart

theorem isPullback_of_fac_mono {C : Type*} [Category C] {P V G S T : C} {p : P ⟶ G} {q : P ⟶ T}
    {h : G ⟶ S} {j : T ⟶ S} (H : IsPullback p q h j) (i : V ⟶ G) [Mono i] (l : P ⟶ V)
    (hl : l ≫ i = p) : IsPullback l q (i ≫ h) j := by
  have w : l ≫ i ≫ h = q ≫ j := by rw [← Category.assoc, hl, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift (s.fst ≫ i) s.snd (by rw [Category.assoc]; exact s.condition)) ?_ ?_ ?_⟩⟩
  · intro s
    rw [← cancel_mono i, Category.assoc, hl, H.lift_fst]
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, ← h1, Category.assoc, hl]
    · rw [H.lift_snd, h2]

theorem isPullback_of_comp_mono {C : Type*} [Category C] {P X Y W Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {a : X ⟶ W} {g : Y ⟶ W} (m : W ⟶ Z) [Mono m] (H : IsPullback p q (a ≫ m) (g ≫ m)) :
    IsPullback p q a g := by
  have w : p ≫ a = q ≫ g := by
    rw [← cancel_mono m, Category.assoc, Category.assoc, H.w]
  refine ⟨⟨w⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => H.lift s.fst s.snd (by
      rw [← Category.assoc, ← Category.assoc, s.condition])) ?_ ?_ ?_⟩⟩
  · intro s
    exact H.lift_fst _ _ _
  · intro s
    exact H.lift_snd _ _ _
  · intro s m h1 h2
    apply H.hom_ext
    · rw [H.lift_fst, h1]
    · rw [H.lift_snd, h2]

theorem exists_isPullback_generic :
    ∀ (R₀ : Type) [CommRing R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) (R : Type)
      [CommRing R] [IsDomain R] (ρ : R₀ →+* R), ρ f ≠ 0 →
      ∀ (G : Over (Sp R)) (V : G.left.Opens) (φ : V.toScheme ⟶ A.left),
      (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) →
      IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ GlobalTheory.Desc.awayMap f) (spMap ρ) →
      ∃ (g : Sp (FractionRing R) ⟶ Sp (Localization.Away f))
        (l : pullback G.hom (jK R) ⟶ V.toScheme),
        l ≫ V.ι = pullback.fst G.hom (jK R) ∧
          IsPullback (l ≫ φ) (pullback.snd G.hom (jK R)) A.hom g := by
  intro R₀ _ f A R _ _ ρ hf G V φ hV hP
  have hu : IsUnit (((algebraMap R (FractionRing R)).comp ρ) f) := by
    rw [isUnit_iff_ne_zero, RingHom.comp_apply]
    exact fun h => hf ((IsFractionRing.injective R (FractionRing R)) (by rw [h, map_zero]))
  let ψ : Localization.Away f →+* FractionRing R := IsLocalization.Away.lift f hu
  have hψ : ψ.comp (algebraMap R₀ (Localization.Away f)) =
      (algebraMap R (FractionRing R)).comp ρ := IsLocalization.Away.lift_comp f hu
  have hg : spMap ψ ≫ GlobalTheory.Desc.awayMap f = jK R ≫ spMap ρ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hψ]
  have hr : Set.range (pullback.fst G.hom (jK R)) ⊆ Set.range V.ι := by
    rintro _ ⟨x, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine (hV _).2 ?_
    have hx : G.hom (pullback.fst G.hom (jK R) x) = jK R (pullback.snd G.hom (jK R) x) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    rw [hx]
    intro hmem
    have hmem' : algebraMap R (FractionRing R) (ρ f) ∈
        (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).asIdeal := hmem
    exact (pullback.snd G.hom (jK R) x : PrimeSpectrum (FractionRing R)).isPrime.ne_top
      (Ideal.eq_top_of_isUnit_mem _ hmem' hu)
  haveI : IsOpenImmersion (GlobalTheory.Desc.awayMap f) := IsOpenImmersion.of_isLocalization f
  refine ⟨spMap ψ, IsOpenImmersion.lift V.ι _ hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
  have h1 := isPullback_of_fac_mono (IsPullback.of_hasPullback G.hom (jK R)) V.ι
    (IsOpenImmersion.lift V.ι _ hr) (IsOpenImmersion.lift_fac _ _ _)
  have h2 := h1.paste_horiz hP
  refine isPullback_of_comp_mono (GlobalTheory.Desc.awayMap f) ?_
  rw [hg]
  exact h2

end GlobalTheory.GenericFibreChart
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.PullOpen

open GlobalTheory.Cartier.DomPull

theorem isDominant_of_gen {X V : Scheme.{0}} [IsIntegral X] (φ : V ⟶ X) (v : V)
    (hv : φ v = genericPoint X) : IsDominant φ := by
  refine ⟨?_⟩
  have hd : Dense ({genericPoint X} : Set X) := by
    rw [dense_iff_closure_eq]; exact (genericPoint_spec X).def
  exact hd.mono (Set.singleton_subset_iff.2 ⟨v, hv⟩)

theorem gp_apply {X : Scheme.{0}} [IsIntegral X] (q : Sp X.functionField) : gp X q = genericPoint X := by
  have h1 : gp X q ⤳ genericPoint X := by
    have : gp X q ∈ Set.range (X.fromSpecStalk (genericPoint X)) := ⟨q, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  exact (h1.antisymm (genericPoint_specializes _)).eq

theorem ffm_comp {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {V : Y.Opens} [IsIntegral V.toScheme]
    [IsDominant V.ι] {φ : V.toScheme ⟶ X} [IsDominant φ] {θ : X.functionField →+* Y.functionField}
    (h : PFF V.ι φ θ) : (GlobalTheory.functionFieldMap V.ι).comp θ = GlobalTheory.functionFieldMap φ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have e1 : Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap V.ι)) ≫ l = genericFieldPoint V.toScheme := by
    rw [← cancel_mono V.ι, Category.assoc, h₁]
    exact GlobalTheory.specMap_functionFieldMap V.ι
  have e2 : Spec.map (CommRingCat.ofHom ((GlobalTheory.functionFieldMap V.ι).comp θ)) ≫ gp X =
      Spec.map (CommRingCat.ofHom (GlobalTheory.functionFieldMap φ)) ≫ gp X := by
    refine Eq.trans ?_ (GlobalTheory.specMap_functionFieldMap φ).symm
    rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
    erw [← h₂]
    rw [← Category.assoc, e1]
  haveI : Mono (gp X) := inferInstanceAs (Mono (X.fromSpecStalk (genericPoint X)))
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 e2))

theorem lbIso_pull : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (V : Y.Opens) (φ : V.toScheme ⟶ X)
    (θ : X.functionField →+* Y.functionField) (D : CartierDiv X) (D₁ : CartierDiv Y),
    PFF V.ι φ θ → PPull V.ι φ θ D D₁ → LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := by
  intro X Y _ _ V φ θ D D₁ hF hP
  obtain ⟨l, h₁, h₂⟩ := hF
  obtain ⟨q⟩ : Nonempty (Sp Y.functionField) := inferInstance
  haveI : Nonempty V := ⟨l q⟩
  haveI : IsIntegral V.toScheme := inferInstance
  haveI : IsDominant V.ι := isDominant_of_gen V.ι (l q) (by
    rw [← Scheme.Hom.comp_apply, h₁, gp_apply])
  haveI : IsDominant φ := isDominant_of_gen φ (l q) (by
    rw [← Scheme.Hom.comp_apply, h₂, Scheme.Hom.comp_apply, gp_apply])
  have key := ffm_comp (V := V) (φ := φ) ⟨l, h₁, h₂⟩
  have hE : pullback V.ι D₁ = pullback φ D := CartierDiv.ext_of_isEqn fun v => by
    obtain ⟨g, hg⟩ := D.exists_isEqn (φ v)
    refine ⟨unitsMap φ g, ?_, isEqn_pullback φ D hg⟩
    have := isEqn_pullback V.ι D₁ (hP v g hg)
    convert this using 1
    ext
    simp only [unitsMap, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe]
    exact (congrArg (fun f : X.functionField →+* V.toScheme.functionField => f g) key).symm
  exact (presents_pullback V.ι D₁).lbIso (hE ▸ presents_pullback φ D)

end GlobalTheory.Desc.PullOpen
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGenericExt

theorem symm_of_generic : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  intro R _ _ _ _ _ G _ hG L hL h
  have e := GlobalTheory.SymBaseChange.inv_left_fst _ _ G (jK R)
  have h1 := GenSpread.lbIso_pull_pull hL (a := pullback.fst G.hom (jK R))
    (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : G ⟶ G).left) (pullback.fst G.hom (jK R)) e
  refine GlobalTheory.GenericDec.lbIso_of_generic G hG (pull_isLB hL _) hL ?_
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h2)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h1 h)

end GlobalTheory.SymGenericExt
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → ∀ L : LB G.left, L.IsLB → LBIso ((L.pull (pullback.fst G.hom (jK R))).pull (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left) (L.pull (pullback.fst G.hom (jK R))) → LBIso (L.pull (GrpObj.inv : G ⟶ G).left) L := by
  atlas_forward_decl GlobalTheory.SymGenericExt.symm_of_generic
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGrpPull

theorem inv_left_comp {S T : Scheme.{0}} (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S)
    (α : B.left ⟶ A.left) (h : IsGrpPullback B A y α) :
    (GrpObj.inv : B ⟶ B).left ≫ α = α ≫ (GrpObj.inv : A ⟶ A).left := by
  have hw : α ≫ A.hom = B.hom ≫ y := h.1.w
  let f : (B ⟶ B) → (Over.mk (B.hom ≫ y) ⟶ A) := fun x =>
    Over.homMk (x.left ≫ α) (by
      change (x.left ≫ α) ≫ A.hom = B.hom ≫ y
      rw [Category.assoc, hw, ← Category.assoc, Over.w x])
  have hmul : ∀ x z : B ⟶ B, f (x * z) = f x * f z := fun x z =>
    Over.OverMorphism.ext (h.2 B x z (f x) (f z) rfl rfl).symm
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [← hmul, _root_.mul_one, _root_.mul_one]
    exact mul_left_cancel e
  have hinv : f (𝟙 B)⁻¹ = (f (𝟙 B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, _root_.inv_mul_cancel, h1]
  have e := congrArg CommaMorphism.left hinv
  have e' : ((𝟙 B ≫ GrpObj.inv : B ⟶ B)).left ≫ α = (f (𝟙 B) ≫ GrpObj.inv).left := e
  simpa [f] using e'

theorem symm_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  intro S T A _ B _ y α h L hL hs
  have e := inv_left_comp A B y α h
  have h1 := GenSpread.lbIso_pull_pull hL (a := α) (GrpObj.inv : B ⟶ B).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : A ⟶ A).left) α e
  have h3 := GenSpread.lbIso_pullback hs α
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymGrpPull
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  atlas_forward_decl GlobalTheory.SymGrpPull.symm_pull
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_pullback_of_isPullback : ∀ (S T S' : Scheme.{0}) (G : Over S) [GrpObj G] (t : T ⟶ S) (A : Over S') [GrpObj A] (a : pullback G.hom t ⟶ A.left) (g : T ⟶ S'), IsSemiAbelian G → IsAbelianScheme A → IsPullback a (pullback.snd G.hom t) A.hom g → IsAbelianScheme ((Over.pullback t).obj G) := by
  intro S T S' G _ t A _ a g hG hA sq
  exact
  { comm := by have := hG.comm; infer_instance
    smooth := by have := hG.smooth; change Smooth (pullback.snd G.hom t); infer_instance
    proper := by
      have := hA.proper; change IsProper (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    geomConnected := by
      have := hA.geomConnected; change GeometricallyConnected (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq inferInstance }

theorem ampleDiv_closure_on_chart : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ D : CartierDiv A.left, AmpleDiv D → LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (ρ : R₀ →+* R), ρ.Flat → ρ f ≠ 0 → ∀ (G : Over (Sp R)) [GrpObj G] [IsIntegral G.left], IsSemiAbelian G → ∀ (V : G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* G.left.functionField) (D₁ : CartierDiv G.left), (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) → IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ awayMap f) (spMap ρ) → ∀ (y : Sp (FractionRing R) ⟶ Sp (Localization.Away f)) (α : pullback G.hom (jK R) ⟶ A.left), IsGrpPullback ((Over.pullback (jK R)).obj G) A y α → (∀ (T : Scheme.{0}) (t : T ⟶ pullback G.hom (jK R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ α = t' ≫ φ) → PFF V.ι φ θ → PPull V.ι φ θ D D₁ → AmpleDiv D₁ := by
  intro R₀ _ _ f A _ _ hA D hD hsym R _ _ _ _ hR ρ hflat hρf G _ _ hG V φ θ D₁ hV hsq y α hα hcomp hff hpp
  obtain ⟨g, l, hl, sq⟩ := GlobalTheory.GenericFibreChart.exists_isPullback_generic R₀ f A R ρ hρf G V φ hV hsq
  have hGK : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    isAbelianScheme_pullback_of_isPullback _ _ _ G (jK R) A (l ≫ φ) g hG hA sq
  haveI : IsProper ((Over.pullback (jK R)).obj G).hom := hGK.proper
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hAD : IsAmpleLB (toLB D) := (ampleDiv_iff_isAmpleLB A.left D).1 hD
  have h1 : IsAmpleLB ((toLB D).pull (l ≫ φ)) := hAD.pull_of_isPullback sq
  have h3 : LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := GlobalTheory.Desc.PullOpen.lbIso_pull _ _ V φ θ D D₁ hff hpp
  have hL₁ := isLB_toLB D₁
  have h4 : LBIso ((toLB D₁).pull (pullback.fst G.hom (jK R))) ((toLB D).pull (l ≫ φ)) := by
    rw [← hl]
    exact LBIso.trans (LB.isLB_pull hL₁ _) (LB.isLB_pull (LB.isLB_pull hL₁ _) _)
      (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL₁ V.ι l).symm
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull hL₁ _) _) (LB.isLB_pull (LB.isLB_pull (isLB_toLB D) _) _)
        (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.Mum.UExt.lbIso_pull h3 l)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (isLB_toLB D) φ l))
  have h5 : IsAmpleLB ((toLB D₁).pull (pullback.fst G.hom (jK R))) := h1.of_lbIso (LB.isLB_pull hL₁ _) h4
  have h6 := (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_pull hL₁ _)).2 h5
  have hlα : α = l ≫ φ := by
    have := hcomp _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rwa [Category.id_comp] at this
  have hs1 := GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback _ _ A ((Over.pullback (jK R)).obj G) y α hα (toLB D) (isLB_toLB D) hsym
  rw [hlα] at hs1
  have hK₁ := LB.isLB_pull hL₁ (pullback.fst G.hom (jK R))
  have hK := LB.isLB_pull (isLB_toLB D) (l ≫ φ)
  have hs2 : LBIso (((toLB D₁).pull (pullback.fst G.hom (jK R))).pull
      (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left)
      ((toLB D₁).pull (pullback.fst G.hom (jK R))) :=
    LBIso.trans (LB.isLB_pull hK₁ _) (LB.isLB_pull hK _) hK₁ (GlobalTheory.Mum.UExt.lbIso_pull h4 _)
      (LBIso.trans (LB.isLB_pull hK _) hK hK₁ hs1 h4.symm)
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hs3 := GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre R G hG (toLB D₁) hL₁ hs2
  have h7 := GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian R hR G hG hGK (toLB D₁) hL₁ h6 hs3
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact (ampleDiv_iff_isAmpleLB G.left D₁).2 h7

end GlobalTheory.Desc
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLB

theorem pull_inv_symm_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → LBIso ((LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]).pull (GrpObj.inv : G ⟶ G).left) (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]) := by
  intro S G _ L hL
  have h₁ := LB.isLB_linComb hL (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB h₁ _) h₁).1 ?_
  rw [GlobalTheory.CechPic.cls_pull h₁, GlobalTheory.CechPic.cls_linComb hL _ _ h₁]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add,
    ← GlobalTheory.CechPic.pull_comp]
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, Category.comp_id, add_comm]

end GlobalTheory.SymLB
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section

namespace GlobalTheory.SymDiv

theorem exists_ampleDiv_symm : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → ∃ D : CartierDiv A.left, AmpleDiv D ∧ LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) := by
  intro R _ A _ _ hA L hL hamp
  classical
  have hprop : IsProper A.hom := hA.proper
  set σ := (GrpObj.inv : A ⟶ A).left with hσ
  have hii : (GrpObj.inv : A ⟶ A) ≫ (GrpObj.inv : A ⟶ A) = 𝟙 A := by
    have h := IsIso.hom_inv_id (GrpObj.inv : A ⟶ A)
    rwa [GrpObj.inv_inv] at h
  have hii' : σ ≫ σ = 𝟙 A.left := by
    rw [hσ, ← Over.comp_left, hii, Over.id_left]
  have : IsIso σ := ⟨⟨σ, hii', hii'⟩⟩
  set L' := LB.LinComb L (K := Fin 2) ![𝟙 A.left, σ] ![1, 1] with hL'def
  have hL' : L'.IsLB := LB.isLB_linComb hL (K := Fin 2) ![𝟙 A.left, σ] ![1, 1]
  have hamL : IsAmpleLB L := (relAmple_iff_isAmpleLB_of_isAffine A hL).1 hamp
  have hamσ : IsAmpleLB (L.pull σ) := hamL.pull_of_isAffineHom σ
  have hamL' : IsAmpleLB L' := by
    refine hamL.tensor hamσ hL' ?_
    have hM := pull_isLB hL σ
    have hD1 := LB.isLB_div hL' hL
    have hD2 := LB.isLB_div hD1 hM
    refine (CechPic.cls_eq_zero_iff hD2).1 ?_
    rw [CechPic.cls_div hD1 hM, CechPic.cls_div hL' hL, CechPic.cls_linComb hL _ _ hL', CechPic.cls_pull hL σ hM]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_zsmul,
      CechPic.pull_id]
    abel
  have : CompactSpace A.left := hamL'.compactSpace
  obtain ⟨i₀, h₀⟩ := exists_chart hL' (genericPoint A.left)
  refine ⟨ofLB hL' i₀ h₀, ?_, ?_⟩
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    exact (ampleDiv_iff_isAmpleLB _ _).2 (hamL'.of_lbIso hT e.symm)
  · have e : LBIso L' (toLB (ofLB hL' i₀ h₀)) := (presents_ofLB hL' i₀ h₀).lbIso (presents_toLB _)
    have hT := isLB_toLB (ofLB hL' i₀ h₀)
    have hs : LBIso (L'.pull σ) L' := GlobalTheory.SymLB.pull_inv_symm_iso _ A L hL
    have e₁ : LBIso ((toLB (ofLB hL' i₀ h₀)).pull σ) (L'.pull σ) := GlobalTheory.FamRep.lbIso_pull e.symm σ
    exact LBIso.trans (pull_isLB hT σ) hL' hT (LBIso.trans (pull_isLB hT σ) (pull_isLB hL' σ) hL' e₁ hs) e

end GlobalTheory.SymDiv
end
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem ufm_stalk_of_smooth_regularLocal {E : Type} [CommRing E] [IsRegularLocalRing E] {Y : Scheme.{0}} [IsIntegral Y]
    (p : Y ⟶ Sp E) [Smooth p] (y : Y) : UniqueFactorizationMonoid (Y.presheaf.stalk y) := by
  have : IsRegularRing E := GlobalTheory.isRegularRing_of_isRegularLocalRing E
  have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth E p y
  exact uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
    isPrincipal_map_away_of_hasProjectiveDimensionLE _

theorem hasExt_awayMap_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  intro R _ _ _ _ f hf A _ hA L hL hamp hC
  have : IsDomain (Localization.Away f) :=
    IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)
  have : IsIntegral A.left := isIntegral_left_of_isAbelianScheme A
  obtain ⟨D, hD, hsym⟩ := GlobalTheory.SymDiv.exists_ampleDiv_symm _ A hA L hL hamp
  let C : ∀ x : Sp R, Chart (awayMap f) A x := fun x => (hC x).some
  have intC : ∀ x, IsIntegral (C x).G.left := fun x =>
    have := (C x).semi
    isIntegral_left_of_isSemiAbelian (C x).G
  choose ρ V φ θ hρ hflat hV hcart hcompat hθ using fun x => chart_part R f hf A hA x (C x)
  have hdiv : ∀ x, ∃ D₁ : CartierDiv (C x).G.left, PPull (V x).ι (φ x) (θ x) D D₁ ∧
      ∀ z, Vert (C x).G.hom (ρ x f) z → D₁.IsEqn z 1 := fun x => by
    have := (C x).semi.smooth
    have : IsLocallyNoetherian (C x).G.left := LocallyOfFiniteType.isLocallyNoetherian (C x).G.hom
    have hρf : Flat (spMap (ρ x)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hflat x
    have hφ : Flat (φ x) := MorphismProperty.of_isPullback (hcart x).flip hρf
    obtain ⟨D₁, h₁, h₂⟩ := exists_cartierDiv_closure (C x).G.left (V x).toScheme A.left
      (ufm_stalk_of_smooth_regularLocal (C x).G.hom) (V x).ι (φ x) (θ x) hφ (hθ x) D
    refine ⟨D₁, h₁, fun z hz => h₂ z ?_ hz.1⟩
    rw [Scheme.Opens.range_ι]
    exact fun hzV => (hV x z).1 hzV hz.2
  choose D₁ hpull hvert using hdiv
  have hamp₁ : ∀ x, AmpleDiv (D₁ x) := fun x => by
    have := (C x).charZero
    have hne : ρ x f ≠ 0 := fun h0 => by
      obtain ⟨l, -⟩ := hθ x
      let v : (V x).toScheme := l (closedPoint _)
      refine (hV x v.1).1 v.2 ?_
      rw [h0]
      exact zero_mem _
    exact ampleDiv_closure_on_chart R f A hA D hD hsym (C x).R (C x).complete (ρ x) (hflat x) hne (C x).G (C x).semi (V x) (φ x) (θ x)
      (D₁ x) (hV x) (hcart x) (C x).y (C x).α (C x).gen (hcompat x) (hθ x) (hpull x)
  exact hasExt_of_setup
    { R := R, f := f, hf := hf, A := A, ab := hA, D := D, amp := hD, C := C, ρ := ρ, hρ := hρ, flat := hflat, V := V,
      hV := hV, φ := φ, cart := hcart, compat := hcompat, θ := θ, hθ := hθ, D₁ := D₁, pull := hpull, noVert := hvert,
      amp₁ := hamp₁ }

end GlobalTheory.Desc
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extendsToSemiAbelian_away_of_charts : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] (f : R), f ≠ 0 → ∀ (A : Over (Sp (Localization.Away f))) [GrpObj A], IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → RelAmple A L → (∀ x : Sp R, Nonempty (Chart (awayMap f) A x)) → HasExt (awayMap f) A := by
  atlas_forward_decl GlobalTheory.Desc.hasExt_awayMap_of_charts
end
