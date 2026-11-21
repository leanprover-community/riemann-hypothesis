import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CardComapMulFinsumEqFinsumFibres
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPts
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NotInFibreOfIsUnit
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeStableUnderAction
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ProjectiveOverCoordsExist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrderStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsProductRefinement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsProperIntegralModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegularStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreProjectiveEmbedding
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointGenericFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointMemDenseOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointLiftAlongIso
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SmoothSchemeStalksDomains
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ClosedInProductProjective
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EveryComponentInSomeChart
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsGenerateFunctionField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordChartsMatchRegular
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingDeterminesComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularRingsEqualImagesEqual
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroCentreOfComplexStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SncPatchAtEachComponent
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCoordsOfGenericPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComponentGenericIsGenericPointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointFactorsOpen
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFiniteExtensionPrimesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAfterFiniteExtension
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericTrdegEqDimension
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import BuildAid.ForwardExisting
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericFibreOpenCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsNormalisation
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalIsoOfIntegrallyClosed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsSingleBlockSegre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtFractionNoetherianClosedStatement
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSncModelOfPatches
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFramesAwayPrime
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalizationStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.IsMultiHomogXpow
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionsNonzero

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ProjModel

open GlobalTheory.ProjSpace GlobalTheory.QCoh.Qcqs GlobalTheory.Cartier

attribute [local instance] MvPolynomial.gradedAlgebra

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem sec_ext (hg : IsCptGen ξ) (hall : ∀ q : X, genPt ξ ⤳ q) {W : X.Opens} {s t : Γ(X, W)}
    (h : ∀ hW : genPt ξ ∈ W, CoordBase.val (ξ := ξ) W hW s = CoordBase.val (ξ := ξ) W hW t) : s = t := by
  refine TopCat.Presheaf.section_ext X.sheaf W s t fun p hp => ?_
  have hW : genPt ξ ∈ W := (hall p).mem_open W.isOpen hp
  refine hg.inj ⟨p, hall p⟩ ?_
  exact (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp s).trans
    ((h hW).trans (CoordBase.genMap_germ_val W hW ⟨p, hall p⟩ hp t).symm)

theorem val_resG {U V : X.Opens} (h : V ≤ U) (hV : genPt ξ ∈ V) (s : Γ(X, U)) :
    CoordBase.val (ξ := ξ) V hV (resG X h s) = CoordBase.val (ξ := ξ) U (h hV) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply (homOfLE h).op.unop _ hV s)

theorem exists_charts {κ : Type} {x : κ → Ω} (hT : CoordTie ℤ ξ x) (hall : ∀ q : X, genPt ξ ⤳ q) :
    ∃ U : κ → X.Opens, (∀ c, IsAffineOpen (U c)) ∧ ∀ c q, q ∈ U c ↔ InChart ξ x c ⟨q, hall q⟩ := by
  have : ∀ c, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ q, q ∈ U ↔ InChart ξ x c ⟨q, hall q⟩ := by
    intro c
    by_cases hc : x c = 0
    · exact ⟨⊥, isAffineOpen_bot X, fun q => ⟨fun h => h.elim, fun h => (h.1 hc).elim⟩⟩
    · obtain ⟨U, hU, hm⟩ := hT.affine c hc
      exact ⟨U, hU, fun q => (hm q).trans ⟨fun ⟨_, h⟩ => h, fun h => ⟨hall q, h⟩⟩⟩
  choose U hU using this
  exact ⟨U, fun c => (hU c).1, fun c => (hU c).2⟩

theorem eval₂Hom_surjective {A J : Type} [CommRing A] (b : ℤ →+* A) (ρ : J → A) (v : A →+* Ω)
    (hv : Function.Injective v) (y : J → Ω) (hρ : ∀ j, v (ρ j) = y j)
    (hA : ∀ a, v a ∈ Algebra.adjoin ℤ (Set.range y)) :
    Function.Surjective (MvPolynomial.eval₂Hom b ρ) := by
  intro g
  have hg := hA g
  rw [Algebra.adjoin_range_eq_range_aeval] at hg
  obtain ⟨P, hP⟩ := hg
  refine ⟨P, hv ?_⟩
  have key : v.comp (MvPolynomial.eval₂Hom b ρ) =
      (MvPolynomial.aeval y : MvPolynomial J ℤ →ₐ[ℤ] Ω).toRingHom := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
    · simp
    · simp [hρ]
  exact (congrArg (fun φ : MvPolynomial J ℤ →+* Ω => φ P) key).trans hP

theorem isProjOver_of_coordTie {N : ℕ} {x : Fin (N + 1) → Ω} (hT : CoordTie ℤ ξ x)
    (hall : ∀ q : X, genPt ξ ⤳ q) (s : X ⟶ Sp ℤ) : IsProjOver s := by
  classical
  obtain ⟨U, hU, hm⟩ := exists_charts hT hall
  have hmem : ∀ c q, q ∈ U c ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩ := fun c q =>
    (hm c q).trans ⟨fun h => ⟨hall q, h⟩, fun ⟨_, h⟩ => h⟩
  have hgen : ∀ c, genPt ξ ∈ U c → x c ≠ 0 := fun c h => ((hm c _).1 h).1
  have hr : ∀ c j, ∃ b : Γ(X, U c), ∀ hW : genPt ξ ∈ U c,
      CoordBase.val (ξ := ξ) (U c) hW b = x j / x c := by
    intro c j
    by_cases hW : genPt ξ ∈ U c
    · obtain ⟨b, hb⟩ := (CoordBase.mem_adjoin_iff hT (hgen c hW) (hU c) (hmem c) hW (x j / x c)).1
        (Algebra.subset_adjoin ⟨j, rfl⟩)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨0, fun h => (hW h).elim⟩
  choose r hr using hr
  have H : IsCoordFamily U r :=
    { cover := by
        rw [eq_top_iff]
        intro q _
        obtain ⟨c, hc⟩ := hT.cover ⟨q, hall q⟩
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨c, (hm c q).2 hc⟩
      self := fun i => sec_ext hT.gen hall fun hW => by
        rw [hr, map_one, div_self (hgen i hW)]
      mul := fun i j k => sec_ext hT.gen hall fun hW => by
        have hi := hgen i hW.1
        have hj := hgen j hW.2
        rw [map_mul, val_resG, val_resG, val_resG, hr, hr, hr]
        field_simp
      basicOpen_le := fun i j p hp => by
        have hpi : p ∈ U i := X.basicOpen_le _ hp
        obtain ⟨u, hu⟩ : IsUnit (X.presheaf.germ (U i) p hpi (r i j)) :=
          (X.mem_basicOpen _ p hpi).1 hp
        have hW : genPt ξ ∈ U i := (hall p).mem_open (U i).isOpen hpi
        have hxi := hgen i hW
        have hv : genMap ξ ⟨p, hall p⟩ (u : X.presheaf.stalk p) = x j / x i := by
          rw [hu]
          exact (CoordBase.genMap_germ_val (U i) hW ⟨p, hall p⟩ hpi _).trans (hr _ _ _)
        have hinv : (x j / x i) * genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = 1 := by
          rw [← hv, ← map_mul, Units.mul_inv, map_one]
        have hxj : x j ≠ 0 := by
          intro h
          rw [h, zero_div, zero_mul] at hinv
          exact zero_ne_one hinv
        have hi := (hm i p).1 hpi
        refine (hm j p).2 ⟨hxj, fun c' => ?_⟩
        have e : x c' / x j = (x c' / x i) *
            genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) := by
          have e' : genMap ξ ⟨p, hall p⟩ ((u⁻¹ : (X.presheaf.stalk p)ˣ) : X.presheaf.stalk p) = x i / x j := by
            field_simp at hinv ⊢
            linear_combination hinv
          rw [e']
          field_simp
        rw [e]
        exact (regAt ξ _).mul_mem (hi.2 c') ⟨_, rfl⟩ }
  refine ⟨N, H.toHom s, ?_, H.toHom_str s⟩
  refine (isClosedImmersion_iff_pullRatio (H.toHom s) (H.toHom_preimage s)).2 fun i => ⟨hU i, ?_⟩
  have hρ : pullRatio (H.toHom s) (U i) i (H.toHom_preimage s i).ge = r i :=
    funext (H.pullRatio_toHom s i)
  rw [hρ]
  by_cases hW : genPt ξ ∈ U i
  · refine eval₂Hom_surjective _ _ (CoordBase.val (ξ := ξ) (U i) hW) ?_ (fun j => x j / x i) (hr i · hW) ?_
    · intro a a' e
      exact sec_ext hT.gen hall fun _ => e
    · intro a
      exact (CoordBase.mem_adjoin_iff hT (hgen i hW) (hU i) (hmem i) hW _).2 ⟨a, rfl⟩
  · exact fun g => ⟨0, sec_ext hT.gen hall fun h => (hW h).elim⟩

theorem isProjOver_pModel {κ : Type} [Finite κ] {x : κ → Ω} (M : PModel ℤ x) : IsProjOver M.s := by
  obtain ⟨N, x', h⟩ := coordTie_int_of_finite M.X Ω M.ξ ℤ κ x M.tie
  exact isProjOver_of_coordTie h M.all M.s

theorem isProjOver_of_map {O : Type} [CommRing O] {Z : Scheme.{0}} {s : Z ⟶ Sp ℤ} (h : IsProjOver s)
    (g : Z ⟶ Sp O) : IsProjOver g := by
  have hp := isProjOver_pullback_snd (Int.castRingHom O) h
  let σ : Z ⟶ pullback s (spMap (Int.castRingHom O)) :=
    pullback.lift (𝟙 Z) g (specZIsTerminal.hom_ext _ _)
  have hσ : IsClosedImmersion σ := by
    have : IsClosedImmersion (σ ≫ pullback.fst s (spMap (Int.castRingHom O))) := by
      rw [pullback.lift_fst]
      infer_instance
    exact .of_comp σ (pullback.fst s (spMap (Int.castRingHom O)))
  have := isProjOver_comp_of_isClosedImmersion σ hp
  rwa [pullback.lift_snd] at this

theorem isProjOver_comp_model : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω]
    (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) :=
  fun _ _ _ _ _ _ _ _ _ Y _ _ _ _ _ M f => isProjOver_of_map (isProjOver_pModel M) (f ≫ Y.s)

end GlobalTheory.CompanionTheory.Ar.ProjModel
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_model_over_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X), IsProjOver (f ≫ Y.s) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.ProjModel.isProjOver_comp_model
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus

theorem exists_dense_open : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  intro E _ _ _ H D l Xo c Y Ω _ κ _ x M f y₀ hξ
  set π := spMap (algebraMap (𝓞 c.F) c.F) with hπ
  haveI : IsOpenImmersion Y.jQ := Y.jQ_open
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  haveI hpre : IsPreimmersion π :=
    IsPreimmersion.of_isLocalization (R := 𝓞 c.F) (S := c.F) (nonZeroDivisors (𝓞 c.F))
  haveI hfst : IsPreimmersion (pullback.fst (f ≫ Y.s) π) := inferInstance
  have hcond : (pullback.fst (f ≫ Y.s) π ≫ f) ≫ Y.s = pullback.snd (f ≫ Y.s) π ≫ π := by
    rw [Category.assoc, pullback.condition]
  set g := pullback.lift (pullback.fst (f ≫ Y.s) π ≫ f) (pullback.snd (f ≫ Y.s) π) hcond with hg
  have hgf : g ≫ pullback.fst Y.s π = pullback.fst (f ≫ Y.s) π ≫ f := pullback.lift_fst _ _ _
  have hpt : ∀ p, f (pullback.fst (f ≫ Y.s) π p) = pullback.fst Y.s π (g p) := by
    intro p
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hgf]
  have hopen : IsOpen (g ⁻¹' Set.range Y.jQ) :=
    (IsOpenImmersion.isOpen_range Y.jQ).preimage g.continuous
  refine ⟨⟨g ⁻¹' Set.range Y.jQ, hopen⟩, ?_, ?_⟩
  · have hc2 : M.ξ ≫ f ≫ Y.s = (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) ≫ π := by
      rw [← Category.assoc, hξ]
      simp only [Model.j, Category.assoc, pullback.condition]
      rfl
    set ξ' := pullback.lift M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2 with hξ'
    have hξg : ξ' ≫ g = y₀ ≫ Y.jQ := by
      apply pullback.hom_ext
      · rw [Category.assoc, hgf, ← Category.assoc, pullback.lift_fst, hξ]
        simp only [Model.j, Category.assoc]
        rfl
      · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.assoc]
    set p0 := ξ' (IsLocalRing.closedPoint Ω) with hp0
    have hp0U : p0 ∈ g ⁻¹' Set.range Y.jQ := by
      refine ⟨y₀ (IsLocalRing.closedPoint Ω), ?_⟩
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ pullback Y.s π) => k (IsLocalRing.closedPoint Ω)) hξg
      change g (ξ' (IsLocalRing.closedPoint Ω)) = Y.jQ (y₀ (IsLocalRing.closedPoint Ω)) at h
      exact h.symm
    have hp0M : pullback.fst (f ≫ Y.s) π p0 = genPt M.ξ := by
      have h := congrArg (fun (k : Spec (CommRingCat.of Ω) ⟶ M.X) => k (IsLocalRing.closedPoint Ω))
        (pullback.lift_fst M.ξ (y₀ ≫ Y.jQ ≫ pullback.snd Y.s π) hc2)
      change pullback.fst (f ≫ Y.s) π (ξ' (IsLocalRing.closedPoint Ω)) = M.ξ (IsLocalRing.closedPoint Ω) at h
      exact h
    have hemb := Scheme.Hom.isEmbedding (pullback.fst (f ≫ Y.s) π)
    intro p
    have hsp : p0 ⤳ p := by
      rw [← hemb.isInducing.specializes_iff, hp0M]
      exact M.all _
    exact closure_mono (Set.singleton_subset_iff.2 hp0U) (specializes_iff_mem_closure.1 hsp)
  · ext p
    simp only [Set.mem_preimage, TopologicalSpace.Opens.coe_mk]
    rw [hpt, ← Set.mem_preimage (f := pullback.fst Y.s π), Y.ab_gen]

end GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_open_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω : Type) [Field Ω] (κ : Type) [Finite κ] (x : κ → Ω) (M : PModel ℤ x) (f : M.X ⟶ Y.X) (y₀ : Sp Ω ⟶ Xo.XF c), M.ξ ≫ f = y₀ ≫ Y.j → ∃ U : (pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F))).Opens, Dense (U : Set ((pullback (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) : Scheme.{0}))) ∧ pullback.fst (f ≫ Y.s) (spMap (algebraMap (𝓞 c.F) c.F)) ⁻¹' (f ⁻¹' abLocus Y.t.G) = U := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoModel.OpenLocus.exists_dense_open
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PatchIso

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem unitAt_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (a : Ω) : unitAt ξ' p' a ↔ unitAt ξ p a := by
  unfold unitAt
  rw [h]

theorem char_zero_congr {X' : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ξ' : Spec (CommRingCat.of Ω) ⟶ X'}
    {p : Cpt ξ} {p' : Cpt ξ'} (h : regAt ξ' p' = regAt ξ p) (hp : Char0 ξ p) : Char0 ξ' p' := fun r hr hf =>
  hp r hr fun hu => hf ((unitAt_congr h _).2 hu)

theorem mem_genFib_of_char0 [CharZero Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : Cpt ξ} (hp : Char0 ξ p) :
    p ∈ genFib ξ := by
  have key : ∀ n : ℕ, 0 < n → ((n : Ω))⁻¹ ∈ regAt ξ p := by
    intro n
    induction n using induction_on_primes with
    | zero => exact fun h => absurd h (lt_irrefl 0)
    | one => intro _; simpa using (regAt ξ p).one_mem
    | prime_mul r a hr ih =>
      intro h
      have ha : 0 < a := Nat.pos_of_mul_pos_left h
      have hu : unitAt ξ p (r : Ω) := not_not.1 (hp r hr)
      rw [Nat.cast_mul, mul_inv]
      exact mul_mem hu.2.2 (ih ha)
  exact fun n hn => ⟨Nat.cast_ne_zero.2 hn.ne', natCast_mem _ n, key n hn⟩

theorem exists_below [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁} (hg : IsCptGen ξ₂)
    (hd : GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω))
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p : Cpt ξ₂) (hp : Char0 ξ₂ p) :
    ∃ p₁ : Cpt ξ₁, p₁.1 = g p.1 ∧ Char0 ξ₁ p₁ ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  obtain ⟨h, -, hu⟩ := RegAtDom.regAt_dominates X₁ Ω ξ₁ X₂ Ω ξ₂ g (RingHom.id Ω) hd p
  have c : Char0 ξ₁ ⟨g p.1, h⟩ := fun r hr hf =>
    hf (hu hg (r : Ω) (natCast_mem _ r) (not_not.1 (hp r hr)))
  refine ⟨⟨g p.1, h⟩, rfl, c, ?_⟩
  rw [(hi _ (mem_genFib_of_char0 c)).regAt_eq p rfl, Subring.map_id]

theorem exists_above [CharZero Ω] {X₁ X₂ : Scheme.{0}} {ξ₁ : Spec (CommRingCat.of Ω) ⟶ X₁}
    {ξ₂ : Spec (CommRingCat.of Ω) ⟶ X₂} {g : X₂ ⟶ X₁}
    (hi : ∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) (p₁ : Cpt ξ₁) (hp : Char0 ξ₁ p₁) :
    ∃ p : Cpt ξ₂, g p.1 = p₁.1 ∧ Char0 ξ₂ p ∧ regAt ξ₂ p = regAt ξ₁ p₁ := by
  have I := hi p₁ (mem_genFib_of_char0 hp)
  obtain ⟨p, hp', -⟩ := I.existsUnique
  have e : regAt ξ₂ p = regAt ξ₁ p₁ := by rw [I.regAt_eq p hp', Subring.map_id]
  exact ⟨p, hp', char_zero_congr e hp, e⟩

theorem sncPts_of_isoAt :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ κ₁ κ₂ x₁ x₂ X₁ X₂ ξ₁ ξ₂ g e Ab _ _ _ t₂ hd hi hs p hp
  have ePts : Pts ξ₂ = Pts ξ₁ := by
    ext R
    constructor
    · rintro ⟨p₂, c, rfl⟩
      obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, c₁, r⟩
    · rintro ⟨p₁, c, rfl⟩
      obtain ⟨p₂, -, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, c₂, r.symm⟩
  have eB : regAt ξ₂ '' {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} = regAt ξ₁ '' {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} := by
    ext R
    constructor
    · rintro ⟨p₂, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₁, e₁, c₁, r⟩ := exists_below t₂.gen hd hi p₂ c
      exact ⟨p₁, ⟨c₁, e₁ ▸ ha⟩, r.symm⟩
    · rintro ⟨p₁, ⟨c, ha⟩, rfl⟩
      obtain ⟨p₂, e₂, c₂, r⟩ := exists_above hi p₁ c
      exact ⟨p₂, ⟨c₂, by rwa [e₂]⟩, r⟩
  obtain ⟨p₁, -, c₁, r⟩ := exists_below t₂.gen hd hi p hp
  obtain ⟨A, z, n, q, hP, hq, hl⟩ := hs p₁ c₁
  refine ⟨A, z, n, q, ?_, hq, ?_⟩
  · rw [ePts, eB]
    exact hP
  · rw [r]
    exact hl

end GlobalTheory.CompanionTheory.Ar.PatchIso
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_points_transfer_dominating : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (κ₁ κ₂ : Type) (x₁ : κ₁ → Ω) (x₂ : κ₂ → Ω) (X₁ X₂ : Scheme.{0}) (ξ₁ : Sp Ω ⟶ X₁) (ξ₂ : Sp Ω ⟶ X₂) (g : X₂ ⟶ X₁) (e : ℕ) (Ab : Set X₁), (∀ q : X₁, genPt ξ₁ ⤳ q) → (∀ q : X₂, genPt ξ₂ ⤳ q) → CoordTie ℤ ξ₁ x₁ → CoordTie ℤ ξ₂ x₂ → GlobalTheory.CompanionTheory.Ar.Dominates ξ₂ ξ₁ g (RingHom.id Ω) → (∀ q ∈ genFib ξ₁, IsoAt ξ₂ g (RingHom.id Ω) q) → SncPts ξ₁ e {p | Char0 ξ₁ p ∧ p.1 ∉ Ab} → SncPts ξ₂ e {p | Char0 ξ₂ p ∧ g p.1 ∉ Ab} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.PatchIso.sncPts_of_isoAt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem mem_of_isIntegral_of_isLocAt {Ω : Type} [Field Ω] [CharZero Ω] (R : Subring Ω) [IsFractionRing R Ω]
    (A : Subalgebra ℚ Ω) (hs : Algebra.Smooth ℚ A) (q : Ideal A) (hq : q.IsPrime) (h : IsLocAt A q R)
    (a : Ω) (ha : IsIntegral R a) : a ∈ R := by
  have hAR : ∀ b : A, (b : Ω) ∈ R := fun b =>
    (h b).2 ⟨1, fun h1 => hq.ne_top ((Ideal.eq_top_iff_one q).2 h1), by simp⟩
  letI : Algebra A R := (RingHom.codRestrict A.val.toRingHom R hAR).toAlgebra
  have hmap : ∀ b : A, ((algebraMap A R b : R) : Ω) = b := fun _ => rfl
  have hne : ∀ s : A, s ∉ q → (s : Ω) ≠ 0 := fun s hs0 h0 =>
    hs0 (by rw [show s = 0 from Subtype.ext h0]; exact q.zero_mem)
  haveI : IsLocalization.AtPrime R q :=
    { map_units := by
        rintro ⟨s, hs0⟩
        have hs1 : s ∉ q := hs0
        refine IsUnit.of_mul_eq_one (⟨(s : Ω)⁻¹, (h _).2 ⟨s, hs1, ?_⟩⟩ : R) (Subtype.ext ?_)
        · rw [mul_inv_cancel₀ (hne s hs1)]; exact A.one_mem
        · simp [hmap, mul_inv_cancel₀ (hne s hs1)]
      surj := by
        rintro ⟨r, hr⟩
        obtain ⟨s, hs1, hsr⟩ := (h r).1 hr
        exact ⟨⟨⟨_, hsr⟩, ⟨s, hs1⟩⟩, Subtype.ext (by simp [hmap, mul_comm])⟩
      exists_of_eq := by
        intro x y hxy
        exact ⟨1, by
          have : (x : Ω) = y := by simpa [hmap] using congrArg (Subtype.val) hxy
          rw [Subtype.ext this]⟩ }
  haveI : IsIntegrallyClosed A := GlobalTheory.isIntegrallyClosed_of_smooth ℚ A
  haveI : IsIntegrallyClosed R :=
    isIntegrallyClosed_of_isLocalization R q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  obtain ⟨r, rfl⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := Ω)).1 ha
  exact r.2

end GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch

theorem GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  intro Ω _ _ X ξ N x e Ab hall htie hsnc
  let M0 : PModel ℤ x :=
    { X := X, ξ := ξ, s := specZIsTerminal.from X, hover := specZIsTerminal.hom_ext _ _, all := hall, tie := htie }
  obtain ⟨κ', _, y, M', f, hdom, hnorm, -, hat⟩ := GlobalTheory.T.exists_normal_dominating_model ℤ Ω (Fin (N + 1)) x M0 Ω
  have hdom' : GlobalTheory.CompanionTheory.Ar.Dominates M'.ξ ξ f (RingHom.id Ω) := hdom
  have hiso : ∀ q ∈ genFib ξ, IsoAt M'.ξ f (RingHom.id Ω) q := by
    intro q hq
    have hc : Char0 ξ q := fun r hr hf => hf (hq r hr.pos)
    obtain ⟨A, z, n, P, hp, hP, hloc⟩ := hsnc q hc
    haveI := (GlobalTheory.T.regAt_fraction_noetherian_closed X Ω ξ htie.gen q).1
    exact GlobalTheory.T.normal_iso_of_integrally_closed X Ω ξ M'.X M'.ξ f q (hat q)
      (fun a ha => mem_of_isIntegral_of_isLocAt _ A hp.smooth P hP hloc a ha)
  obtain ⟨N', x', hx'⟩ := GlobalTheory.T.coord_over_int_of_finite_order M'.X Ω M'.ξ ℤ κ' y M'.tie
  have hone := GlobalTheory.T.coords_single_block_segre M'.X Ω M'.ξ N' x' hx'
  have hsnc' := GlobalTheory.T.snc_points_transfer_dominating Ω (Fin (N + 1)) _ x _ X M'.X ξ M'.ξ f e Ab hall M'.all htie hone hdom' hiso hsnc
  exact ⟨Unit, inferInstance, fun _ => Fin (N' + 1), fun _ => inferInstance, fun p => x' p.2,
    { X := M'.X, ξ := M'.ξ, s := M'.s, hover := M'.hover, all := M'.all, tie := hone }, f,
    inferInstance, hdom', hnorm, hsnc'⟩
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projective_coord_model : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (N : ℕ) (x : Fin (N + 1) → Ω) (e : ℕ) (Ab : Set X), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ x → SncPts ξ e {p | Char0 ξ p ∧ p.1 ∉ Ab} → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (M : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (g : M.X ⟶ X), Nonempty K ∧ GlobalTheory.CompanionTheory.Ar.Dominates M.ξ ξ g (RingHom.id Ω) ∧ Flat.NormalCpt M.ξ ∧ SncPts M.ξ e {p | Char0 M.ξ p ∧ g p.1 ∉ Ab} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoModel.NormPatch.exists_normal_model
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GeoModel.Seg

open MvPolynomial GlobalTheory.CompanionTheory.Ar.SegreChart

variable {K : Type} [Fintype K] {J : K → Type} {N : ℕ}

def segPt {R : Type} [CommMonoid R] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → R) :
    (Σ _ : Unit, Fin (N + 1)) → R :=
  fun p => ∏ k, y ⟨k, E p.2 k⟩

def segMap (E : Fin (N + 1) ≃ ((k : K) → J k)) :
    MRing (fun _ : Unit => Fin (N + 1)) →ₐ[ℤ] MRing J :=
  aeval (segPt E fun p => (X p : MRing J))

theorem aeval_segMap {R : Type} [CommRing R] (E : Fin (N + 1) ≃ ((k : K) → J k)) (v : (Σ k, J k) → R)
    (g : MRing (fun _ : Unit => Fin (N + 1))) : aeval v (segMap E g) = aeval (segPt E v) g := by
  rw [segMap, comp_aeval_apply]
  simp only [segPt, map_prod, aeval_X]
  rfl

theorem seg_ratio {Ω : Type} [Field Ω] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω)
    (c : (k : K) → J k) (p : Σ _ : Unit, Fin (N + 1)) :
    segPt E y p / segPt E y ⟨p.1, E.symm c⟩ = segPt E (fun p => y p / y ⟨p.1, c p.1⟩) p := by
  simp only [segPt, Equiv.apply_symm_apply, Finset.prod_div_distrib]

theorem adjoin_ratios_seg {Ω : Type} [Field Ω] [Algebra ℚ Ω] (E : Fin (N + 1) ≃ ((k : K) → J k))
    (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) :
    Algebra.adjoin ℚ (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) =
      Algebra.adjoin ℚ (Set.range fun p : Σ _ : Unit, Fin (N + 1) =>
        segPt E y p / segPt E y ⟨p.1, E.symm c⟩) := by
  classical
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨⟨k, i⟩, rfl⟩
    have h1 := seg_ratio_update y c hc k i
    refine Algebra.subset_adjoin ⟨⟨(), E.symm (Function.update c k i)⟩, ?_⟩
    simp only [segPt, Equiv.apply_symm_apply]
    exact h1
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨p, rfl⟩
    rw [SetLike.mem_coe]
    simp only [seg_ratio]
    exact prod_mem fun k _ => Algebra.subset_adjoin ⟨⟨k, E p.2 k⟩, rfl⟩

theorem clause_map {σ τ Ω : Type} [Field Ω] [Algebra ℚ Ω] (S : Subalgebra ℚ Ω) (v : σ → Ω) (hv : ∀ p, v p ∈ S)
    (v₁ : τ → Ω) (φ : MvPolynomial τ ℤ →ₐ[ℤ] MvPolynomial σ ℤ) (hφ : ∀ g, aeval v (φ g) = aeval v₁ g)
    (I : Ideal (MvPolynomial τ ℤ)) (q : Ideal S) :
    (∀ g ∈ I.map φ, ∀ s : S, (s : Ω) = aeval v g → s ∈ q) ↔
      ∀ g ∈ I, ∀ s : S, (s : Ω) = aeval v₁ g → s ∈ q := by
  let ev : MvPolynomial σ ℤ →ₐ[ℤ] S := aeval fun p => (⟨v p, hv p⟩ : S)
  have hev : ∀ g, ((ev g : S) : Ω) = aeval v g := fun g => by
    induction g using MvPolynomial.induction_on with
    | C a => simp [ev]
    | add p q hp hq => simp only [map_add, Subalgebra.coe_add, hp, hq]
    | mul_X p i hp => simp only [map_mul, Subalgebra.coe_mul, hp]; simp [ev]
  constructor
  · exact fun h g hg s hs => h _ (Ideal.mem_map_of_mem _ hg) s (hs.trans (hφ g).symm)
  · intro h g hg s hs
    have hle : I.map φ ≤ q.comap ev :=
      Ideal.map_le_iff_le_comap.2 fun g hg => h g hg _ ((hev _).trans (hφ g))
    have e : s = ev g := Subtype.ext (hs.trans (hev g).symm)
    rw [e]
    exact hle hg

theorem isSncModel_seg {Ω : Type} [Field Ω] [Algebra ℚ Ω] [∀ k, Fintype (J k)]
    (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω) (e : ℕ)
    (bd₁ : Ideal (MRing (fun _ : Unit => Fin (N + 1)))) (h : Cmp.IsSncModel (segPt E y) e bd₁) :
    Cmp.IsSncModel y e (bd₁.map (segMap E)) := by
  intro c hc
  have h0 : ∀ k : Unit, segPt E y ⟨k, E.symm c⟩ ≠ 0 := fun k => by
    simp only [segPt, Equiv.apply_symm_apply]
    exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨m, f, b, hf, hb, hsum, hS⟩ := h (fun _ => E.symm c) h0
  have hA := adjoin_ratios_seg E y c hc
  refine ⟨m, f, b, fun l => ?_, fun l => ?_, hsum, fun l hfl S hSeq => ?_⟩
  · rw [hA]
    exact hf l
  · rw [hA]
    exact hb l
  have hS' : S = Algebra.adjoin ℚ (insert (f l)⁻¹ (Set.range fun p : Σ _ : Unit, Fin (N + 1) =>
      segPt E y p / segPt E y ⟨p.1, E.symm c⟩)) := by
    rw [hSeq, ← Algebra.adjoin_insert_adjoin, hA, Algebra.adjoin_insert_adjoin]
  obtain ⟨hsm, z, n, hn, hli, hspan, hq⟩ := hS l hfl S hS'
  refine ⟨hsm, z, n, hn, hli, hspan, fun q hqp => ?_⟩
  have hv : ∀ p : Σ k, J k, y p / y ⟨p.1, c p.1⟩ ∈ S := fun p => by
    rw [hSeq]
    exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ ⟨p, rfl⟩)
  rw [← hq q hqp]
  refine clause_map S _ hv _ (segMap E) (fun g => ?_) bd₁ q
  rw [aeval_segMap]
  congr 2
  funext p
  exact (seg_ratio E y c p).symm

theorem mem_mcPts_seg (E : Fin (N + 1) ≃ ((k : K) → J k)) (bd₁ : Ideal (MRing (fun _ : Unit => Fin (N + 1))))
    (w : (Σ k, J k) → ℂ) (hw : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) :
    w ∈ mcPts (bd₁.map (segMap E)) ↔ segPt E w ∈ mcPts bd₁ := by
  have hval : ∀ g, eval w (map (Int.castRingHom ℂ) (segMap E g)) =
      eval (segPt E w) (map (Int.castRingHom ℂ) g) := fun g => by
    rw [eval_map_int, eval_map_int, aeval_segMap]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun _ => ?_, fun g hg => ?_⟩
    · choose c hc using hw
      refine ⟨E.symm c, ?_⟩
      simp only [segPt, Equiv.apply_symm_apply]
      exact Finset.prod_ne_zero_iff.2 fun k _ => hc k
    · rw [← hval]
      exact h _ (Ideal.mem_map_of_mem _ hg)
  · rintro ⟨-, h⟩
    refine ⟨hw, fun f hf => ?_⟩
    have hle : bd₁.map (segMap E) ≤ RingHom.ker (aeval w : MRing J →ₐ[ℤ] ℂ) :=
      Ideal.map_le_iff_le_comap.2 fun g hg => by
        have h1 := h g hg
        rw [eval_map_int, ← aeval_segMap] at h1
        exact h1
    rw [eval_map_int]
    exact hle hf

section Val

variable {Sc : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ Sc}
  {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ Sc}

theorem valAt_one (h : genPt ξ ⤳ centre z) : ValAt ξ z (1 : Ω) (1 : R) :=
  ⟨h, 1, map_one _, map_one _⟩

theorem valAt_mul {a b : Ω} {r t : R} (ha : ValAt ξ z a r) (hb : ValAt ξ z b t) : ValAt ξ z (a * b) (r * t) := by
  obtain ⟨h, s, rfl, rfl⟩ := ha
  obtain ⟨-, s', rfl, rfl⟩ := hb
  exact ⟨h, s * s', map_mul _ _ _, map_mul _ _ _⟩

theorem valAt_prod {α : Type} (h : genPt ξ ⤳ centre z) (s : Finset α) (a : α → Ω) (r : α → R)
    (H : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using valAt_one h
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact valAt_mul (H i (Finset.mem_insert_self i s))
      (ih fun j hj => H j (Finset.mem_insert_of_mem hj))

theorem coordsAt_seg [Nonempty K] (E : Fin (N + 1) ≃ ((k : K) → J k)) (y : (Σ k, J k) → Ω)
    (z : Spec (CommRingCat.of ℂ) ⟶ Sc) (w : (Σ k, J k) → ℂ) (h : CoordsAt ξ y z w) :
    CoordsAt ξ (segPt E y : (Σ _ : Unit, Fin (N + 1)) → Ω) z (segPt E w) := by
  obtain ⟨hb, hr⟩ := h
  refine ⟨fun _ => ?_, fun _ j hj => ?_⟩
  · choose c hc using hb
    refine ⟨E.symm c, ?_⟩
    simp only [segPt, Equiv.apply_symm_apply]
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => (hc k).ne_zero)
  · have huj : ∀ k, IsUnit (w ⟨k, E j k⟩) := fun k =>
      isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 (show (∏ k, w ⟨k, E j k⟩) ≠ 0 from hj.ne_zero) k
        (Finset.mem_univ k))
    have h0 : ∀ k, y ⟨k, E j k⟩ ≠ 0 := fun k => (hr k _ (huj k)).1
    refine ⟨Finset.prod_ne_zero_iff.2 fun k _ => h0 k, fun i => ?_⟩
    choose r hrv hrw using fun k => (hr k _ (huj k)).2 (E i k)
    have hgen : genPt ξ ⤳ centre z := by
      obtain ⟨k⟩ := ‹Nonempty K›
      exact (hrv k).choose
    refine ⟨∏ k, r k, ?_, ?_⟩
    · have h1 := valAt_prod hgen Finset.univ _ _ fun k _ => hrv k
      rw [Finset.prod_div_distrib] at h1
      exact h1
    · show (∏ k, w ⟨k, E i k⟩) = (∏ k, r k) * ∏ k, w ⟨k, E j k⟩
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun k _ => hrw k

end Val

theorem points_of_isEmpty [IsEmpty K] [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [CharZero Ω] {Sc : Scheme.{0}}
    {ξ : Sp Ω ⟶ Sc} (y : (Σ k, J k) → Ω) (e : ℕ) (B : Set (Cpt ξ)) (bd : Ideal (MRing J))
    (hs : Cmp.IsSncModel y e bd) (hB : ∀ p ∈ B, Char0 ξ p) (hP : SncPts ξ e B)
    (z : Spec (CommRingCat.of ℂ) ⟶ Sc) (w : (Σ k, J k) → ℂ) :
    w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B := by
  haveI hE : IsEmpty (Σ k, J k) := ⟨fun p => isEmptyElim p.1⟩
  let c : (k : K) → J k := fun k => isEmptyElim k
  obtain ⟨m, f, a, hf, ha, hsum, hS⟩ := hs c (fun k => isEmptyElim k)
  have hr : (Set.range fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) = ∅ := Set.range_eq_empty _
  rw [hr] at hf ha hS
  rw [Algebra.adjoin_empty] at hf ha
  obtain ⟨l, hl⟩ : ∃ l, f l ≠ 0 := by
    by_contra hall
    push_neg at hall
    simp [hall] at hsum
  obtain ⟨hsm, zz, n, hn, hli, hspan, hq⟩ := hS l hl _ rfl
  set S : Subalgebra ℚ Ω := Algebra.adjoin ℚ (insert (f l)⁻¹ ∅) with hSdef
  have hbot : S ≤ ⊥ := by
    refine Algebra.adjoin_le ?_
    rintro _ (rfl | h)
    · obtain ⟨t, ht⟩ := Algebra.mem_bot.1 (hf l)
      exact Algebra.mem_bot.2 ⟨t⁻¹, by rw [← ht, map_inv₀]⟩
    · exact absurd h (Set.notMem_empty _)
  have hD : ∀ s : S, KaehlerDifferential.D ℚ S s = 0 := fun s => by
    obtain ⟨t, ht⟩ := Algebra.mem_bot.1 (hbot s.2)
    have e1 : s = algebraMap ℚ S t := Subtype.ext ht.symm
    rw [e1]
    exact (KaehlerDifferential.D ℚ S).map_algebraMap t
  haveI hFe : IsEmpty (Fin e) := ⟨fun i => hli.ne_zero i (hD _)⟩
  have hcl := hq ⊥ Ideal.isPrime_bot
  obtain ⟨g, hg, s, hs1, hs0⟩ : ∃ g ∈ bd, ∃ s : S, (s : Ω) = aeval (fun p : Σ k, J k => y p / y ⟨p.1, c p.1⟩) g ∧
      s ∉ (⊥ : Ideal S) := by
    by_contra hall
    push_neg at hall
    obtain ⟨i, -⟩ := hcl.1 hall
    exact isEmptyElim i
  constructor
  · rintro ⟨-, hz⟩
    exfalso
    have h1 := hz g hg
    rw [eq_C_of_isEmpty g] at h1 hs1
    apply hs0
    rw [Ideal.mem_bot]
    apply Subtype.ext
    simp at h1 hs1
    simp [hs1, h1]
  · rintro ⟨h, hp⟩
    exfalso
    obtain ⟨A, zA, nA, qA, hpa, hqA, hl'⟩ := hP _ (hB _ hp)
    obtain ⟨R, -, hRl, hbd⟩ := hpa.pts qA hqA
    have hR : R = regAt ξ ⟨centre z, h⟩ := Subring.ext fun a => (hRl a).trans (hl' a).symm
    obtain ⟨i, -⟩ := hbd.1 ⟨_, hp, hR.symm⟩
    exact isEmptyElim i

end GlobalTheory.CompanionTheory.Ar.GeoModel.Seg

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

open Seg in

theorem exists_isSncModel_of_sncPts : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ p ∈ B, Char0 ξ p) → SncPts ξ e B → ∃ bd : Ideal (MRing J), Cmp.IsSncModel y e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  intro Ω _ _ X ξ K _ J _ y e B hT hB hP
  obtain ⟨c₀, -⟩ := hT.cover ⟨genPt ξ, specializes_rfl⟩
  haveI : Nonempty ((k : K) → J k) := ⟨c₀⟩
  have hcard : 0 < Nat.card ((k : K) → J k) := Nat.card_pos
  obtain ⟨N, hN⟩ := Nat.exists_eq_succ_of_ne_zero hcard.ne'
  let E : Fin (N + 1) ≃ ((k : K) → J k) := (Finite.equivFinOfCardEq hN).symm
  have hTx : CoordTie ℤ ξ (fun j : Fin (N + 1) => ∏ k, y ⟨k, E j k⟩) := CoordBase.coordTie_reindex E hT
  obtain ⟨bd₁, hs, hpt⟩ := GlobalTheory.T.exists_snc_model_of_patches Ω X ξ N _ e B hTx hB hP
  have hs' := isSncModel_seg E y e bd₁ hs
  refine ⟨bd₁.map (segMap E), hs', fun z w hw => ?_⟩
  rcases isEmpty_or_nonempty K with hK | hK
  · exact points_of_isEmpty y e B _ hs' hB hP z w
  · have hnz : ∀ k, ∃ i, w ⟨k, i⟩ ≠ 0 := fun k => by
      obtain ⟨i, hi⟩ := hw.1 k
      exact ⟨i, hi.ne_zero⟩
    rw [mem_mcPts_seg E bd₁ w hnz]
    exact hpt z _ (coordsAt_seg E y z w hw)

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_model_boundary_coords : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (e : ℕ) (B : Set (Cpt ξ)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ p ∈ B, Char0 ξ p) → SncPts ξ e B → ∃ bd : Ideal (MRing J), Cmp.IsSncModel y e bd ∧ ∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ ∃ h : genPt ξ ⤳ centre z, (⟨centre z, h⟩ : Cpt ξ) ∈ B) := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.GeoModel.exists_isSncModel_of_sncPts
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.DetLine

theorem matrix_eq_mul {Ω E : Type} [Field Ω] [AddCommGroup E] [Module Ω E] {r : ℕ} {b₀ c b : Fin r → E}
    {T T' A : Matrix (Fin r) (Fin r) Ω} (hb₀ : LinearIndependent Ω b₀)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k')
    (hA : ∀ k, b k = ∑ i, A i k • c i) : T' = T * A := by
  ext i k
  have h : ∑ k', (T' k' k - (T * A) k' k) • b₀ k' = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, Matrix.mul_apply, Finset.sum_smul, ← hT']
    rw [sub_eq_zero, hA k, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul, _root_.mul_comm]
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hb₀ _ h i)

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]

theorem det_mem_span (L : Lat ξ E) {r : ℕ} {b₀ c b : Fin r → E} {q : Cpt ξ} {T T' : Matrix (Fin r) (Fin r) Ω}
    (hb₀ : LinearIndependent Ω b₀) (hc : L.IsFrameAt c q) (hb : L.IsFrameAt b q)
    (hT : ∀ k, c k = ∑ k', T k' k • b₀ k') (hT' : ∀ k, b k = ∑ k', T' k' k • b₀ k') :
    T'.det ∈ Submodule.span (regAt ξ q) {T.det} := by
  have hmem : ∀ k, b k ∈ Submodule.span (regAt ξ q) (Set.range c) := fun k => by
    rw [← hc.2, hb.2]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun (regAt ξ q)).1 (hmem k)
  let M : Matrix (Fin r) (Fin r) (regAt ξ q) := Matrix.of fun i k => a k i
  have hM : T' = T * (regAt ξ q).subtype.mapMatrix M :=
    matrix_eq_mul hb₀ hT hT' fun k => (ha k).symm
  refine Submodule.mem_span_singleton.2 ⟨M.det, ?_⟩
  rw [hM, Matrix.det_mul, ← RingHom.map_det, _root_.mul_comm]
  rfl

theorem isVB_detLat : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E]
    (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ →
    Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  intro X Ω _ ξ E _ _ L r V b₀ hb₀ hsp hL p _
  obtain ⟨U, hU, c, hc, hf⟩ := hL p trivial
  have hcV : ∀ k, c k ∈ Submodule.span Ω (Set.range b₀) := fun k => by
    rw [hsp, ← hc]
    exact Submodule.subset_span ⟨k, rfl⟩
  have hbV : ∀ k, b₀ k ∈ Submodule.span Ω (Set.range c) := fun k => by
    rw [hc, ← hsp]
    exact Submodule.subset_span ⟨k, rfl⟩
  choose a ha using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hcV k)
  choose s hs using fun k => (Submodule.mem_span_range_iff_exists_fun Ω).1 (hbV k)
  let T : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => a k i
  let S : Matrix (Fin r) (Fin r) Ω := Matrix.of fun i k => s k i
  have hT : ∀ k, c k = ∑ k', T k' k • b₀ k' := fun k => (ha k).symm
  have hTS : (1 : Matrix (Fin r) (Fin r) Ω) = T * S :=
    matrix_eq_mul hb₀ hT (fun k => by simp [Matrix.one_apply, ite_smul]) fun k => (hs k).symm
  have ht : T.det ≠ 0 := fun h => by
    have := congrArg Matrix.det hTS
    rw [Matrix.det_one, Matrix.det_mul, h, zero_mul] at this
    exact one_ne_zero this
  refine ⟨U, hU, fun _ => T.det, ?_, fun q _ hq => ⟨?_, ?_⟩⟩
  · refine eq_top_iff.2 fun x _ => ?_
    have hx : x = (x * T.det⁻¹) • T.det := by
      rw [smul_eq_mul, _root_.mul_assoc, inv_mul_cancel₀ ht, _root_.mul_one]
    rw [hx]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  · exact linearIndependent_unique_iff.2 ht
  · have hr : Set.range (fun _ : Fin 1 => T.det) = {T.det} := Set.range_const
    rw [hr]
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨b, T', hfr, hT', rfl⟩
      exact det_mem_span L hb₀ (hf q trivial hq) hfr hT hT'
    · rintro _ rfl
      exact ⟨c, T, hf q trivial hq, hT, rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.DetLine
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_lattice_line_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (r : ℕ) (V : Submodule Ω E) (b₀ : Fin r → E), LinearIndependent Ω b₀ → Submodule.span Ω (Set.range b₀) = V → L.IsVB r V → (Cusp.detLat L b₀).IsVB 1 ⊤ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Cusp.DetLine.isVB_detLat
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.VertForm

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {K : Type} [Fintype K] [DecidableEq K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω]

abbrev segCo (y : (Σ k, J k) → Ω) : ((k : K) → J k) → Ω := fun c' => ∏ k, y ⟨k, c' k⟩

abbrev chartA (y : (Σ k, J k) → Ω) (c : (k : K) → J k) : Subalgebra ℤ Ω :=
  Algebra.adjoin ℤ (Set.range fun j => segCo y j / segCo y c)

def ym (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d : K → ℕ) : Ω := ∏ k, y ⟨k, c k⟩ ^ d k

variable {y : (Σ k, J k) → Ω} {c : (k : K) → J k}

theorem aeval_xpow (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d : K → ℕ) :
    MvPolynomial.aeval y (xpow c d) = ym y c d := by
  simp [xpow, ym, map_prod]

theorem ym_add (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (d e : K → ℕ) :
    ym y c (d + e) = ym y c d * ym y c e := by
  simp [ym, pow_add, Finset.prod_mul_distrib]

theorem ym_ne_zero (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : K → ℕ) : ym y c d ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun k _ => pow_ne_zero _ (hy k)

theorem xpow_notMem {W : Ideal (MRing J)} [hW : W.IsPrime] (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W)
    (d : K → ℕ) : xpow c d ∉ W := by
  intro h
  obtain ⟨k, -, hk⟩ := (Ideal.IsPrime.prod_mem_iff).1 h
  exact hc k (hW.mem_of_pow_mem _ hk)

theorem mh_add {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f + g) a := by
  classical
  intro m hm k
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hf m h k
  · exact hg m h k

theorem mh_sub {f g : MRing J} {a : K → ℕ} (hf : IsMultiHomog f a) (hg : IsMultiHomog g a) :
    IsMultiHomog (f - g) a := by
  rw [sub_eq_add_neg]
  refine mh_add hf fun m hm k => hg m ?_ k
  rwa [MvPolynomial.support_neg] at hm

def IsRep (y : (Σ k, J k) → Ω) (c : (k : K) → J k) (s : Ω) (d : K → ℕ) (G : MRing J) : Prop :=
  IsMultiHomog G d ∧ MvPolynomial.aeval y G = s * ym y c d

theorem IsRep.mul {s s' : Ω} {d d' : K → ℕ} {G G' : MRing J} (h : IsRep y c s d G) (h' : IsRep y c s' d' G') :
    IsRep y c (s * s') (d + d') (G * G') :=
  ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 h'.1, by rw [map_mul, h.2, h'.2, ym_add]; ring⟩

theorem IsRep.add {s s' : Ω} {d d' : K → ℕ} {G G' : MRing J} (h : IsRep y c s d G) (h' : IsRep y c s' d' G') :
    IsRep y c (s + s') (d + d') (G * xpow c d' + G' * xpow c d) :=
  ⟨mh_add (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 (isMultiHomog_xpow c d'))
      (by rw [add_comm d d']; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h'.1 (isMultiHomog_xpow c d)),
    by rw [map_add, map_mul, map_mul, aeval_xpow, aeval_xpow, h.2, h'.2, ym_add]; ring⟩

theorem exists_rep (hc : segCo y c ≠ 0) {s : Ω} (hs : s ∈ chartA y c) : ∃ d G, IsRep y c s d G := by
  induction hs using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    refine ⟨1, xpow j 1, isMultiHomog_xpow _ _, ?_⟩
    have e : ∀ c', ym y c' 1 = segCo y c' := fun c' => by simp [ym, segCo]
    rw [aeval_xpow, e, e, div_mul_cancel₀ _ hc]
  | algebraMap n => exact ⟨0, MvPolynomial.C n, isMultiHomog_C_zero n, by simp [ym]⟩
  | add a b _ _ ha hb =>
    obtain ⟨d, G, h⟩ := ha
    obtain ⟨d', G', h'⟩ := hb
    exact ⟨_, _, h.add h'⟩
  | mul a b _ _ ha hb =>
    obtain ⟨d, G, h⟩ := ha
    obtain ⟨d', G', h'⟩ := hb
    exact ⟨_, _, h.mul h'⟩

theorem IsRep.mem_of_mem {W : Ideal (MRing J)} [hW : W.IsPrime] (hP : mCoordIdeal y ≤ W)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W) {s : Ω} {d d' : K → ℕ} {G G' : MRing J}
    (h : IsRep y c s d G) (h' : IsRep y c s d' G') (hG : G ∈ W) : G' ∈ W := by
  have h0 : G * xpow c d' - G' * xpow c d ∈ mCoordIdeal y := by
    refine mem_mCoordIdeal_of_aeval_eq_zero y (d := d + d')
      (mh_sub (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h.1 (isMultiHomog_xpow c d'))
        (by rw [add_comm d d']; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul h'.1 (isMultiHomog_xpow c d))) ?_
    rw [map_sub, map_mul, map_mul, aeval_xpow, aeval_xpow, h.2, h'.2]
    ring
  have h1 : G' * xpow c d ∈ W := by
    have := W.sub_mem (W.mul_mem_right (xpow c d') hG) (hP h0)
    simpa using this
  exact (hW.mem_or_mem h1).resolve_right (xpow_notMem hc d)

theorem exists_prime (hsc : segCo y c ≠ 0) {W : Ideal (MRing J)} [hW : W.IsPrime] (hP : mCoordIdeal y ≤ W)
    (hc : ∀ k, (MvPolynomial.X ⟨k, c k⟩ : MRing J) ∉ W) :
    ∃ I : Ideal (chartA y c), I.IsPrime ∧
      ∀ s : chartA y c, s ∈ I ↔ ∃ d G, IsRep y c (s : Ω) d G ∧ G ∈ W := by
  let I : Ideal (chartA y c) :=
    { carrier := {s | ∃ d G, IsRep y c (s : Ω) d G ∧ G ∈ W}
      add_mem' := by
        rintro a b ⟨d, G, h, hG⟩ ⟨d', G', h', hG'⟩
        exact ⟨d + d', _, h.add h', W.add_mem (W.mul_mem_right _ hG) (W.mul_mem_right _ hG')⟩
      zero_mem' := ⟨0, 0, ⟨fun m hm => by simp at hm, by simp⟩, W.zero_mem⟩
      smul_mem' := by
        rintro r a ⟨d, G, h, hG⟩
        obtain ⟨e, R, hR⟩ := exists_rep hsc r.2
        exact ⟨e + d, R * G, hR.mul h, W.mul_mem_left _ hG⟩ }
  refine ⟨I, Ideal.isPrime_iff.2 ⟨fun ht => ?_, fun {a b} hab => ?_⟩, fun s => Iff.rfl⟩
  · have h1 : (1 : chartA y c) ∈ I := ht ▸ Submodule.mem_top
    obtain ⟨d, G, h, hG⟩ := h1
    have h2 : IsRep y c ((1 : chartA y c) : Ω) 0 1 := ⟨ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_one, by simp [ym]⟩
    exact hW.ne_top ((Ideal.eq_top_iff_one W).2 (h.mem_of_mem hP hc h2 hG))
  · obtain ⟨d, G, h, hG⟩ := hab
    obtain ⟨e, A, hA⟩ := exists_rep hsc a.2
    obtain ⟨e', B, hB⟩ := exists_rep hsc b.2
    have h3 : A * B ∈ W := h.mem_of_mem hP hc (hA.mul hB) hG
    rcases hW.mem_or_mem h3 with h4 | h4
    · exact Or.inl ⟨e, A, hA, h4⟩
    · exact Or.inr ⟨e', B, hB, h4⟩

theorem unitAt_mul {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ} {a b : Ω}
    (ha : unitAt ξ q a) (hb : unitAt ξ q b) : unitAt ξ q (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact mul_mem ha.2.2 hb.2.2⟩

theorem exists_frac {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hT : CoordTie ℤ ξ (segCo y))
    (hc : InChart ξ (segCo y) c (CptModel.self ξ)) (e : Ω) :
    ∃ (d : K → ℕ) (F G : MRing J), IsMultiHomog F d ∧ IsMultiHomog G d ∧ MvPolynomial.aeval y G ≠ 0 ∧
      MvPolynomial.aeval y F = e * MvPolynomial.aeval y G := by
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨s, hs, hu, hse⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (segCo y) hT c (CptModel.self ξ) hc e).1
    (by rw [CptModel.regAt_self hT.gen]; trivial)
  obtain ⟨d, G, hG⟩ := exists_rep hc.1 hs
  obtain ⟨d', F, hF⟩ := exists_rep hc.1 hse
  refine ⟨d' + d, F * xpow c d, G * xpow c d', ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hF.1 (isMultiHomog_xpow _ _),
    by rw [add_comm]; exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hG.1 (isMultiHomog_xpow _ _), ?_, ?_⟩
  · rw [map_mul, aeval_xpow, hG.2]
    exact mul_ne_zero (mul_ne_zero hu.1 (ym_ne_zero hy _)) (ym_ne_zero hy _)
  · rw [map_mul, map_mul, aeval_xpow, aeval_xpow, hG.2, hF.2]
    ring

theorem zpow_ym (hy : ∀ k, y ⟨k, c k⟩ ≠ 0) (a : K → ℤ) :
    (∏ k, y ⟨k, c k⟩ ^ a k) * ym y c (fun k => (-a k).toNat) = ym y c (fun k => (a k).toNat) := by
  rw [ym, ym, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hy k)]
  congr 1
  omega

theorem unit_off {X : Scheme.{0}} {ξ : Spec (CommRingCat.of Ω) ⟶ X} {p : ℕ} {Δ : Lat ξ Ω} {a : K → ℤ} {e₀ : Ω}
    (hT : CoordTie ℤ ξ (segCo y)) (hDeg : Δ.IsDegOn Set.univ y a e₀)
    (hΔ : ∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) {f g : MRing J} {bf bg : K → ℕ}
    (hf : IsMultiHomog f bf) (hg : IsMultiHomog g bg) (hb : ∀ k, (bf k : ℤ) - bg k = - a k)
    (hfg : MvPolynomial.aeval y f = e₀ * MvPolynomial.aeval y g) (W : Ideal (MRing J)) (hW : W.IsPrime)
    (hP : mCoordIdeal y ≤ W) (hrel : IsRelevant W) (hp : (MvPolynomial.C (p : ℤ) : MRing J) ∉ W) :
    ∃ u v : MRing J, u ∉ W ∧ v ∉ W ∧ u * f - v * g ∈ mCoordIdeal y := by
  choose c hc using hrel
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (hP (mem_mCoordIdeal_of_aeval_eq_zero y
    (isMultiHomog_X' k (c k)) (by simpa using h0)))
  have hsc : segCo y c ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hy k
  obtain ⟨I, hI, hmem⟩ := exists_prime hsc hP hc
  obtain ⟨q, ⟨hq, hu⟩, -⟩ := GlobalTheory.T.prime_chart_existsUnique_point X Ω ξ ℤ _ (segCo y) hT c hsc I hI
  have hpI : (p : chartA y c) ∉ I := fun h => by
    obtain ⟨d, G, hr, hG⟩ := (hmem _).1 h
    have h2 : IsRep y c (((p : chartA y c)) : Ω) 0 (MvPolynomial.C (p : ℤ)) :=
      ⟨isMultiHomog_C_zero _, by simp [ym]⟩
    exact hp (hr.mem_of_mem hP hc h2 hG)
  have hpu : unitAt ξ q (p : Ω) := by simpa using (hu _).1 hpI
  have hΔ1 := hΔ q (fun hf' => hf' hpu)
  have hΔ2 := hDeg.2 q trivial c hq
  obtain ⟨s, hs⟩ : ∃ s, s = (∏ k, y ⟨k, c k⟩ ^ a k) * e₀ := ⟨_, rfl⟩
  rw [smul_eq_mul, ← hs] at hΔ2
  have hs1 : s ∈ Submodule.span (regAt ξ q) {(1 : Ω)} := by
    rw [← hΔ1, hΔ2]; exact Submodule.mem_span_singleton_self _
  have h1s : (1 : Ω) ∈ Submodule.span (regAt ξ q) {s} := by
    rw [← hΔ2, hΔ1]; exact Submodule.mem_span_singleton_self _
  obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 hs1
  obtain ⟨r', hr'⟩ := Submodule.mem_span_singleton.1 h1s
  have hr2 : (r : Ω) = s := by simpa [Subring.smul_def] using hr
  have hr3 : (r' : Ω) * s = 1 := by simpa [Subring.smul_def] using hr'
  have hsu : unitAt ξ q s := ⟨right_ne_zero_of_mul_eq_one hr3, hr2 ▸ r.2, by
    rw [← eq_inv_of_mul_eq_one_left hr3]; exact r'.2⟩
  obtain ⟨t, ht, hut, hts⟩ := (GlobalTheory.T.regAt_iff_chart_localization X Ω ξ ℤ _ (segCo y) hT c q hq s).1 hsu.2.1
  have hv : (⟨t, ht⟩ : chartA y c) ∉ I := (hu _).2 hut
  have hu' : (⟨t * s, hts⟩ : chartA y c) ∉ I := (hu _).2 (unitAt_mul hut hsu)
  obtain ⟨dv, V, hV⟩ := exists_rep hsc ht
  obtain ⟨du, U, hU⟩ := exists_rep hsc hts
  have hVW : V ∉ W := fun h => hv ((hmem _).2 ⟨dv, V, hV, h⟩)
  have hUW : U ∉ W := fun h => hu' ((hmem _).2 ⟨du, U, hU, h⟩)
  have hZ := zpow_ym hy a
  refine ⟨V * xpow c (du + fun k => (a k).toNat), U * xpow c (dv + fun k => (-a k).toNat),
    fun h => (hW.mem_or_mem h).elim hVW (xpow_notMem hc _),
    fun h => (hW.mem_or_mem h).elim hUW (xpow_notMem hc _), ?_⟩
  refine mem_mCoordIdeal_of_aeval_eq_zero y (d := dv + (du + fun k => (a k).toNat) + bf)
    (mh_sub (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hV.1 (isMultiHomog_xpow _ _)) hf) ?_) ?_
  · have e : dv + (du + fun k => (a k).toNat) + bf = du + (dv + fun k => (-a k).toNat) + bg := by
      funext k
      have := hb k
      simp only [Pi.add_apply]
      omega
    rw [e]
    exact ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hU.1 (isMultiHomog_xpow _ _)) hg
  · rw [map_sub, map_mul, map_mul, map_mul, map_mul, aeval_xpow, aeval_xpow, hV.2, hU.2, hfg, ym_add, ym_add,
      ← hZ, hs]
    ring

end GlobalTheory.CompanionTheory.Ar.VertForm

theorem GlobalTheory.CompanionTheory.Ar.VertForm.exists_vertical : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) (Δ : Lat ξ Ω) (a : K → ℤ) (e₀ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Δ.IsDegOn Set.univ y a e₀ → (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) → ∃ f g : MRing J, IsVerticalDivisorAt (mCoordIdeal y) p (-a) f g ∧ MvPolynomial.aeval y g ≠ 0 ∧ MvPolynomial.aeval y f / MvPolynomial.aeval y g = e₀ := by
  intro X Ω _ ξ K _ J _ y p Δ a e₀ hT _ hDeg hΔ
  classical
  obtain ⟨c, hc⟩ := hT.cover (CptModel.self ξ)
  have hy : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hc.1 k (Finset.mem_univ k)
  obtain ⟨d, F, G, hF, hG, hG0, hFG⟩ :=
    GlobalTheory.CompanionTheory.Ar.VertForm.exists_frac (y := y) hT hc (e₀ * ∏ k, y ⟨k, c k⟩ ^ a k)
  have hZ := GlobalTheory.CompanionTheory.Ar.VertForm.zpow_ym hy a
  have hg0 : MvPolynomial.aeval y (G * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (a k).toNat) ≠ 0 := by
    rw [map_mul, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow]
    exact mul_ne_zero hG0 (GlobalTheory.CompanionTheory.Ar.VertForm.ym_ne_zero hy _)
  have hfg : MvPolynomial.aeval y (F * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (-a k).toNat) =
      e₀ * MvPolynomial.aeval y (G * ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.xpow c fun k => (a k).toNat) := by
    rw [map_mul, map_mul, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow, GlobalTheory.CompanionTheory.Ar.VertForm.aeval_xpow, hFG, ← hZ]
    ring
  have hb : ∀ k, (((d + fun k => (-a k).toNat) k : ℕ) : ℤ) - ((d + fun k => (a k).toNat) k : ℕ) = -a k := by
    intro k
    simp only [Pi.add_apply]
    omega
  have hFm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hF (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c fun k => (-a k).toNat)
  have hGm := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_mul hG (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.isMultiHomog_xpow c fun k => (a k).toNat)
  refine ⟨_, _, ⟨⟨_, _, hFm, hGm, funext hb⟩, fun h => ?_, fun h => ?_, fun W hW hP hrel hp => ?_⟩, hg0, ?_⟩
  · exact mul_ne_zero hDeg.1 hg0 (hfg ▸ SegreChart.aeval_eq_zero_of_mem y h)
  · exact hg0 (SegreChart.aeval_eq_zero_of_mem y h)
  · exact GlobalTheory.CompanionTheory.Ar.VertForm.unit_off hT hDeg hΔ hFm hGm hb hfg W hW hP hrel hp
  · rw [hfg, mul_div_cancel_right₀ _ hg0]
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase GlobalTheory.CompanionTheory.Ar.GeoModel
open GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vertical_divisor_degree : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (p : ℕ) (Δ : Lat ξ Ω) (a : K → ℤ) (e₀ : Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ q : X, genPt ξ ⤳ q) → Δ.IsDegOn Set.univ y a e₀ → (∀ q, ¬ InFibre ξ p q → Δ q = Submodule.span (regAt ξ q) {1}) → ∃ f g : MRing J, IsVerticalDivisorAt (mCoordIdeal y) p (-a) f g ∧ MvPolynomial.aeval y g ≠ 0 ∧ MvPolynomial.aeval y f / MvPolynomial.aeval y g = e₀ := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.VertForm.exists_vertical
end

section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
open GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.GeoModel

theorem exists_patches_of_res (hRes : ResK.ResKStatement)
    (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (hp : IsProjOver s)
    (hn : Tor.IsNormalScheme P) (U : (pullback s (spMap (algebraMap (𝓞 F) F))).Opens) (hd : Dense (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))) (e : ℕ)
    (hU : SmoothOfRelativeDimension e (U.ι ≫ pullback.snd s (spMap (algebraMap (𝓞 F) F))))
    (Ab : Set P) (hAb : pullback.fst s (spMap (algebraMap (𝓞 F) F)) ⁻¹' Ab = U)
    (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P) (hξ₀ : IsCptGen ξ₀) :
    ∃ (N : ℕ) (x : Fin (N + 1) → Ω) (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (f : X ⟶ P),
      (∀ q : X, genPt ξ ⤳ q) ∧ CoordTie ℤ ξ x ∧ ξ ≫ f = ξ₀ ∧
      SncPts ξ e {p | Char0 ξ p ∧ f p.1 ∉ Ab} := by
  obtain ⟨hred, hln, M, i, hi, his⟩ := GlobalTheory.T.generic_fibre_projective_embedding F P s hp hn
  obtain ⟨b, ξF, hF1, hF2, hFg⟩ := GlobalTheory.T.generic_point_generic_fibre F P s Ω ξ₀ hξ₀
  have hmem := GlobalTheory.T.generic_point_mem_dense_open _ Ω ξF U hFg hd
  have hin : ResK.IsResInput M i U e := ⟨hi, hred, hd, by rw [his]; exact hU⟩
  obtain ⟨r, X', j, f', hj, hfj, hsm, hiso, hdense, hsnc⟩ := hRes F M e _ i U hin
  letI algF : Algebra F Ω := b.toAlgebra
  letI algO : Algebra (𝓞 F) Ω := (b.comp (algebraMap (𝓞 F) F)).toAlgebra
  haveI : IsScalarTower (𝓞 F) F Ω := .of_algebraMap_eq' rfl
  have hs0 : ξ₀ ≫ s = spMap (algebraMap (𝓞 F) Ω) := by
    rw [← hF1, Category.assoc, pullback.condition, ← Category.assoc, hF2]
    show _ = Spec.map (CommRingCat.ofHom (b.comp (algebraMap (𝓞 F) F)))
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨nu, u, hu⟩ := GlobalTheory.T.projective_over_coords_exist (𝓞 F) P s hp Ω ξ₀ hξ₀ hs0
  have hproj : IsProjOver (f' ≫ i ≫ PSpace.str F M) := by
    have := GlobalTheory.T.closed_in_product_projective F M r X' j hj
    rwa [← Category.assoc, ← hfj, Category.assoc] at this
  have hdom := GlobalTheory.T.smooth_scheme_stalks_domains F e X' _ hsm
  obtain ⟨ξ', h1, hξ'⟩ := GlobalTheory.T.generic_point_lift_along_iso _ X' f' U Ω ξF hiso hmem hFg hdom
  have hξs : ξ' ≫ f' ≫ i ≫ PSpace.str F M = spMap (algebraMap F Ω) := by
    rw [← Category.assoc, h1, his, hF2]
  obtain ⟨nx, x2, hx2⟩ := GlobalTheory.T.projective_over_coords_exist F X' _ hproj Ω ξ' hξ' hξs
  have hg : ξ' ≫ (f' ≫ pullback.fst _ _) = ξ₀ := by rw [← Category.assoc, h1, hF1]
  have hbase := GlobalTheory.T.every_component_in_some_chart X' P Ω ξ' ξ₀ _ (𝓞 F) _ u hu hg
  obtain ⟨n, ht⟩ := GlobalTheory.T.coords_product_refinement X' Ω ξ' F _ _ x2 u hx2 hbase
  obtain ⟨c₀, hc₀, hfrac⟩ := GlobalTheory.T.coords_generate_function_field (𝓞 F) F Ω X' ξ' _ _ ht
  obtain ⟨X, ξ, sX, htX, hirr, -, -, -⟩ := GlobalTheory.T.exists_proper_integral_model Ω (𝓞 F) _ _ c₀ hc₀ hfrac
  have hreg : ∀ (a : 𝓞 F) (p : Cpt ξ), (RingHom.id Ω) (algebraMap (𝓞 F) Ω a) ∈ regAt ξ p := by
    intro a p
    obtain ⟨c, hc⟩ := htX.cover p
    exact (htX.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p hc
  have hchart : ∀ p : Cpt ξ, ∃ c, InChart ξ (fun k => (RingHom.id Ω) (u k)) c p := by
    intro p
    obtain ⟨⟨q1, q2, q3⟩, h0, hc⟩ := htX.cover p
    have hne := h0
    simp only [mul_ne_zero_iff] at hne
    refine ⟨q3, hne.2, fun c' => ?_⟩
    have := hc ⟨q1, q2, c'⟩
    have e1 : ((∏ a, x2 (q1 a)) * x2 q2 * u c') / ((∏ a, x2 (q1 a)) * x2 q2 * u q3) = u c' / u q3 := by
      field_simp [hne.1.1, hne.1.2, hne.2]
    simpa [e1] using this
  obtain ⟨f, hf, -⟩ := GlobalTheory.T.dominates_of_coords_regular P Ω ξ₀ (𝓞 F) _ u X Ω ξ (RingHom.id Ω) hu htX.gen hirr hreg hchart
  have hf' : ξ ≫ f = ξ₀ := by
    have : ξ ≫ f = _ := hf
    rw [this]; simp
  obtain ⟨N, x, hx⟩ := GlobalTheory.T.coord_over_int_of_finite_order X Ω ξ (𝓞 F) _ _ htX
  obtain ⟨R1, R2⟩ := GlobalTheory.T.coord_charts_match_regular (𝓞 F) F Ω X X' ξ ξ' _ _ htX ht
  have hchar := GlobalTheory.T.char_zero_iff_nonzero_units F Ω X ξ _ _ htX
  have hFreg : ∀ (a : F) (p' : Cpt ξ'), algebraMap F Ω a ∈ regAt ξ' p' := by
    intro a p'
    obtain ⟨c, hc⟩ := ht.cover p'
    exact (ht.ring c hc.1 _).1 (Subalgebra.algebraMap_mem _ a) p' hc
  have hunit : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → Char0 ξ p := by
    intro p p' h
    refine (hchar p).2 fun d hd0 => ?_
    have hd1 : (algebraMap (𝓞 F) F d) ≠ 0 := by simpa using hd0
    have e1 : algebraMap (𝓞 F) Ω d = algebraMap F Ω (algebraMap (𝓞 F) F d) := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [e1]; exact (map_ne_zero _).2 hd1
    · rw [h, e1]; exact hFreg _ p'
    · rw [h, e1, ← map_inv₀]; exact hFreg _ p'
  have hPts : Pts ξ = Set.range (regAt ξ') := by
    ext R
    constructor
    · rintro ⟨p, hp0, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', h.symm⟩
    · rintro ⟨p', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, hunit p p' h, h.symm⟩
  let B : Set (Cpt ξ) := {p | Char0 ξ p ∧ f p.1 ∉ Ab}
  let T : Set X' := f'.base ⁻¹' (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0})))ᶜ
  have hgen : ∀ (p : Cpt ξ) (p' : Cpt ξ'), regAt ξ p = regAt ξ' p' → (f p.1 ∉ Ab ↔ p'.1 ∈ T) := by
    intro p p' h
    have e1 : f p.1 = (f' ≫ pullback.fst _ _) p'.1 :=
      GlobalTheory.T.regular_rings_equal_images_equal P X X' Ω ξ₀ ξ ξ' f _ (𝓞 F) _ u hu htX.gen hξ' hf' hg p p' h
    have e2 : ((f' ≫ pullback.fst s (spMap (algebraMap (𝓞 F) F))) p'.1 ∈ Ab) ↔ f' p'.1 ∈ (U : Set ((pullback s (spMap (algebraMap (𝓞 F) F)) : Scheme.{0}))) := by
      rw [← hAb]; simp
    rw [e1, e2]; rfl
  have hBd : regAt ξ '' B = regAt ξ' '' {p | p.1 ∈ T} := by
    ext R
    constructor
    · rintro ⟨p, ⟨hp0, hp1⟩, rfl⟩
      obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
      exact ⟨p', (hgen p p' h).1 hp1, h.symm⟩
    · rintro ⟨p', hp', rfl⟩
      obtain ⟨p, h⟩ := R1 p'
      exact ⟨p, ⟨hunit p p' h, (hgen p p' h).2 hp'⟩, h⟩
  have hpatch := GlobalTheory.T.snc_patch_at_each_component F X' _ e T Ω ξ' hξ' hξs hsm hsnc (GlobalTheory.T.regular_ring_determines_component X' Ω ξ' F _ _ ht)
  refine ⟨N, x, X, ξ, f, hirr, hx, hf', fun p hp0 => ?_⟩
  obtain ⟨p', h⟩ := R2 p ((hchar p).1 hp0)
  show ∃ (A : Subalgebra ℚ Ω) (z : Fin e → A) (n : ℕ) (q : Ideal A),
    IsSncPatch (Pts ξ) (regAt ξ '' B) e A z n ∧ q.IsPrime ∧ IsLocAt A q (regAt ξ p)
  rw [hPts, hBd, h]
  exact hpatch p'

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem exists_cst {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {Ω : Type} [Field Ω] (y₀ : Sp Ω ⟶ Xo.XF c) :
    ∃ cst : c.F →+* Ω, y₀ ≫ Y.j ≫ Y.s = spMap (cst.comp (algebraMap (𝓞 c.F) c.F)) := by
  refine ⟨(Spec.preimage (y₀ ≫ pullback.snd _ _)).hom, ?_⟩
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc]
  unfold spMap
  rw [CommRingCat.ofHom_comp, Spec.map_comp, CommRingCat.ofHom_hom, Spec.map_preimage]

theorem exists_base (hRes : ResK.ResKStatement) (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H)
    (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Ω₀ : Type) [Field Ω₀]
    (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X) (hg : IsCptGen ξ₀) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k))
      (y : (Σ k, J k) → Ω) (M₁ : PModel ℤ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (f₁ : M₁.X ⟶ Y.X)
      (y₀ : Sp Ω ⟶ Xo.XF c) (i : Ω₀ →+* Ω), Nonempty K ∧ (letI := i.toAlgebra; FiniteDimensional Ω₀ Ω) ∧
      Flat.NormalCpt M₁.ξ ∧ M₁.ξ ≫ f₁ = y₀ ≫ Y.j ∧ M₁.ξ ≫ f₁ = spMap i ≫ ξ₀ ∧
      (∀ p ∈ S, FullTorsion Y.t.G (M₁.ξ ≫ f₁) (p ^ 4)) ∧ (∀ p ∈ S, ∃ ζ : Ω, IsPrimitiveRoot ζ (p ^ 4)) ∧
      SncPts M₁.ξ D.dim {p | Char0 M₁.ξ p ∧ p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} ∧
      Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
  haveI : FiniteDimensional ℚ c.F := c.fin
  haveI : NumberField c.F := {}
  have hgen₀ := GlobalTheory.T.component_generic_is_generic_point E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨w₀, -⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω₀ ξ₀ hgen₀
  obtain ⟨cst, -⟩ := exists_cst (Y := Y) w₀
  haveI : CharZero Ω₀ := charZero_of_injective_ringHom cst.injective
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y Ω₀ ξ₀ S hgen₀ hS
  obtain ⟨K₀, _, J₀, _, yc, X₀, ξ', f₀, bd₀, -, hall₀, htie₀, hf₀, -, -⟩ := GlobalTheory.T.exists_coords_of_generic_point hRes E H D l Xo c Y Ω₀ ξ₀ hg
  obtain ⟨K₁, _, J₁, _, y₁, bk, bx, M, h, -, -, hdom, hnorm, hsm⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes K₀ J₀ Ω₀ Ω i yc X₀ ξ' hfin hall₀ htie₀
  have hMξ : M.ξ ≫ h ≫ f₀ = spMap i ≫ ξ₀ := by
    have e : M.ξ ≫ h = Spec.map (CommRingCat.ofHom i) ≫ ξ' := hdom
    rw [← Category.assoc, e, Category.assoc, hf₀]
  have hgenM : genPt (M.ξ ≫ h ≫ f₀) ∈ genericPoints Y.X := by
    rw [hMξ]
    show genPt (Spec.map (CommRingCat.ofHom i) ≫ ξ₀) ∈ _
    rw [genPt_comp]
    exact hgen₀
  obtain ⟨y₀, hy₀⟩ := GlobalTheory.T.generic_point_factors_open E H D l Xo c Y Ω _ hgenM
  have hinj : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hA := GlobalTheory.T.generic_trdeg_eq_dimension E H D l Xo c _ _ Y Ω₀ ξ₀ Ω y₀ i hinj hg (hy₀ ▸ hMξ)
  have htr : Algebra.trdeg ℤ Ω = ((D.dim : ℕ) : Cardinal) := by
    letI : Algebra Ω₀ Ω := i.toAlgebra
    haveI : FiniteDimensional Ω₀ Ω := hfin
    haveI : FaithfulSMul ℤ Ω₀ := (faithfulSMul_iff_algebraMap_injective ℤ Ω₀).mpr Int.cast_injective
    haveI : FaithfulSMul Ω₀ Ω := (faithfulSMul_iff_algebraMap_injective Ω₀ Ω).mpr i.injective
    have htow := trdeg_add_eq ℤ Ω₀ (A := Ω)
    rw [hA, trdeg_eq_zero_iff.2 (Algebra.IsAlgebraic.of_finite Ω₀ Ω), add_zero] at htow
    exact htow.symm
  obtain ⟨U, hd, hAb⟩ := GlobalTheory.T.dense_open_generic_fibre E H D l Xo c Y Ω _ _ M (h ≫ f₀) y₀ hy₀
  have hU := GlobalTheory.T.generic_fibre_open_coords E H D l Xo c Y Ω K₁ J₁ y₁ M (h ≫ f₀) y₀ U hy₀ hsm htr
  have hnm : Tor.IsNormalScheme M.X := ((GlobalTheory.T.normal_cpt_iff_normal_scheme _ Ω M.ξ M.tie.gen M.all).2).1 hnorm
  obtain ⟨N, x, X, ξ, f₂, hall, htie, hf₂, hp⟩ := exists_patches_of_res hRes c.F M.X ((h ≫ f₀) ≫ Y.s)
    (GlobalTheory.T.projective_model_over_base E H D l Xo c Y Ω _ _ M (h ≫ f₀)) hnm U hd D.dim hU _ hAb Ω M.ξ M.tie.gen
  obtain ⟨K, _, J, _, y, M₁, g, hne, hdom₁, hn₁, hp₁⟩ := GlobalTheory.T.exists_projective_coord_model Ω X ξ N x D.dim
    (f₂ ⁻¹' ((h ≫ f₀) ⁻¹' abLocus Y.t.G)) hall htie hp
  have hg₁ : M₁.ξ ≫ g = ξ := by
    have e : M₁.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ := hdom₁
    rw [e]; simp
  have hξ₁ : M₁.ξ ≫ g ≫ f₂ ≫ h ≫ f₀ = M.ξ ≫ h ≫ f₀ := by
    rw [← Category.assoc, hg₁, ← Category.assoc, hf₂]
  refine ⟨Ω, inferInstance, inferInstance, K, inferInstance, J, inferInstance, y, M₁, g ≫ f₂ ≫ h ≫ f₀, y₀, i, hne, hfin, hn₁,
    hξ₁.trans hy₀, hξ₁.trans hMξ, fun p hp' => ?_, hroot, ?_, htr⟩
  · rw [hξ₁, hMξ]
    exact htors p hp'
  · convert hp₁ using 4
    simp

section Shrink

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
  {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S : Finset ℕ}
  {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}

theorem ht_isVBOn (A : HodgeCpt Y S y) (hβ : Function.Injective β) {p : ℕ} (hp : p ∈ S) (s : CMType H ⊕ CMType H) :
    (A.HT p s).IsVBOn {q | ∀ r : ℕ, r.Prime → r ≠ p → ¬ InFibre A.ξ r q} (labelRk D s) (A.Vgen s) := by
  intro q _
  obtain ⟨U, hU, b, hb, hfr⟩ := A.vb s q trivial
  refine ⟨U, hU, b, hb, fun q' hq' hU' => ?_⟩
  have h := hfr q' trivial hU'
  have hV : A.V s q' = A.HT p s q' := by
    by_cases hf : InFibre A.ξ p q'
    · refine Lat.patch_of_unique S _ _ hp hf fun p' hp' h' => ?_
      by_contra hne
      exact hq' p' (A.S_prime p' hp') hne h'
    · have hc : ∀ r : ℕ, r.Prime → ¬ InFibre A.ξ r q' := fun r hr => by
        by_cases e : r = p
        · rw [e]; exact hf
        · exact hq' r hr e
      obtain ⟨h1, h2, -⟩ := GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y S Ω K J y A hβ q' hc
      rw [h1 s, h2 p (A.S_prime p hp) s]
  exact ⟨h.1, hV ▸ h.2⟩

theorem unitAt_nat {X : Scheme.{0}} {ξ : Sp Ω ⟶ X} [CharZero Ω] (q : Cpt ξ) (n : ℕ) (hn : n ≠ 0)
    (h : ∀ r : ℕ, r.Prime → r ∣ n → ¬ InFibre ξ r q) : unitAt ξ q (n : Ω) := by
  induction n using Nat.recOnMul with
  | zero => exact absurd rfl hn
  | one =>
    rw [Nat.cast_one]
    exact ⟨one_ne_zero, (regAt ξ q).one_mem, by simpa using (regAt ξ q).one_mem⟩
  | prime r hr =>
    have := h r hr dvd_rfl
    exact not_not.1 this
  | mul a b ha hb =>
    have ha0 : a ≠ 0 := left_ne_zero_of_mul hn
    have hb0 : b ≠ 0 := right_ne_zero_of_mul hn
    have h1 := ha ha0 fun r hr hd => h r hr (hd.mul_right b)
    have h2 := hb hb0 fun r hr hd => h r hr (hd.mul_left a)
    rw [Nat.cast_mul]
    refine ⟨mul_ne_zero h1.1 h2.1, mul_mem h1.2.1 h2.2.1, ?_⟩
    rw [mul_inv]
    exact mul_mem h1.2.2 h2.2.2

end Shrink

theorem vb_shrink {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) (s : CMType H ⊕ CMType H) :
    (Lat.patch S₀ (A.M.eigLat A.ρ (A.cst.comp (labelEmb c s)))
      fun p => htLabel A.M A.t.PP.L (p ^ A.R p) A.ρ (fun s' => A.cst.comp (labelEmb c s')) s).IsVB (labelRk D s)
      (eigSp A.ρ (A.cst.comp (labelEmb c s))) := by
  classical
  obtain ⟨-, -, hchar, hemb, hrank, -, -, hreg⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l Xo c O β Y _ Ω K J y A hβ
  haveI := hchar
  haveI : Fintype (CMType H ⊕ CMType H) := Fintype.ofFinite _
  haveI : IsNoetherian A.X := ((GlobalTheory.T.regAt_noetherian_model_noetherian _ Ω A.ξ ℤ _ _ A.tie).2 A.all).1
  have hS₀ : ∀ p ∈ S₀, p.Prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  obtain ⟨-, hcard⟩ := GlobalTheory.T.label_embedding_injective E H l c
  have hlat := (GlobalTheory.T.lie_omega_lattice_vector_bundle A.X Ω A.ξ A.t.G A.Li A.M A.tie.gen A.t.semi.smooth).1
  have hsplit := GlobalTheory.T.lattice_eigen_vector_bundle A.X Ω A.ξ A.Li E A.ρ A.M.lat {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} _ (CMType H ⊕ CMType H)
    A.emb A.tie.gen hemb (by rw [← hcard, Nat.card_eq_fintype_card])
    (fun p _ => (hlat p trivial) |> fun ⟨U, hU, b, hb, hf⟩ => ⟨U, hU, b, hb, fun q _ hq => hf q trivial hq⟩)
    (fun p _ a e he => GlobalTheory.CompanionTheory.Ar.LieStable.lat_stable _ Ω A.ξ _ _ A.M _ A.t.act A.ρ A.act p a e he)
    (fun p _ s a => hreg s a p)
    (fun p hp => by
      have h := unitAt_nat p (NumberField.discr E).natAbs (Int.natAbs_ne_zero.2 (NumberField.discr_ne_zero E))
        fun r hr hdv => hp r (hd r hr (Int.natCast_dvd.2 hdv))
      rcases Int.natAbs_eq (NumberField.discr E) with e | e
      · rw [e]; simpa using h
      · rw [e]
        refine ⟨by simpa using h.1, by simpa using neg_mem h.2.1, ?_⟩
        simpa using neg_mem h.2.2)
  have h₀ : (A.dR s).IsVBOn {q | ∀ l ∈ S₀, ¬ InFibre A.ξ l q} (labelRk D s) (A.Vgen s) := by
    have := hsplit.1 s
    rw [show Module.finrank Ω (eigSp A.ρ (A.emb s)) = labelRk D s from hrank s] at this
    exact this
  obtain ⟨L, hL, hoff, hon⟩ := GlobalTheory.T.lattice_glue_over_primes A.X Ω A.ξ A.Li S₀ (A.dR s) (fun p => A.HT p s) (labelRk D s) (A.Vgen s)
    A.tie.gen hS₀ h₀ (fun p hp => ht_isVBOn A hβ (Finset.mem_union_left _ hp) s)
    (fun p hp q hq => ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l Xo c O β Y _ Ω K J y A hβ q hq).2.1 p (hS₀ p hp) s))
  have he : Lat.patch S₀ (A.dR s) (fun p => A.HT p s) = L := by
    funext q
    by_cases hq : ∃ p ∈ S₀, InFibre A.ξ p q
    · obtain ⟨p, hp, hf⟩ := hq
      rw [hon p hp q hf]
      exact Lat.patch_of_unique S₀ _ _ hp hf fun p' hp' h' => inFibre_unique (hS₀ p hp) (hS₀ p' hp') hf h'
    · push_neg at hq
      rw [hoff q hq]
      exact Lat.patch_of_not S₀ _ _ hq
  show (Lat.patch S₀ (A.dR s) (fun p => A.HT p s)).IsVB (labelRk D s) (A.Vgen s)
  rw [he]
  exact hL

def toS₀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Tor.Level H}
    {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {S₀ S₁ : Finset ℕ}
    {Ω : Type} [Field Ω] {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω}
    (A : HodgeCpt Y (S₀ ∪ S₁) y) (hβ : Function.Injective β)
    (hd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) {Ω₀ : Type} [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X)
    (h₀ : IsCptGen ξ₀) (i : Ω₀ →+* Ω) (hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i) {K' : Type} [Fintype K'] {J' : K' → Type}
    [∀ k, Fintype (J' k)] (y' : (Σ k, J' k) → Ω)
    (tie' : CoordTie ℤ A.ξ fun c' : (k : K') → J' k => ∏ k, y' ⟨k, c' k⟩) : HodgeCpt Y S₀ y' where
  X := A.X
  ξ := A.ξ
  all := A.all
  tie := tie'
  normal := A.normal
  f := A.f
  Ω₀ := Ω₀
  ξ₀ := ξ₀
  gen₀ := h₀
  cst := A.cst
  cst_over := A.cst_over
  fn := i
  fn_over := hi
  t := A.t
  m := A.m
  Li := A.Li
  M := A.M
  ρ := A.ρ
  act := A.act
  S_prime := fun p hp => A.S_prime p (Finset.mem_union_left _ hp)
  R := A.R
  R_ge := fun p hp => A.R_ge p (Finset.mem_union_left _ hp)
  tors := fun p hp => A.tors p (Finset.mem_union_left _ hp)
  vb := vb_shrink A hβ hd

theorem unitAt_div_of_span {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {q : Cpt ξ} {t m : Ω}
    (h : Submodule.span (regAt ξ q) {t} = Submodule.span (regAt ξ q) {m}) (hm : m ≠ 0) : unitAt ξ q (t / m) := by
  have h1 : t ∈ Submodule.span (regAt ξ q) {m} := h ▸ Submodule.mem_span_singleton_self t
  have h2 : m ∈ Submodule.span (regAt ξ q) {t} := h ▸ Submodule.mem_span_singleton_self m
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 h1
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 h2
  rw [Subring.smul_def, smul_eq_mul] at ha hb
  have ht : t ≠ 0 := by
    rintro rfl
    exact hm (by simpa using hb.symm)
  refine ⟨div_ne_zero ht hm, ?_, ?_⟩
  · rw [← ha, mul_div_assoc, div_self hm, _root_.mul_one]
    exact a.2
  · rw [inv_div, ← hb, mul_div_assoc, div_self ht, _root_.mul_one]
    exact b.2

theorem exists_geo : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → ∀ (Ω₀ : Type) [Field Ω₀] (ξ₀ : Spec (CommRingCat.of Ω₀) ⟶ Y.X), IsCptGen ξ₀ → ∀ (S₀ S₁ : Finset ℕ) (sm : CMType H → CMType H ⊕ CMType H) (r : ℕ), (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, labelRk D (sm τ) = r) → (∀ p ∈ S₀, p.Prime) → (∀ p ∈ S₁, p.Prime) → Disjoint S₁ S₀ → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀) → ∃ (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S₀ y) (deg : ℕ) (bd : Ideal (MRing J)) (vdeg : ℕ → K → ℤ) (vnum vden : ℕ → MRing J) (s : CMType H → Fin r → 𝔐.Li) (aMu : K → ℤ) (e₀ : Ω), Nonempty K ∧ genPt 𝔐.ξ₀ = genPt ξ₀ ∧ 𝔐.IsCover deg ∧ 𝔐.OmVB ∧ (∀ p ∈ S₀ ∪ S₁, HT.HTFree 𝔐 p) ∧ Algebra.trdeg ℤ Ω = D.dim ∧ Cmp.IsSncModel y D.dim bd ∧ (∀ (z : Spec (CommRingCat.of ℂ) ⟶ 𝔐.X) w, CoordsAt 𝔐.ξ y z w → (w ∈ mcPts bd ↔ ¬ 𝔐.Interior z)) ∧ (∀ p ∈ S₁, 4 ≤ 𝔐.R p) ∧ (∀ p ∈ S₁, FullTorsion 𝔐.t.G 𝔐.ξ (p ^ 𝔐.R p)) ∧ (∀ p ∈ S₁, ∀ s', (𝔐.HT p s').IsVBOn {q | ∀ r' : ℕ, r'.Prime → r' ≠ p → ¬ InFibre 𝔐.ξ r' q} (labelRk D s') (𝔐.Vgen s')) ∧ (∀ p ∈ S₁, IsVerticalDivisorAt (mCoordIdeal y) p (vdeg p) (vnum p) (vden p)) ∧ (∀ p ∈ S₁, ∀ q : Cpt 𝔐.ξ, InFibre 𝔐.ξ p q → ∀ ch, InChart 𝔐.ξ (segreCoord y) ch q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → 𝔐.Li) (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω), (∀ τ, (𝔐.V (sm τ)).IsFrameAt (b τ) q) → (∀ τ, (𝔐.HT p (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') → unitAt 𝔐.ξ q ((∏ τ, (T τ).det) / (MvPolynomial.aeval y (vnum p) / MvPolynomial.aeval y (vden p) * chartMono y ch (-vdeg p)))) ∧ (∀ τ, LinearIndependent Ω (s τ)) ∧ (∀ τ, Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) ∧ (Lat.tens (fun τ => Cusp.detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y aMu e₀ := by
  intro hG hW E _ _ _ H D Xo l c Y hgl hp hq Ω₀ _ ξ₀ hξ₀ S₀ S₁ sm r hsm hrk hS₀ hS₁ hdis hdisc
  classical
  have hRes : ResK.ResKStatement := hG.2.2.2.2.1
  have hS : ∀ p ∈ S₀ ∪ S₁, p.Prime := fun p hp' => by
    rcases Finset.mem_union.1 hp' with h | h
    · exact hS₀ p h
    · exact hS₁ p h
  have hSd : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S₀ ∪ S₁ := fun p h1 h2 =>
    Finset.mem_union_left _ (hdisc p h1 h2)
  obtain ⟨Ω, _, _, K₁, _, J₁, _, y₁, M₁, f₁, z₀, i, ⟨k₁⟩, hfin, hN, hz₀, hdomi, htors, hroot, hsnc₁, htr⟩ :=
    exists_base hRes E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀ (S₀ ∪ S₁) hS
  have hgen₁ : f₁ (genPt M₁.ξ) ∈ genericPoints Y.X := by
    have e : genPt (M₁.ξ ≫ f₁) = genPt ξ₀ := by
      rw [hdomi]; exact genPt_comp i ξ₀
    have h0 := GlobalTheory.T.component_generic_is_generic_point E H D l (Xo l) c Y Ω₀ ξ₀ hξ₀
    rw [← e] at h0
    exact h0
  obtain ⟨K₂, _, J₂, _, y₂, bk, bx, A, g, hbk, hy₂, hdom₂, hf₂, hR₂, hfree, hiso⟩ :=
    GlobalTheory.T.hodge_cpt_projective_model hW E H D l (Xo l) c Y (S₀ ∪ S₁) (fun _ => 4) Ω K₁ J₁ y₁ M₁ f₁ z₀ hN hz₀ hgen₁ hS hSd
      (fun _ _ => le_rfl) htors hroot
  have hgA : A.ξ ≫ g = M₁.ξ := by
    have e : A.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have hsncA : SncPts A.ξ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} :=
    GlobalTheory.T.snc_points_transfer_dominating Ω _ _ _ _ M₁.X A.X M₁.ξ A.ξ g D.dim _ M₁.all A.all M₁.tie A.tie hdom₂ hiso hsnc₁
  have hi : GlobalTheory.CompanionTheory.Ar.Dominates A.ξ ξ₀ A.f i := by
    show A.ξ ≫ A.f = _
    rw [hf₂, ← Category.assoc, hgA]
    exact hdomi
  obtain ⟨-, -, hchar, -, hrank, -, -, -⟩ := GlobalTheory.T.hodge_cpt_interior_generic E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ
  have hVB : ∀ s', (Lat.patch S₀ (A.dR s') fun p => A.HT p s').IsVB (labelRk D s') (A.Vgen s') :=
    vb_shrink A hβ hdisc
  have hs : ∀ τ, ∃ b : Fin r → A.Li, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = A.Vgen (sm τ) := by
    intro τ
    have hfr : Module.finrank Ω (A.Vgen (sm τ)) = r := (hrank _).trans (hrk τ)
    have hr : 0 < r := by
      rw [← hrk τ]
      rcases hsm with e | e <;> rw [e] <;> simp only [labelRk, Sum.elim_inl, Sum.elim_inr] <;> omega
    haveI : Module.Finite Ω (A.Vgen (sm τ)) := Module.finite_of_finrank_pos (by omega)
    let bs := Module.finBasisOfFinrankEq Ω (A.Vgen (sm τ)) hfr
    refine ⟨fun k => (bs k : A.Li), ?_, ?_⟩
    · exact bs.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _)
    · have h := congrArg (Submodule.map (A.Vgen (sm τ)).subtype) bs.span_eq
      rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at h
      exact h
  choose s hsl hss using hs
  have hdel : ∀ P : S₁, ∃ Δ : Lat A.ξ Ω, Δ.IsVB 1 ⊤ ∧ (∀ q, ¬ InFibre A.ξ P q → Δ q = Submodule.span (regAt A.ξ q) {1}) ∧
      ∀ q, InFibre A.ξ P q → ∀ (b b' : ∀ τ, Fin (labelRk D (sm τ)) → A.Li)
        (T : ∀ τ, Matrix (Fin (labelRk D (sm τ))) (Fin (labelRk D (sm τ))) Ω),
        (∀ τ, (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)).IsFrameAt (b τ) q) →
        (∀ τ, (A.HT P (sm τ)).IsFrameAt (b' τ) q) → (∀ τ k, b' τ k = ∑ k', T τ k' k • b τ k') →
        Δ q = Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} := fun P =>
    GlobalTheory.T.lattice_frames_away_prime A.X Ω A.ξ _ _ A.Li (CMType H) (fun τ => labelRk D (sm τ)) (fun τ => A.Vgen (sm τ))
      (fun τ => Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (fun τ => A.HT P (sm τ)) P A.tie A.all (hS₁ P P.2)
      (fun τ => hVB _) (fun τ => ht_isVBOn A hβ (Finset.mem_union_right _ P.2) _)
      (fun τ q hq => by
        have hB := GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ (toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₂ A.tie) hβ q hq
        exact ((GlobalTheory.T.hodge_cpt_away_from_primes E H D l (Xo l) c _ _ Y _ Ω K₂ J₂ y₂ A hβ q hq).2.1 P (hS₁ P P.2) (sm τ)).trans
          (hB.1 (sm τ)).symm)
  choose Δ hΔv hΔ1 hΔf using hdel
  let lmu : Lat A.ξ Ω := Lat.tens (fun τ => Cusp.detLat (Lat.patch S₀ (A.dR (sm τ)) fun p => A.HT p (sm τ)) (s τ)) fun _ => -1
  have hmu : lmu.IsVB 1 ⊤ := (GlobalTheory.T.lattice_tensor_power_line_bundle A.X Ω A.ξ _ _ Set.univ (fun τ => GlobalTheory.T.det_lattice_line_bundle A.X Ω A.ξ A.Li _ r (A.Vgen (sm τ)) (s τ)
    (hsl τ) (hss τ) (hrk τ ▸ hVB (sm τ))) _).1
  let Λ : Option S₁ → Lat A.ξ Ω := fun o => o.elim lmu Δ
  have hΛ : ∀ o, (Λ o).IsVB 1 ⊤ := by
    rintro (_ | P)
    · exact hmu
    · exact hΔv P
  obtain ⟨K₃, _, J₃, _, y₃, κ, v, hκ, hv, tie₃, hdeg⟩ := GlobalTheory.T.exists_block_refinement_lines A.X Ω A.ξ K₂ J₂ y₂ (Option S₁) Λ A.tie hΛ
  choose a e hde using hdeg
  have hver : ∀ P : S₁, ∃ f g : MRing J₃, IsVerticalDivisorAt (mCoordIdeal y₃) P (-(a (some P))) f g ∧
      MvPolynomial.aeval y₃ g ≠ 0 ∧ MvPolynomial.aeval y₃ f / MvPolynomial.aeval y₃ g = e (some P) := fun P =>
    GlobalTheory.T.vertical_divisor_degree A.X Ω A.ξ K₃ J₃ y₃ P (Δ P) (a (some P)) (e (some P)) tie₃ A.all (hde (some P)) (hΔ1 P)
  choose fv gv hvd hgv hfg using hver
  obtain ⟨bd, hbd, hbd'⟩ := GlobalTheory.T.snc_model_boundary_coords Ω A.X A.ξ K₃ J₃ y₃ D.dim {p | Char0 A.ξ p ∧ g p.1 ∉ f₁ ⁻¹' abLocus Y.t.G} tie₃
    (fun p hp' => hp'.1) hsncA
  have hab : abLocus A.t.G = A.f ⁻¹' abLocus Y.t.G :=
    (Set.ext fun x => abLocus_pullback abLocusOne Y.t.semi A.m.cart.1 x).symm
  letI algi : Algebra Ω₀ Ω := i.toAlgebra
  haveI : FiniteDimensional Ω₀ Ω := hfin
  refine ⟨K₃, inferInstance, J₃, inferInstance, Ω, inferInstance, inferInstance, y₃, toS₀ A hβ hdisc ξ₀ hξ₀ i hi y₃ tie₃,
    Module.finrank Ω₀ Ω, bd, fun p => if h : p ∈ S₁ then -(a (some ⟨p, h⟩)) else 0,
    fun p => if h : p ∈ S₁ then fv ⟨p, h⟩ else 0, fun p => if h : p ∈ S₁ then gv ⟨p, h⟩ else 0, s, a none, e none,
    ⟨κ (bk k₁)⟩, rfl, ⟨Module.finrank_pos, rfl⟩, fun p hp' => hfree p (Finset.mem_union_left _ hp'), hfree, htr, hbd, ?_, ?_, ?_, ?_,
    ?_, ?_, hsl, hss, hde none⟩
  · intro z w hw
    rw [hbd' z w hw]
    constructor
    · rintro ⟨h, -, h2⟩ hI
      have h3 : centre z ∈ abLocus A.t.G := hI
      rw [hab, hf₂] at h3
      exact h2 h3
    · intro hn
      refine ⟨A.all _, GlobalTheory.T.char_zero_centre_of_complex Ω A.X A.ξ z _ A.tie.gen, fun h => hn ?_⟩
      show centre z ∈ abLocus A.t.G
      rw [hab, hf₂]
      exact h
  · intro p hp'
    show 4 ≤ A.R p
    rw [hR₂]
  · intro p hp'
    exact A.tors p (Finset.mem_union_right _ hp')
  · intro p hp' s'
    exact ht_isVBOn A hβ (Finset.mem_union_right _ hp') s'
  · intro p hp'
    simp only [dif_pos hp']
    exact hvd ⟨p, hp'⟩
  · intro p hp' q hf ch hch b b' T hb hb' hT
    simp only [dif_pos hp']
    have h1 := hΔf ⟨p, hp'⟩ q hf b b' T hb hb' hT
    have h2 := (hde (some ⟨p, hp'⟩)).2 q trivial ch hch
    have he0 : e (some ⟨p, hp'⟩) ≠ 0 := (hde (some ⟨p, hp'⟩)).1
    have hne : ∀ k, y₃ ⟨k, ch k⟩ ≠ 0 := fun k => Finset.prod_ne_zero_iff.1 hch.1 k (Finset.mem_univ k)
    have hm : e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩)) ≠ 0 :=
      mul_ne_zero he0 (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k))
    have h3 : Submodule.span (regAt A.ξ q) {∏ τ, (T τ).det} = Submodule.span (regAt A.ξ q)
        {e (some ⟨p, hp'⟩) * GroundTheory.Heights₂.Heights.LowerBoundFree.chartMono y₃ ch (a (some ⟨p, hp'⟩))} := by
      rw [← h1]
      refine Eq.trans h2 ?_
      rw [smul_eq_mul, mul_comm]
      rfl
    rw [neg_neg, hfg ⟨p, hp'⟩]
    exact unitAt_div_of_span h3 hm

end GlobalTheory.CompanionTheory.Ar.GeoModel
end
end
