import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IdealSheafFlatDescent
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionKrullDim
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.DisjointUnionOfOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.StrictTransformClosedImmersion

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace MaxContactReduction

namespace FiniteOpenCoverWithIdeals

variable {T : MarkedIdealWithBoundary.{u}}

abbrev piece (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : Scheme.{u} := (D.opens i).toScheme

abbrev summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.piece i ⟶ D.disjointUnion :=
  Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i

theorem isOpenImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) := by
  show IsOpenImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsOpenImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsOpenImmersion (D.summandι i) :=
  isOpenImmersion_summandι D i

theorem isClosedImmersion_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) := by
  show IsClosedImmersion (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instIsClosedImmersionSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    IsClosedImmersion (D.summandι i) :=
  isClosedImmersion_summandι D i

theorem quasiCompact_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) := by
  show QuasiCompact (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i)
  infer_instance

instance instQuasiCompactSummandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    QuasiCompact (D.summandι i) :=
  quasiCompact_summandι D i

theorem summandι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.summandι i ≫ D.disjointUnionMap = (D.opens i).ι :=
  sigma_ι_sigmaOpensDesc T.scheme D.opens i

theorem disjointUnionMap_summandι_mem (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (y : D.piece i) :
    D.disjointUnionMap.base ((D.summandι i).base y) ∈ D.opens i := by
  have hmem : D.disjointUnionMap.base ((D.summandι i).base y) ∈ Set.range (D.opens i).ι.base := by
    rw [← summandι_comp_disjointUnionMap D i]
    exact ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι] at hmem
  exact hmem

private theorem comap_imageIdealSheaf_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (imageIdealSheaf (D.summandι i) (D.localIdeal i)).comap (D.summandι i) = D.localIdeal i :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp (D.localIdeal i) (D.summandι i)

private theorem imageIdealSheaf_eq_ker {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    (I : X.IdealSheafData) : imageIdealSheaf f I = Scheme.Hom.ker (I.subschemeι ≫ f) := rfl

private theorem subsingleton_sections_bot (Z : Scheme.{u}) :
    Subsingleton ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) := by
  have ht : CategoryTheory.Limits.IsTerminal (Z.presheaf.obj (Opposite.op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty Z.sheaf
  refine ⟨fun a b => ?_⟩
  have h := ht.hom_ext
    (CommRingCat.ofHom (RingHom.fst ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
    (CommRingCat.ofHom (RingHom.snd ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))
      ↥(Z.presheaf.obj (Opposite.op (⊥ : Z.Opens)))))
  exact congrArg (fun m => (CommRingCat.Hom.hom m) (a, b)) h

private theorem ideal_ker_eq_top_of_disjoint {Y Z : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g]
    (U : Y.affineOpens) (hdisj : ∀ z : ↥Z, g.base z ∉ (U.1 : Set ↥Y)) :
    (Scheme.Hom.ker g).ideal U = ⊤ := by
  have hempty : g ⁻¹ᵁ U.1 = ⊥ := by
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_bot]
    exact Set.eq_empty_iff_forall_notMem.mpr fun z hz => hdisj z hz
  have hsub : Subsingleton ↥(Z.presheaf.obj (Opposite.op (g ⁻¹ᵁ U.1))) := by
    rw [hempty]
    exact subsingleton_sections_bot Z
  rw [Scheme.Hom.ker_apply]
  refine (Ideal.eq_top_iff_one _).mpr ?_
  rw [RingHom.mem_ker, map_one]
  exact Subsingleton.elim _ _

private theorem ideal_imageIdealSheaf_eq_top_of_ne (D : FiniteOpenCoverWithIdeals T) {i j : D.idx} (hij : j ≠ i)
    (W : D.disjointUnion.Opens) (hW : IsAffineOpen W)
    (hsub : ∀ y ∈ (W : Set ↥D.disjointUnion), y ∈ Set.range (D.summandι i).base) :
    (imageIdealSheaf (D.summandι j) (D.localIdeal j)).ideal ⟨W, hW⟩ = ⊤ := by
  rw [imageIdealSheaf_eq_ker]
  refine ideal_ker_eq_top_of_disjoint ((D.localIdeal j).subschemeι ≫ D.summandι j) ⟨W, hW⟩ ?_
  intro z hz
  obtain ⟨v, hv⟩ := hsub _ hz
  have hcomp : ((D.localIdeal j).subschemeι ≫ D.summandι j).base z
      = (D.summandι j).base ((D.localIdeal j).subschemeι.base z) := rfl
  exact Blowup.sigmaι_base_ne (fun t : D.idx => (D.opens t).toScheme) hij
    ((D.localIdeal j).subschemeι.base z) v (hcomp.symm.trans hv.symm)

theorem comap_iInfImageIdeal_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.iInfImageIdeal.comap (D.summandι i) = D.localIdeal i := by
  have hglue : D.iInfImageIdeal
      = ⨅ j : D.idx, imageIdealSheaf (D.summandι j) (D.localIdeal j) := rfl
  refine le_antisymm ?_ ?_
  · rw [hglue]
    exact le_trans (Scheme.IdealSheafData.comap_mono (D.summandι i) (iInf_le _ i))
      (le_of_eq (comap_imageIdealSheaf_summandι D i))
  · rw [Scheme.IdealSheafData.le_def]
    intro V
    have hW : IsAffineOpen ((D.summandι i) ''ᵁ V.1) :=
      V.2.image_of_isOpenImmersion (D.summandι i)
    have hle : V.1 ≤ (D.summandι i) ⁻¹ᵁ ((D.summandι i) ''ᵁ V.1) := fun x hx => ⟨x, hx, rfl⟩
    have hsub : ∀ y ∈ ((((D.summandι i) ''ᵁ V.1) : D.disjointUnion.Opens) : Set ↥D.disjointUnion),
        y ∈ Set.range (D.summandι i).base := by
      rintro y ⟨v, hv, rfl⟩
      exact ⟨v, rfl⟩
    have h1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE D.iInfImageIdeal (D.summandι i)
      ⟨_, hW⟩ V hle
    have h2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE
      (imageIdealSheaf (D.summandι i) (D.localIdeal i)) (D.summandι i) ⟨_, hW⟩ V hle
    have h3 : D.iInfImageIdeal.ideal ⟨_, hW⟩
        = (imageIdealSheaf (D.summandι i) (D.localIdeal i)).ideal ⟨_, hW⟩ := by
      rw [hglue]
      simp only [Scheme.IdealSheafData.ideal_iInf, iInf_apply]
      refine le_antisymm (iInf_le _ i) (le_iInf fun j => ?_)
      by_cases hj : j = i
      · rw [hj]
      · rw [ideal_imageIdealSheaf_eq_top_of_ne D hj _ hW hsub]
        exact le_top
    have h4 : (D.iInfImageIdeal.comap (D.summandι i)).ideal V = (D.localIdeal i).ideal V := by
      rw [h1, h3, ← h2, comap_imageIdealSheaf_summandι D i]
    exact le_of_eq h4.symm

abbrev summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) : D.disjointUnion.Opens :=
  (D.summandι i).opensRange

theorem range_summandι (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    Set.range (D.summandι i).base = Set.range (D.summandOpen i).ι.base :=
  (Scheme.Opens.range_ι (D.summandOpen i)).symm

abbrev summandIso (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    D.piece i ≅ (D.summandOpen i).toScheme :=
  IsOpenImmersion.isoOfRangeEq (D.summandι i) (D.summandOpen i).ι (range_summandι D i)

theorem summandOpen_ι_comp_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    (D.summandOpen i).ι ≫ D.disjointUnionMap = (D.summandIso i).inv ≫ (D.opens i).ι := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [← h, Category.assoc, summandι_comp_disjointUnionMap]

theorem exists_summandι_base_eq (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ (i : D.idx) (y : D.piece i), (D.summandι i).base y = x := by
  obtain ⟨⟨i, y⟩, hx⟩ := (sigmaMk fun j : D.idx => (D.opens j).toScheme).surjective x
  refine ⟨i, y, ?_⟩
  show (Sigma.ι (fun j : D.idx => (D.opens j).toScheme) i).base y = x
  simpa using hx

theorem exists_mem_summandOpen (D : FiniteOpenCoverWithIdeals T) (x : ↥D.disjointUnion) :
    ∃ i : D.idx, x ∈ D.summandOpen i := by
  obtain ⟨i, y, hy⟩ := D.exists_summandι_base_eq x
  refine ⟨i, ?_⟩
  have hmem : x ∈ Set.range (D.summandι i).base := ⟨y, hy⟩
  exact hmem

theorem isAffineOpen_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (h : IsAffineOpen (D.opens i)) :
    IsAffineOpen (D.summandOpen i) := by
  have hA : IsAffine ((D.opens i).toScheme) := h
  exact isAffineOpen_opensRange (D.summandι i)

theorem restrictIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) (J : D.disjointUnion.IdealSheafData) :
    restrictIdeal J (D.summandOpen i) = (J.comap (D.summandι i)).comap (D.summandIso i).inv := by
  have h : (D.summandIso i).inv ≫ D.summandι i = (D.summandOpen i).ι := by
    simp [FiniteOpenCoverWithIdeals.summandIso]
  rw [restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp, h]

theorem restrictIdeal_iInfImageIdeal_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx) :
    restrictIdeal D.iInfImageIdeal (D.summandOpen i) =
      (D.localIdeal i).comap (D.summandIso i).inv := by
  rw [restrictIdeal_summandOpen D i D.iInfImageIdeal, comap_iInfImageIdeal_summandι D i]


theorem restrictIdeal_comap_disjointUnionMap_summandOpen (D : FiniteOpenCoverWithIdeals T) (i : D.idx)
    (J : T.scheme.IdealSheafData) :
    restrictIdeal (J.comap D.disjointUnionMap) (D.summandOpen i) =
      (restrictIdeal J (D.opens i)).comap (D.summandIso i).inv := by
  rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
    ← Scheme.IdealSheafData.comap_comp, summandOpen_ι_comp_disjointUnionMap]

private theorem summandIso_inv_comp_map_comp_affineSpaceFinToSpec (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    ((D.summandIso i).inv ≫ c.map) ≫ affineSpaceFinToSpec T.base n =
      (D.summandOpen i).ι ≫ (D.disjointUnionMap ≫ T.structMap) := by
  rw [Category.assoc, c.comp_struct, ← Category.assoc, ← summandOpen_ι_comp_disjointUnionMap,
    Category.assoc]

private theorem etale_summandIso_inv_comp_map (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    Etale ((D.summandIso i).inv ≫ c.map) := by
  have h1 : Etale c.map := c.isEtale
  have h4 : Etale ((D.summandIso i).inv) := inferInstance
  infer_instance

def summandEtaleChart (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    EtaleChart (D.disjointUnionMap ≫ T.structMap) (D.summandOpen i) n where
  map := (D.summandIso i).inv ≫ c.map
  comp_struct := summandIso_inv_comp_map_comp_affineSpaceFinToSpec D i c
  isEtale := etale_summandIso_inv_comp_map D i c

theorem summandEtaleChart_map (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) :
    (D.summandEtaleChart i c).map = (D.summandIso i).inv ≫ c.map := rfl

theorem summandEtaleChart_coordIdeal (D : FiniteOpenCoverWithIdeals T) (i : D.idx) {n : ℕ}
    (c : EtaleChart T.structMap (D.opens i) n) (S : Finset (Fin n)) :
    (D.summandEtaleChart i c).coordIdeal S = (c.coordIdeal S).comap (D.summandIso i).inv := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, summandEtaleChart_map,
    ← Scheme.IdealSheafData.comap_comp]

private theorem eq_of_map_eq_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I = Ideal.map φ I') : I = I' := by
  ext x
  constructor
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I' := by
      rw [← h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha
  · intro hx
    have hmem : φ x ∈ Ideal.map φ I := by
      rw [h]
      exact Ideal.mem_map_of_mem φ hx
    obtain ⟨a, ha, hax⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp hmem
    have hax' : a = x := hinj hax
    rw [hax'] at ha
    exact ha

private theorem top_le_preimage_opens {X : Scheme.{u}} (V : X.Opens) :
    (⊤ : V.toScheme.Opens) ≤ (TopologicalSpace.Opens.map V.ι.base).obj V := by
  intro y _
  exact y.2

private theorem appLE_ι_eq_topIso_inv {X : Scheme.{u}} (V : X.Opens) :
    V.ι.appLE V ⊤ (top_le_preimage_opens V) = V.topIso.inv := by
  simp
  rfl

private theorem ideal_eq_of_comap_ι_eq {X : Scheme.{u}} {I J : X.IdealSheafData}
    (V : X.Opens) (hV : IsAffineOpen V) (h : I.comap V.ι = J.comap V.ι) :
    I.ideal ⟨V, hV⟩ = J.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have key1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE I V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have key2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
      ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  rw [h] at key1
  have hinj : Function.Injective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V))) := by
    rw [appLE_ι_eq_topIso_inv V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (V.ι.appLE V ⊤ (top_le_preimage_opens V))) := by
    rw [appLE_ι_eq_topIso_inv V]
    exact V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact eq_of_map_eq_of_bijective _ hinj hsurj (key1.symm.trans key2)

private theorem ext_of_comap_ι_eq_of_iSup_eq_top {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)
    (hU : iSup U = ⊤) {I J : X.IdealSheafData}
    (h : ∀ i : ι, I.comap (U i).ι = J.comap (U i).ι) : I = J := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := {W : X.affineOpens // ∃ i : ι, (W.1 : X.Opens) ≤ U i})
    (fun W => W.1) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    have hx : x ∈ iSup U := by
      rw [hU]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    obtain ⟨V, hV, hxV, hVU⟩ :=
      TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hi
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, i, hVU⟩, hxV⟩
  · rintro ⟨⟨W, hW⟩, i, hWU⟩
    refine ideal_eq_of_comap_ι_eq W hW ?_
    have e1 : I.comap W.ι = (I.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    have e2 : J.comap W.ι = (J.comap (U i).ι).comap (X.homOfLE hWU) := by
      rw [← Scheme.IdealSheafData.comap_comp, Scheme.homOfLE_ι]
    rw [e1, e2, h i]

theorem ext_of_comap_summandι (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) = J'.comap (D.summandι i)) : J = J' := by
  refine ext_of_comap_ι_eq_of_iSup_eq_top (fun i : D.idx => D.summandOpen i) ?_ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · intro i
    have h1 := restrictIdeal_summandOpen D i J
    have h2 := restrictIdeal_summandOpen D i J'
    rw [h i] at h1
    exact h1.trans h2.symm

private theorem ideal_le_of_map_le_of_bijective {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (hinj : Function.Injective φ) (hsurj : Function.Surjective φ)
    {I I' : Ideal A} (h : Ideal.map φ I ≤ Ideal.map φ I') : I ≤ I' := by
  intro a ha
  have h1 : φ a ∈ Ideal.map φ I' := h (Ideal.mem_map_of_mem φ ha)
  obtain ⟨b, hb, hba⟩ := (Ideal.mem_map_iff_of_surjective (f := φ) hsurj).mp h1
  have hba' : b = a := hinj hba
  rwa [hba'] at hb

private theorem ideal_le_of_comap_ι_le {Y : Scheme.{u}} {J J' : Y.IdealSheafData}
    (V : Y.Opens) (hV : IsAffineOpen V) (h : J.comap V.ι ≤ J'.comap V.ι) :
    J.ideal ⟨V, hV⟩ ≤ J'.ideal ⟨V, hV⟩ := by
  have : IsAffine V.toScheme := hV
  have k1 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have k2 := Scheme.IdealSheafData.comap_ideal_eq_map_appLE J' V.ι ⟨V, hV⟩
    ⟨⊤, isAffineOpen_top V.toScheme⟩ (top_le_preimage_opens V)
  have hle := Scheme.IdealSheafData.le_def.mp h ⟨⊤, isAffineOpen_top V.toScheme⟩
  rw [k1, k2, appLE_ι_eq_topIso_inv V] at hle
  have hinj : Function.Injective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.injective
  have hsurj : Function.Surjective (CommRingCat.Hom.hom V.topIso.inv) :=
    V.topIso.symm.commRingCatIsoToRingEquiv.surjective
  exact ideal_le_of_map_le_of_bijective _ hinj hsurj hle

private theorem le_of_ideal_le_locally {Y : Scheme.{u}} {J J' : Y.IdealSheafData}
    (V : ↥Y → Y.Opens) (hmem : ∀ y : ↥Y, y ∈ V y)
    (hloc : ∀ (y : ↥Y) (W : Y.Opens) (hW : IsAffineOpen W), W ≤ V y →
      J.ideal ⟨W, hW⟩ ≤ J'.ideal ⟨W, hW⟩) :
    J ≤ J' := by
  have key : J ⊓ J' = J := by
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top
      (ι := {W : Y.affineOpens // ∃ y : ↥Y, (W.1 : Y.Opens) ≤ V y})
      (fun W => W.1) ?_ ?_
    · rw [eq_top_iff]
      intro x _
      obtain ⟨W, hW, hxW, hWV⟩ :=
        TopologicalSpace.Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (hmem x)
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, x, hWV⟩, hxW⟩
    · rintro ⟨⟨W, hW⟩, y, hWV⟩
      show (J ⊓ J').ideal ⟨W, hW⟩ = J.ideal ⟨W, hW⟩
      simp only [Scheme.IdealSheafData.ideal_inf, Pi.inf_apply, inf_eq_left]
      exact hloc y W hW hWV
  exact inf_eq_left.mp key

theorem le_of_comap_summandι_le (D : FiniteOpenCoverWithIdeals T) {J J' : D.disjointUnion.IdealSheafData}
    (h : ∀ i : D.idx, J.comap (D.summandι i) ≤ J'.comap (D.summandι i)) : J ≤ J' := by
  classical
  choose idxf hidxf using D.exists_mem_summandOpen
  refine le_of_ideal_le_locally (fun y => D.summandOpen (idxf y)) hidxf ?_
  intro y W hW hWle
  refine ideal_le_of_comap_ι_le W hW ?_
  have hrange : Set.range W.ι.base ⊆ Set.range (D.summandι (idxf y)).base := by
    rw [Scheme.Opens.range_ι, range_summandι D (idxf y), Scheme.Opens.range_ι]
    exact hWle
  have hg : IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange ≫ D.summandι (idxf y)
      = W.ι :=
    IsOpenImmersion.lift_fac (D.summandι (idxf y)) W.ι hrange
  have e1 : J.comap W.ι
      = (J.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  have e2 : J'.comap W.ι
      = (J'.comap (D.summandι (idxf y))).comap
        (IsOpenImmersion.lift (D.summandι (idxf y)) W.ι hrange) := by
    rw [← Scheme.IdealSheafData.comap_comp, hg]
  rw [e1, e2]
  exact Scheme.IdealSheafData.comap_mono _ (h (idxf y))

theorem etale_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_sigmaOpensDesc T.scheme D.opens

instance instEtaleTotalMap (D : FiniteOpenCoverWithIdeals T) : Etale D.disjointUnionMap :=
  etale_disjointUnionMap D

theorem smooth_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap := by
  have het : Etale D.disjointUnionMap := etale_disjointUnionMap D
  infer_instance

instance instSmoothTotalMap (D : FiniteOpenCoverWithIdeals T) : Smooth D.disjointUnionMap :=
  smooth_disjointUnionMap D

theorem flat_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : Flat D.disjointUnionMap := by
  have he : Etale D.disjointUnionMap := etale_disjointUnionMap D
  have hs : Smooth D.disjointUnionMap := inferInstance
  infer_instance

theorem locallyOfFiniteType_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_sigmaOpensDesc T.scheme D.opens

instance instLocallyOfFiniteTypeTotalMap (D : FiniteOpenCoverWithIdeals T) : LocallyOfFiniteType D.disjointUnionMap :=
  locallyOfFiniteType_disjointUnionMap D

theorem surjective_disjointUnionMap (D : FiniteOpenCoverWithIdeals T) (h : iSup D.opens = ⊤) :
    Surjective D.disjointUnionMap :=
  surjective_sigmaOpensDesc T.scheme D.opens h

theorem isAffine_disjointUnion (D : FiniteOpenCoverWithIdeals T) (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    IsAffine D.disjointUnion :=
  isAffine_sigmaOpens T.scheme D.opens h

private theorem subsingleton_spec (k : Type u) [Field k] :
    Subsingleton ↥(Spec (CommRingCat.of k)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum k))

theorem quasiCompact_disjointUnionMap_comp (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, IsAffineOpen (D.opens i)) :
    QuasiCompact (D.disjointUnionMap ≫ T.structMap) := by
  have haff : IsAffine D.disjointUnion := isAffine_disjointUnion D h
  have hcs : CompactSpace ↥D.disjointUnion := inferInstance
  have hsub : Subsingleton ↥(Spec (CommRingCat.of T.base)) := subsingleton_spec T.base
  exact AlgebraicGeometry.quasiCompact_of_compactSpace_of_subsingleton
    (D.disjointUnionMap ≫ T.structMap)

theorem isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart (D : FiniteOpenCoverWithIdeals T)
    (h : ∀ i : D.idx, ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n),
      D.localIdeal i = ⊤ ∨ ∃ j : Fin n, D.localIdeal i = c.coordIdeal {j}) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal D.iInfImageIdeal ?_
  intro x
  obtain ⟨i, hi⟩ := D.exists_mem_summandOpen x
  obtain ⟨n, c, hc⟩ := h i
  refine ⟨D.summandOpen i, hi, n, D.summandEtaleChart i c, ?_⟩
  rcases hc with htop | ⟨j, hj⟩
  · left
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, htop]
    simp
  · right
    refine ⟨j, ?_⟩
    rw [restrictIdeal_iInfImageIdeal_summandOpen D i, hj]
    exact (summandEtaleChart_coordIdeal D i c {j}).symm

theorem isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal (D : FiniteOpenCoverWithIdeals T)
    (halt : ∀ i : D.idx, D.localIdeal i = ⊤ ∨
      ∃ (n : ℕ) (c : EtaleChart T.structMap (D.opens i) n) (j : Fin n),
        D.localIdeal i = c.coordIdeal {j})
    (hchart : ∀ i : D.idx, ∃ n : ℕ, Nonempty (EtaleChart T.structMap (D.opens i) n)) :
    IsSmoothDivisor (D.disjointUnionMap ≫ T.structMap) D.iInfImageIdeal := by
  refine isSmoothDivisor_iInfImageIdeal_of_exists_etaleChart D ?_
  intro i
  rcases halt i with htop | ⟨n, c, j, hj⟩
  · obtain ⟨m, ⟨c⟩⟩ := hchart i
    exact ⟨m, c, Or.inl htop⟩
  · exact ⟨n, c, Or.inr ⟨j, hj⟩⟩

end FiniteOpenCoverWithIdeals

end MaxContactReduction

end FunctorialResolution.EmbeddedResolution

end
end

section
universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev markedTripleOfIdeal (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) : MarkedIdealWithBoundary.{u} :=
  { base := k, scheme := Y, structMap := q, ideal := J, mult := 1, boundary := [] }

@[simp] theorem markedTripleOfIdeal_scheme (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).scheme = Y := rfl

@[simp] theorem markedTripleOfIdeal_structureMorphism (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).structMap = q := rfl

@[simp] theorem markedTripleOfIdeal_ideal (k : Type u) [Field k] (Y : Scheme.{u})
    (q : Y ⟶ Spec (CommRingCat.of k)) (J : Y.IdealSheafData) :
    (markedTripleOfIdeal k Y q J).ideal = J := rfl

def HasLocalEtaleCharts {X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) : Prop :=
  ∀ x : X', ∃ (W : X'.Opens) (_ : x ∈ W) (n : ℕ), Nonempty (EtaleChart p W n)

private theorem ofIdealTop_mono {X : Scheme.{u}} {I J : Ideal Γ(X, ⊤)} (h : I ≤ J) :
    AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop I ≤
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop J := by
  intro U
  exact Ideal.map_mono h

theorem EtaleChart.coordIdeal_mono {Y : Scheme.{u}} {k : Type u} [Field k]
    {p : Y ⟶ Spec (CommRingCat.of k)} {U : Y.Opens} {m : ℕ} (ch : EtaleChart p U m)
    {S S' : Finset (Fin m)} (h : S ⊆ S') :
    ch.coordIdeal S ≤ ch.coordIdeal S' := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, coordSubspaceIdeal_eq_ofIdealTop_span_coord]
  apply Scheme.IdealSheafData.comap_mono
  apply ofIdealTop_mono
  apply Ideal.span_mono
  rintro x ⟨i, hi, rfl⟩
  exact ⟨i, Finset.mem_coe.mpr (h (Finset.mem_coe.mp hi)), rfl⟩

private theorem coe_support_ker_eq_range {X X' : Scheme.{u}} (τ : X ⟶ X') [IsClosedImmersion τ] :
    (↑(Scheme.Hom.ker τ).support : Set X') = Set.range τ.base := by
  have h1 : ∀ z, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom ≫ τ).base z
      = (Scheme.Hom.ker τ).subschemeι.base z := by
    intro z
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_hom_comp τ]
  have h2 : ∀ x, ((FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv ≫ (Scheme.Hom.ker τ).subschemeι).base x
      = τ.base x := by
    intro x
    rw [FunctorialResolution.EmbeddedResolution.kerSubschemeIso_inv_comp τ]
  rw [← Scheme.IdealSheafData.range_subschemeι]
  apply Set.Subset.antisymm
  · rintro y ⟨z, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).hom.base z, h1 z⟩
  · rintro y ⟨x, rfl⟩
    exact ⟨(FunctorialResolution.EmbeddedResolution.kerSubschemeIso τ).inv.base x, h2 x⟩

theorem restrictIdeal_ker_eq_top_of_not_mem {X X' : Scheme.{u}} (τ : X ⟶ X')
    [IsClosedImmersion τ] (U : X'.Opens) (h : ∀ x : X, τ.base x ∉ U) :
    restrictIdeal τ.ker U = ⊤ := by
  rw [restrictIdeal_eq_comap_ι, Scheme.IdealSheafData.eq_top_iff_support_eq_empty, support_comap_eq,
    coe_support_ker_eq_range τ]
  refine Set.subset_empty_iff.mp ?_
  rintro y ⟨x, hx⟩
  refine absurd ?_ (h x)
  rw [hx]
  exact y.2

structure AdaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  idxSet : Finset (Fin coordCount)
  card_idxSet : idxSet.card = c
  coord : Fin coordCount
  coord_mem : coord ∈ idxSet
  restrictIdeal_ker : restrictIdeal τ.ker opens = chart.coordIdeal idxSet

private theorem coordIdeal_restrict {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {U V : X.Opens} {m : ℕ} (ch : EtaleChart p U m)
    (h : V ≤ U) (S : Finset (Fin m)) :
    (ch.restrict h).coordIdeal S = (ch.coordIdeal S).comap (X.homOfLE h) := by
  simp only [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.restrict_map]
  rw [Scheme.IdealSheafData.comap_comp]

theorem exists_adaptedEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) :
    ∀ x : X, ∃ A : AdaptedEtaleChart p τ c, τ.base x ∈ A.opens := by
  intro x
  obtain ⟨U, hxU, m, ch, S, hcard, hker⟩ := hcodim x
  obtain ⟨V, hxV, hVU⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hxU
  have hSne : S.Nonempty := Finset.card_pos.mp (by rw [hcard]; omega)
  obtain ⟨j, hj⟩ := hSne
  refine ⟨⟨(V : X'.Opens), V.2, m, ch.restrict hVU, S, hcard, j, hj, ?_⟩, hxV⟩
  rw [restrictIdeal_eq_comap_homOfLE_restrictIdeal (Scheme.Hom.ker τ) hVU, hker,
    coordIdeal_restrict ch hVU S]

structure DisjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') : Type u where
  opens : X'.Opens
  isAffine : IsAffineOpen opens
  coordCount : ℕ
  chart : EtaleChart p opens coordCount
  not_mem : ∀ x : X, τ.base x ∉ opens

theorem exists_disjointEtaleChart {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') [IsClosedImmersion τ]
    (hcharts : HasLocalEtaleCharts p) (y : X') (hy : ∀ x : X, τ.base x ≠ y) :
    ∃ F : DisjointEtaleChart p τ, y ∈ F.opens := by
  obtain ⟨W, hyW, n, ⟨ch⟩⟩ := hcharts y
  have hclosed : IsClosed (Set.range τ.base) := by
    rw [← coe_support_ker_eq_range τ]
    exact (Scheme.Hom.ker τ).support.2
  have hopen : IsOpen ((W : Set X') ∩ (Set.range τ.base)ᶜ) :=
    W.isOpen.inter hclosed.isOpen_compl
  have hynot : y ∉ Set.range τ.base := by
    rintro ⟨x, hx⟩
    exact hy x hx
  set O : X'.Opens := ⟨(W : Set X') ∩ (Set.range τ.base)ᶜ, hopen⟩
  have hyO : y ∈ O := Set.mem_inter hyW hynot
  obtain ⟨U, hyU, hUO⟩ := AlgebraicGeometry.Scheme.exists_affineOpens_mem_le hyO
  have hUW : (U : X'.Opens) ≤ W := by
    intro z hz
    exact (hUO hz).1
  refine ⟨⟨(U : X'.Opens), U.2, n, ch.restrict hUW, ?_⟩, hyU⟩
  intro x hx
  exact (hUO hx).2 ⟨x, rfl⟩

def coverOpens {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) : α ⊕ β → X'.Opens
  | Sum.inl a => (A a).opens
  | Sum.inr b => (B b).opens

@[simp] theorem coverOpens_inl {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (a : α) :
    coverOpens A B (Sum.inl a) = (A a).opens := rfl

@[simp] theorem coverOpens_inr {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) (b : β) :
    coverOpens A B (Sum.inr b) = (B b).opens := rfl

def coverHypersurfaceIdeal {X X' : Scheme.{u}} {k : Type u} [Field k]
    {p : X' ⟶ Spec (CommRingCat.of k)} {τ : X ⟶ X'} {c : ℕ} {α : Type v} {β : Type w}
    (A : α → AdaptedEtaleChart p τ c) (B : β → DisjointEtaleChart p τ) :
    (i : α ⊕ β) → (coverOpens A B i).toScheme.IdealSheafData
  | Sum.inl a => (A a).chart.coordIdeal {(A a).coord}
  | Sum.inr _ => ⊤



structure MaximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) (τ : X ⟶ X') (I : X.IdealSheafData) (c : ℕ) :
    Type (u + 1) where
  toCoverData : MaxContactReduction.FiniteOpenCoverWithIdeals (markedTripleOfIdeal k X' p (imageIdealSheaf τ I))
  covers : iSup toCoverData.opens = ⊤
  isAffine : ∀ i : toCoverData.idx, IsAffineOpen (toCoverData.opens i)
  hasChart : ∀ i : toCoverData.idx, ∃ n : ℕ,
    Nonempty (EtaleChart p (toCoverData.opens i) n)
  hypersurface : ∀ i : toCoverData.idx, toCoverData.localIdeal i = ⊤ ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (j : Fin n),
      toCoverData.localIdeal i = ch.coordIdeal {j}
  adapted : ∀ i : toCoverData.idx,
    (toCoverData.localIdeal i = ⊤ ∧ ∀ x : X, τ.base x ∉ toCoverData.opens i) ∨
    ∃ (n : ℕ) (ch : EtaleChart p (toCoverData.opens i) n) (S : Finset (Fin n)) (j : Fin n),
      S.card = c ∧ j ∈ S ∧
        restrictIdeal τ.ker (toCoverData.opens i) = ch.coordIdeal S ∧
        toCoverData.localIdeal i = ch.coordIdeal {j}

theorem nonempty_maximalContactCover {X X' : Scheme.{u}} {k : Type u} [Field k]
    (p : X' ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.QuasiCompact p]
    (τ : X ⟶ X') [IsClosedImmersion τ] (I : X.IdealSheafData) (c : ℕ) (hc : 1 ≤ c)
    (hcodim : HasEtaleCoordCodim p τ c) (hcharts : HasLocalEtaleCharts p) :
    Nonempty (MaximalContactCover p τ I c) := by
  classical
  have hSpec : IsCompact (Set.univ : Set ↥(Spec (CommRingCat.of k))) := by
    have h := (AlgebraicGeometry.isAffineOpen_top (Spec (CommRingCat.of k))).isCompact
    rwa [TopologicalSpace.Opens.coe_top] at h
  have hX'c : IsCompact (Set.univ : Set ↥X') := by
    have h := AlgebraicGeometry.QuasiCompact.isCompact_preimage (f := p) Set.univ isOpen_univ hSpec
    rwa [Set.preimage_univ] at h
  have hcover : ∀ y : ↥X', ∃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
      y ∈ coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q := by
    intro y
    by_cases hy : ∃ x : ↥X, τ.base x = y
    · obtain ⟨x, hx⟩ := hy
      obtain ⟨A, hA⟩ := exists_adaptedEtaleChart p τ c hc hcodim x
      refine ⟨Sum.inl A, ?_⟩
      rw [← hx]
      exact hA
    · have hy' : ∀ x : X, τ.base x ≠ y := fun x hx => hy ⟨x, hx⟩
      obtain ⟨F, hF⟩ := exists_disjointEtaleChart p τ hcharts y hy'
      exact ⟨Sum.inr F, hF⟩
  have hsub : (Set.univ : Set ↥X') ⊆
      ⋃ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ,
        ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
          X'.Opens) : Set ↥X') := by
    intro y _
    obtain ⟨q, hq⟩ := hcover y
    exact Set.mem_iUnion.2 ⟨q, hq⟩
  obtain ⟨t, ht⟩ := hX'c.elim_finite_subcover
    (fun q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ =>
      ((coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q :
        X'.Opens) : Set ↥X'))
    (fun q => (coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q).isOpen)
    hsub
  refine ⟨⟨⟨{ q : AdaptedEtaleChart p τ c ⊕ DisjointEtaleChart p τ // q ∈ t }, inferInstance,
    fun q => coverOpens (fun a : AdaptedEtaleChart p τ c => a) (fun b : DisjointEtaleChart p τ => b) q.1,
    fun q => coverHypersurfaceIdeal (fun a : AdaptedEtaleChart p τ c => a)
      (fun b : DisjointEtaleChart p τ => b) q.1⟩, ?_, ?_, ?_, ?_, ?_⟩⟩
  · apply TopologicalSpace.Opens.ext
    rw [TopologicalSpace.Opens.coe_iSup, TopologicalSpace.Opens.coe_top]
    refine Set.eq_univ_of_forall fun y => ?_
    obtain ⟨q, hqt, hq⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact Set.mem_iUnion.2 ⟨⟨q, hqt⟩, hq⟩
  · rintro ⟨A | F, _⟩
    · exact A.isAffine
    · exact F.isAffine
  · rintro ⟨A | F, _⟩
    · exact ⟨A.coordCount, ⟨A.chart⟩⟩
    · exact ⟨F.coordCount, ⟨F.chart⟩⟩
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.coord, rfl⟩
    · exact Or.inl rfl
  · rintro ⟨A | F, _⟩
    · exact Or.inr ⟨A.coordCount, A.chart, A.idxSet, A.coord, A.card_idxSet, A.coord_mem,
        A.restrictIdeal_ker, rfl⟩
    · exact Or.inl ⟨rfl, F.not_mem⟩

namespace MaximalContactCover

variable {X X' : Scheme.{u}} {k : Type u} [Field k] {p : X' ⟶ Spec (CommRingCat.of k)}
  {τ : X ⟶ X'} {I : X.IdealSheafData} {c : ℕ}

abbrev projection (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion ⟶ X' :=
  C.toCoverData.disjointUnionMap

@[simp] theorem projection_eq (C : MaximalContactCover p τ I c) :
    C.projection = C.toCoverData.disjointUnionMap := rfl

theorem isAffine_disjointUnion (C : MaximalContactCover p τ I c) : IsAffine C.toCoverData.disjointUnion :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isAffine_disjointUnion C.toCoverData C.isAffine

instance instIsAffineTotal (C : MaximalContactCover p τ I c) : IsAffine C.toCoverData.disjointUnion :=
  C.isAffine_disjointUnion

theorem quasiCompact_projection_comp (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.QuasiCompact (C.projection ≫ p) :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.quasiCompact_disjointUnionMap_comp C.toCoverData C.isAffine

instance instQuasiCompactProjComp (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.QuasiCompact (C.projection ≫ p) :=
  C.quasiCompact_projection_comp

theorem smooth_projection_comp (C : MaximalContactCover p τ I c) [AlgebraicGeometry.Smooth p] :
    AlgebraicGeometry.Smooth (C.projection ≫ p) := by
  have h : AlgebraicGeometry.Smooth C.toCoverData.disjointUnionMap :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.Smooth) C.toCoverData.disjointUnionMap p h
    inferInstance

instance instSmoothProjComp (C : MaximalContactCover p τ I c) [AlgebraicGeometry.Smooth p] :
    AlgebraicGeometry.Smooth (C.projection ≫ p) :=
  C.smooth_projection_comp

theorem locallyOfFiniteType_projection_comp (C : MaximalContactCover p τ I c)
    [AlgebraicGeometry.LocallyOfFiniteType p] :
    AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p) := by
  have h1 : AlgebraicGeometry.LocallyOfFiniteType C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.locallyOfFiniteType_disjointUnionMap C.toCoverData
  exact MorphismProperty.comp_mem (@AlgebraicGeometry.LocallyOfFiniteType) C.projection p h1
    inferInstance

instance instLocallyOfFiniteTypeProjComp (C : MaximalContactCover p τ I c)
    [AlgebraicGeometry.LocallyOfFiniteType p] :
    AlgebraicGeometry.LocallyOfFiniteType (C.projection ≫ p) :=
  C.locallyOfFiniteType_projection_comp

theorem isSmoothDivisor_iInfImageIdeal (C : MaximalContactCover p τ I c) :
    IsSmoothDivisor (C.projection ≫ p) C.toCoverData.iInfImageIdeal :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.isSmoothDivisor_iInfImageIdeal_of_forall_eq_top_or_coordIdeal C.toCoverData C.hypersurface C.hasChart

theorem surjective_projection (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.projection :=
  MaxContactReduction.FiniteOpenCoverWithIdeals.surjective_disjointUnionMap C.toCoverData C.covers

abbrev pullbackFiber (C : MaximalContactCover p τ I c) : Scheme.{u} :=
  Limits.pullback τ C.projection

abbrev pullbackFiberToTotal (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ C.toCoverData.disjointUnion :=
  Limits.pullback.snd τ C.projection

abbrev pullbackFiberToBase (C : MaximalContactCover p τ I c) : C.pullbackFiber ⟶ X :=
  Limits.pullback.fst τ C.projection

theorem isPullback_pullbackFiber (C : MaximalContactCover p τ I c) :
    IsPullback C.pullbackFiberToBase C.pullbackFiberToTotal τ C.projection :=
  IsPullback.of_hasPullback τ C.projection

theorem isClosedImmersion_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal := by
  have h : IsClosedImmersion τ := inferInstance
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.IsClosedImmersion) C.isPullback_pullbackFiber h

instance instIsClosedImmersionStarEmb (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToTotal :=
  C.isClosedImmersion_pullbackFiberToTotal

theorem flat_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Flat C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) C.isPullback_pullbackFiber.flip h

instance instFlatStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Flat C.pullbackFiberToBase :=
  C.flat_pullbackFiberToBase

theorem smooth_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Smooth C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.smooth_disjointUnionMap C.toCoverData
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Smooth) C.isPullback_pullbackFiber.flip h

instance instSmoothStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Smooth C.pullbackFiberToBase :=
  C.smooth_pullbackFiberToBase

theorem surjective_pullbackFiberToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase := by
  have h : AlgebraicGeometry.Surjective C.projection := C.surjective_projection
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Surjective) C.isPullback_pullbackFiber.flip h

instance instSurjectiveStarToBase (C : MaximalContactCover p τ I c) :
    AlgebraicGeometry.Surjective C.pullbackFiberToBase :=
  C.surjective_pullbackFiberToBase

theorem ker_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    Scheme.Hom.ker C.pullbackFiberToTotal = τ.ker.comap C.projection := by
  have hq : AlgebraicGeometry.QuasiCompact τ := inferInstance
  have hq' : AlgebraicGeometry.QuasiCompact C.pullbackFiberToTotal :=
    quasiCompact_of_isPullback C.isPullback_pullbackFiber
  have hf : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  exact ker_eq_comap_ker_of_isPullback_of_flat C.isPullback_pullbackFiber

theorem exists_factor_pullbackFiberToTotal (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    ∃ f : C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme,
      f ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal := by
  have hle : C.toCoverData.iInfImageIdeal ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    have hker : Scheme.Hom.ker C.pullbackFiberToTotal
        = (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := C.ker_pullbackFiberToTotal
    rw [hker]
    refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
    intro i
    have e1 : C.toCoverData.iInfImageIdeal.comap (C.toCoverData.summandι i)
        = C.toCoverData.localIdeal i :=
      MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι C.toCoverData i
    have e2 : ((Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap).comap
          (C.toCoverData.summandι i)
        = restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
      rw [← Scheme.IdealSheafData.comap_comp,
        MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap, restrictIdeal_eq_comap_ι]
    rw [e1, e2]
    rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hrestrict, hloc⟩
    · exact le_of_eq (htop.trans (restrictIdeal_ker_eq_top_of_not_mem τ _ hnot).symm)
    · rw [hloc, hrestrict]
      exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)
  have hle' : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι
      ≤ Scheme.Hom.ker C.pullbackFiberToTotal := by
    rwa [Scheme.IdealSheafData.ker_subschemeι]
  exact ⟨IsClosedImmersion.lift C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle',
    IsClosedImmersion.lift_fac C.toCoverData.iInfImageIdeal.subschemeι C.pullbackFiberToTotal hle'⟩

def pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.pullbackFiber ⟶ C.toCoverData.iInfImageIdeal.subscheme :=
  (C.exists_factor_pullbackFiberToTotal).choose

theorem pullbackFiberToHypersurface_comp_subschemeι (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι = C.pullbackFiberToTotal :=
  (C.exists_factor_pullbackFiberToTotal).choose_spec

theorem pullbackFiberToHypersurface_comp_subschemeι_assoc (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    {Z : Scheme.{u}} (h : C.toCoverData.disjointUnion ⟶ Z) :
    C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι ≫ h = C.pullbackFiberToTotal ≫ h := by
  rw [← Category.assoc, C.pullbackFiberToHypersurface_comp_subschemeι]

private theorem isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    IsClosedImmersion (C.pullbackFiberToHypersurface ≫ C.toCoverData.iInfImageIdeal.subschemeι) := by
  rw [C.pullbackFiberToHypersurface_comp_subschemeι]
  infer_instance

theorem isClosedImmersion_pullbackFiberToHypersurface (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToHypersurface := by
  have := isClosedImmersion_pullbackFiberToHypersurface_comp_subschemeι C
  exact AlgebraicGeometry.IsClosedImmersion.of_comp C.pullbackFiberToHypersurface
    C.toCoverData.iInfImageIdeal.subschemeι

instance instIsClosedImmersionStarFactor (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    IsClosedImmersion C.pullbackFiberToHypersurface :=
  C.isClosedImmersion_pullbackFiberToHypersurface

def comapImageIdealSheaf (C : MaximalContactCover p τ I c) : C.toCoverData.disjointUnion.IdealSheafData :=
  (imageIdealSheaf τ I).comap C.projection

theorem comapImageIdealSheaf_eq (C : MaximalContactCover p τ I c) :
    C.comapImageIdealSheaf = (imageIdealSheaf τ I).comap C.projection := rfl

def idealOnHypersurface (C : MaximalContactCover p τ I c) :
    C.toCoverData.iInfImageIdeal.subscheme.IdealSheafData :=
  C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι

theorem idealOnHypersurface_eq_comap (C : MaximalContactCover p τ I c) :
    C.idealOnHypersurface = C.comapImageIdealSheaf.comap C.toCoverData.iInfImageIdeal.subschemeι := rfl

private theorem localIdeal_le_restrictIdeal_ker (C : MaximalContactCover p τ I c) [IsClosedImmersion τ]
    (i : C.toCoverData.idx) :
    C.toCoverData.localIdeal i ≤ restrictIdeal (Scheme.Hom.ker τ) (C.toCoverData.opens i) := by
  rcases C.adapted i with ⟨htop, hnot⟩ | ⟨n, ch, S, j, hcard, hjS, hker, hloc⟩
  · have h1 := restrictIdeal_ker_eq_top_of_not_mem τ (C.toCoverData.opens i) hnot
    rw [htop]
    exact h1.ge
  · rw [hloc, hker]
    exact ch.coordIdeal_mono (Finset.singleton_subset_iff.mpr hjS)

private theorem iInfImageIdeal_le_comap_ker (C : MaximalContactCover p τ I c) [IsClosedImmersion τ] :
    C.toCoverData.iInfImageIdeal ≤ (Scheme.Hom.ker τ).comap C.toCoverData.disjointUnionMap := by
  refine MaxContactReduction.FiniteOpenCoverWithIdeals.le_of_comap_summandι_le C.toCoverData ?_
  intro i
  rw [MaxContactReduction.FiniteOpenCoverWithIdeals.comap_iInfImageIdeal_summandι,
    ← Scheme.IdealSheafData.comap_comp,
    MaxContactReduction.FiniteOpenCoverWithIdeals.summandι_comp_disjointUnionMap]
  exact localIdeal_le_restrictIdeal_ker C i

theorem comapImageIdealSheaf_eq_imageIdealSheaf_idealOnHypersurface (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    C.comapImageIdealSheaf = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι C.idealOnHypersurface := by
  have hG : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι = C.toCoverData.iInfImageIdeal := by
    simp
  have hle : Scheme.Hom.ker C.toCoverData.iInfImageIdeal.subschemeι ≤ C.comapImageIdealSheaf := by
    rw [hG, C.comapImageIdealSheaf_eq]
    exact le_trans (iInfImageIdeal_le_comap_ker C)
      (Scheme.IdealSheafData.comap_mono C.projection (ker_le_map_idealSheaf τ I))
  have h2 := ker_subschemeι_comp_eq_of_ker_le C.toCoverData.iInfImageIdeal.subschemeι C.comapImageIdealSheaf hle
    C.idealOnHypersurface C.idealOnHypersurface_eq_comap
  exact h2.symm

theorem idealOnHypersurface_eq_imageIdealSheaf (C : MaximalContactCover p τ I c)
    [IsClosedImmersion τ] :
    C.idealOnHypersurface = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) := by
  have hqc : AlgebraicGeometry.QuasiCompact τ := inferInstance
  have hflat : AlgebraicGeometry.Flat C.projection :=
    MaxContactReduction.FiniteOpenCoverWithIdeals.flat_disjointUnionMap C.toCoverData
  have h1 : (imageIdealSheaf τ I).comap C.projection
      = imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase) :=
    comap_map_eq_map_comap_of_isPullback C.isPullback_pullbackFiber I
  have h2 : imageIdealSheaf C.pullbackFiberToTotal (I.comap C.pullbackFiberToBase)
      = imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
          (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase)) := by
    have h := Scheme.IdealSheafData.map_comp (I.comap C.pullbackFiberToBase) C.pullbackFiberToHypersurface
      C.toCoverData.iInfImageIdeal.subschemeι
    rw [C.pullbackFiberToHypersurface_comp_subschemeι] at h
    exact h
  have h3 : (imageIdealSheaf C.toCoverData.iInfImageIdeal.subschemeι
        (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))).comap
        C.toCoverData.iInfImageIdeal.subschemeι
      = imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase) :=
    Blowup.comap_map_of_isClosedImmersion
      C.toCoverData.iInfImageIdeal.subschemeι (imageIdealSheaf C.pullbackFiberToHypersurface (I.comap C.pullbackFiberToBase))
  rw [C.idealOnHypersurface_eq_comap, C.comapImageIdealSheaf_eq, h1, h2, h3]

end MaximalContactCover

end FunctorialResolution.EmbeddedResolution

end
end
