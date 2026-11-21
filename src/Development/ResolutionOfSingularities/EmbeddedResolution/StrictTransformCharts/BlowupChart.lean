import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Blowup.AffineBlowupUniversal
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart

section
open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

def uliftFinset (m : ℕ) (S : Finset (Fin m)) : Finset (ULift.{u} (Fin m)) :=
  S.map ⟨fun j => (ULift.up j : ULift.{u} (Fin m)), fun _ _ h => congrArg ULift.down h⟩

@[simp] theorem mem_uliftFinset {m : ℕ} (S : Finset (Fin m)) (x : ULift.{u} (Fin m)) :
    x ∈ uliftFinset.{u} m S ↔ x.down ∈ S := by
  constructor
  · intro h
    obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp h
    exact ha
  · intro h
    exact Finset.mem_map.mpr ⟨x.down, h, rfl⟩

theorem up_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {j : Fin m} (hj : j ∈ S) :
    (ULift.up j : ULift.{u} (Fin m)) ∈ uliftFinset.{u} m S :=
  (mem_uliftFinset S _).mpr hj

theorem down_mem_of_mem_uliftFinset {m : ℕ} {S : Finset (Fin m)} {x : ULift.{u} (Fin m)}
    (hx : x ∈ uliftFinset.{u} m S) : x.down ∈ S :=
  (mem_uliftFinset S x).mp hx

abbrev finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Ideal (MvPolynomial (ULift.{u} (Fin m)) k) :=
  coordIdeal k (uliftFinset.{u} m S)

def affineSpaceSpecIso (k : Type u) [Field k] (m : ℕ) :
    affineSpaceFin k m ≅ Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) :=
  AffineSpace.SpecIso (ULift.{u} (Fin m)) (CommRingCat.of k)

private theorem appTop_comp_apply_eq_appTop_appTop {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (x : Γ(Z, ⊤)) : (f ≫ g).appTop.hom x = f.appTop.hom (g.appTop.hom x) := rfl

private theorem appTop_specMap_ΓSpecIso_inv_apply {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop.hom ((Scheme.ΓSpecIso R).inv.hom x)
      = (Scheme.ΓSpecIso S).inv.hom (f.hom x) := by
  have h : (Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop = f ≫ (Scheme.ΓSpecIso S).inv := by
    rw [← cancel_mono (Scheme.ΓSpecIso S).hom]
    simp [Scheme.ΓSpecIso_naturality]
  have h2 : ((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom x
      = (f ≫ (Scheme.ΓSpecIso S).inv).hom x := by rw [h]
  exact h2

private theorem affineSpaceSpecIso_inv_appTop_coord (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).inv.appTop.hom (AffineSpace.coord (Spec (CommRingCat.of k)) j)
      = (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j) := by
  apply AlgebraicGeometry.AffineSpace.SpecIso_inv_appTop_coord

private theorem affineSpaceSpecIso_hom_appTop_X (k : Type u) [Field k] (m : ℕ)
    (j : ULift.{u} (Fin m)) :
    (affineSpaceSpecIso k m).hom.appTop.hom
        ((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X j))
      = AffineSpace.coord (Spec (CommRingCat.of k)) j := by
  rw [← affineSpaceSpecIso_inv_appTop_coord k m j, ← appTop_comp_apply_eq_appTop_appTop, Iso.hom_inv_id]
  simp

private theorem affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec (k : Type u) [Field k] (m : ℕ) :
    (affineSpaceSpecIso k m).inv ≫ affineSpaceFinToSpec k m
      = Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin m)) k)) := by
  simp [affineSpaceSpecIso, affineSpaceFinToSpec]

abbrev affineSpaceCoordBlowup (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) : Scheme.{u} :=
  Blowup.affineBlowup (finCoordIdeal k m S)

def affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    affineSpaceCoordBlowup k m S ⟶ affineSpaceFin k m :=
  Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv

private theorem comap_specIdealSheaf_finCoordIdeal (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (Blowup.specIdealSheaf (finCoordIdeal k m S)).comap (affineSpaceSpecIso k m).hom
      = coordSubspaceIdeal k m S := by
  have : IsAffine (affineSpaceFin k m) := inferInstance
  have hset : ((affineSpaceSpecIso k m).hom.appTop.hom) ''
      (((Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom) ''
        ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))))
      = (fun i => AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up i)) ''
          (↑S : Set (Fin m)) := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, ⟨j, hj, rfl⟩, rfl⟩, rfl⟩
      exact ⟨j.down, Finset.mem_coe.mpr (down_mem_of_mem_uliftFinset (Finset.mem_coe.mp hj)),
        (affineSpaceSpecIso_hom_appTop_X k m j).symm⟩
    · rintro ⟨i, hi, rfl⟩
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k))).inv.hom
          (MvPolynomial.X (ULift.up i)),
        ⟨MvPolynomial.X (ULift.up i),
          ⟨ULift.up i, Finset.mem_coe.mpr (up_mem_uliftFinset (Finset.mem_coe.mp hi)), rfl⟩, rfl⟩,
        ?_⟩
      exact affineSpaceSpecIso_hom_appTop_X k m (ULift.up i)
  have hI : (finCoordIdeal k m S : Ideal (MvPolynomial (ULift.{u} (Fin m)) k))
      = Ideal.span ((MvPolynomial.X : ULift.{u} (Fin m) → MvPolynomial (ULift.{u} (Fin m)) k) ''
          (↑(uliftFinset.{u} m S) : Set (ULift.{u} (Fin m)))) :=
    coordIdeal_eq_span k (uliftFinset.{u} m S)
  rw [Blowup.specIdealSheaf_eq_ofIdealTop, Scheme.IdealSheafData.comap_ofIdealTop, coordSubspaceIdeal_eq_ofIdealTop_span_coord, hI,
    Ideal.map_span, Ideal.map_span, hset]

theorem isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    Blowup.IsBlowupAlongIdealSheaf (affineSpaceCoordBlowupMap k m S) (coordSubspaceIdeal k m S) := by
  rw [← comap_specIdealSheaf_finCoordIdeal k m S]
  exact (Blowup.isBlowupAlongIdealSheaf_affineBlowup_toSpec (finCoordIdeal k m S)).comp_iso_hom
    (affineSpaceSpecIso k m).symm

abbrev finCoordIdealGen (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    ↥(finCoordIdeal k m S) :=
  coordIdealGen k (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)

abbrev coordBlowupChartRing (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :=
  HomogeneousLocalization.Away (Blowup.reesGrading (finCoordIdeal k m S))
    (Blowup.reesGenerator (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))

def coordBlowupChartRingEquiv (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    coordBlowupChartRing k m S s hs ≃+* MvPolynomial (ULift.{u} (Fin m)) k :=
  @awayCoordGenEquivMvPolynomial k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)
    (up_mem_uliftFinset hs)

def coordBlowupChartRingCatIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    CommRingCat.of (coordBlowupChartRing k m S s hs) ≅
      CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k) :=
  (coordBlowupChartRingEquiv k m S s hs).toCommRingCatIso

def specCoordBlowupChartRingIso (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅
      Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin m)) k)) where
  hom := Spec.map (coordBlowupChartRingCatIso k m S s hs).inv
  inv := Spec.map (coordBlowupChartRingCatIso k m S s hs).hom
  hom_inv_id := by rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  inv_hom_id := by rw [← Spec.map_comp, Iso.inv_hom_id, Spec.map_id]

def specCoordBlowupChartRingIsoAffineSpace (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ≅ affineSpaceFin k m :=
  specCoordBlowupChartRingIso k m S s hs ≪≫ (affineSpaceSpecIso k m).symm

def affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m)
    (hs : s ∈ S) :
    Spec (CommRingCat.of (coordBlowupChartRing k m S s hs)) ⟶ affineSpaceCoordBlowup k m S :=
  Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

instance instIsOpenImmersionModelBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m))
    (s : Fin m) (hs : s ∈ S) : IsOpenImmersion (affineSpaceCoordBlowupChart k m S s hs) :=
  Blowup.instIsOpenImmersionAffineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs)

private def coordBlowupSubstUliftFin (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) (s : Fin m) :
    MvPolynomial (ULift.{u} (Fin m)) k →ₐ[k] MvPolynomial (ULift.{u} (Fin m)) k :=
  @coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _) (uliftFinset.{u} m S) (ULift.up s)

private theorem specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) :
    Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
        ≫ (affineSpaceSpecIso k m).inv
      = (affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s := by
  refine AffineSpace.hom_ext ?_ ?_
  · show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv) ≫ affineSpaceFinToSpec k m
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m
    rw [Category.assoc, Category.assoc, coordBlowupSubstMap_comp_affineSpaceFinToSpec, affineSpaceSpecIso_inv_comp_affineSpaceFinToSpec,
      ← Spec.map_comp]
    congr 1
    ext r
    simp [coordBlowupSubstUliftFin]
  · intro i
    show (Spec.map (CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom)
          ≫ (affineSpaceSpecIso k m).inv).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
      = ((affineSpaceSpecIso k m).inv ≫ coordBlowupSubstMap k m S s).appTop.hom
            (AffineSpace.coord (Spec (CommRingCat.of k)) i)
    rw [appTop_comp_apply_eq_appTop_appTop, appTop_comp_apply_eq_appTop_appTop, affineSpaceSpecIso_inv_appTop_coord,
      appTop_specMap_ΓSpecIso_inv_apply, coordBlowupSubstMap_appTop_coord]
    by_cases hc : i.down ∈ S ∧ i.down ≠ s
    · rw [if_pos hc, map_mul, affineSpaceSpecIso_inv_appTop_coord, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc.1, hc.2]
    · rw [if_neg hc, affineSpaceSpecIso_inv_appTop_coord]
      simp [coordBlowupSubstUliftFin, ULift.ext_iff, hc]

theorem affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap (k : Type u) [Field k] (m : ℕ)
    (S : Finset (Fin m)) (s : Fin m) (hs : s ∈ S) :
    affineSpaceCoordBlowupChart k m S s hs ≫ affineSpaceCoordBlowupMap k m S =
      (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s := by
  have hcomp : (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom.comp
      (coordBlowupSubstUliftFin k m S s).toRingHom
      = Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) :=
    @awayCoordGenEquivMvPolynomial_symm_comp_coordBlowupSubst k _ (ULift.{u} (Fin m)) (Classical.decEq _)
      (uliftFinset.{u} m S) (ULift.up s) (up_mem_uliftFinset hs)
  have hring : CommRingCat.ofHom (Blowup.chartRingHom (finCoordIdeal k m S) (finCoordIdealGen k m S s hs))
      = CommRingCat.ofHom (coordBlowupSubstUliftFin k m S s).toRingHom ≫
        CommRingCat.ofHom (coordBlowupChartRingEquiv k m S s hs).symm.toRingHom := by
    rw [← hcomp]
    rfl
  show Blowup.affineBlowupChart (finCoordIdeal k m S) (finCoordIdealGen k m S s hs) ≫
      (Blowup.AffineBlowup.toSpec (finCoordIdeal k m S) ≫ (affineSpaceSpecIso k m).inv)
    = (specCoordBlowupChartRingIsoAffineSpace k m S s hs).hom ≫ coordBlowupSubstMap k m S s
  rw [← Category.assoc, Blowup.affineBlowupChart_comp_toSpec, Blowup.algebraMap_chart_eq_chartRingHom, hring,
    Spec.map_comp, Category.assoc, specMap_coordBlowupSubstUliftFin_comp_affineSpaceSpecIso_inv k m S s, ← Category.assoc]
  rfl

theorem iSup_opensRange_affineSpaceCoordBlowupChart (k : Type u) [Field k] (m : ℕ) (S : Finset (Fin m)) :
    (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2))
      = (⊤ : (affineSpaceCoordBlowup k m S).Opens) := by
  refine le_antisymm le_top ?_
  rw [← iSup_opensRange_affineBlowupChart_coordIdealGen k (uliftFinset.{u} m S)]
  refine iSup_le fun j => ?_
  refine le_iSup_of_le ⟨j.1.down, down_mem_of_mem_uliftFinset j.2⟩ ?_
  exact le_rfl

end FunctorialResolution.EmbeddedResolution

end
end

section
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

universe u

structure BlowupChart {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (s : Fin m) where
  domain : X₁.Opens
  domain_le : domain ≤ π ⁻¹ᵁ U
  chart : EtaleChart (π ≫ p) domain m
  comm : chart.map ≫ coordBlowupSubstMap k m S s = π.resLE U domain domain_le ≫ c.map

private theorem exists_opens_isPullback_of_opens {X₁ M : Scheme.{u}} (V : X₁.Opens)
    (q : V.toScheme ⟶ M) (W : M.Opens) :
    ∃ (dom : X₁.Opens) (_hle : dom ≤ V) (g : dom.toScheme ⟶ W.toScheme)
      (r : dom.toScheme ⟶ V.toScheme),
      IsPullback g r W.ι q ∧ r ≫ V.ι = dom.ι ∧
        ∀ y, q.base y ∈ W → V.ι.base y ∈ dom := by
  classical
  have hdle : Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι) ≤ V := by
    rintro x ⟨y, rfl⟩
    have h1 : V.ι.base ((q ⁻¹ᵁ W).ι.base y) ∈ Set.range V.ι.base := ⟨_, rfl⟩
    rw [Scheme.Opens.range_ι] at h1
    exact h1
  obtain ⟨e, he⟩ : ∃ e : (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).toScheme ≅
      (q ⁻¹ᵁ W).toScheme,
      e.hom ≫ ((q ⁻¹ᵁ W).ι ≫ V.ι) = (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι :=
    ⟨IsOpenImmersion.isoOfRangeEq (Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι)).ι
        ((q ⁻¹ᵁ W).ι ≫ V.ι) (Scheme.Opens.range_ι _),
      IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩
  refine ⟨Scheme.Hom.opensRange ((q ⁻¹ᵁ W).ι ≫ V.ι), hdle, e.hom ≫ (q ∣_ W),
    e.hom ≫ (q ⁻¹ᵁ W).ι, ?_, ?_, ?_⟩
  · have h1 : IsPullback e.hom (e.hom ≫ (q ⁻¹ᵁ W).ι) ((q ⁻¹ᵁ W).ι) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by simp⟩
    have h2 := h1.paste_horiz (isPullback_morphismRestrict q W)
    rwa [Category.id_comp] at h2
  · rw [Category.assoc]
    exact he
  · intro y hy
    exact ⟨⟨y, hy⟩, rfl⟩

private theorem exists_blowupChart_family_isPullback_covering {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) (Z : X.IdealSheafData)
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S) :
    ∃ F : ∀ s : Fin m, s ∈ S → BlowupChart π c S s,
      (∀ (s : Fin m) (hs : s ∈ S),
          IsPullback (F s hs).chart.map
            (π.resLE U (F s hs).domain (F s hs).domain_le)
            (coordBlowupSubstMap k m S s) c.map) ∧
      (∀ x : ↥X₁, x ∈ π ⁻¹ᵁ U → ∃ (s : Fin m) (hs : s ∈ S), x ∈ (F s hs).domain) := by
  classical
  have : AlgebraicGeometry.Etale c.map := c.isEtale
  have : AlgebraicGeometry.Flat c.map := inferInstance
  have hcomap : Z.comap U.ι = (coordSubspaceIdeal k m S).comap c.map := by
    rw [← restrictIdeal_eq_comap_ι, hZ, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  have hres : Blowup.IsBlowupAlongIdealSheaf (π ∣_ U) ((coordSubspaceIdeal k m S).comap c.map) := by
    have h1 := hπ.restrict U
    rwa [hcomap] at h1
  obtain ⟨q, -, hq⟩ := (isBlowupAlongIdealSheaf_affineSpaceCoordBlowupMap k m S).exists_isPullback_of_flat c.map hres
  have key : ∀ (s : Fin m) (hs : s ∈ S), ∃ B : BlowupChart π c S s,
      IsPullback B.chart.map (π.resLE U B.domain B.domain_le) (coordBlowupSubstMap k m S s) c.map ∧
        ∀ y, q.base y ∈ Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs) →
          (π ⁻¹ᵁ U).ι.base y ∈ B.domain := by
    intro s hs
    obtain ⟨dom, hle, g, r, hpb, hrι, hmem⟩ :=
      exists_opens_isPullback_of_opens (π ⁻¹ᵁ U) q (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    have hrange : Set.range (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι.base
        = Set.range (affineSpaceCoordBlowupChart k m S s hs).base :=
      Scheme.Opens.range_ι (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs))
    obtain ⟨eW, heW⟩ : ∃ e : (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).toScheme ≅
        affineSpaceFin k m,
        e.hom ≫ coordBlowupSubstMap k m S s =
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫ affineSpaceCoordBlowupMap k m S := by
      refine ⟨IsOpenImmersion.isoOfRangeEq
          (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
          (affineSpaceCoordBlowupChart k m S s hs) hrange ≪≫ specCoordBlowupChartRingIsoAffineSpace k m S s hs, ?_⟩
      have hfac := IsOpenImmersion.isoOfRangeEq_hom_fac
        (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι
        (affineSpaceCoordBlowupChart k m S s hs) hrange
      rw [Iso.trans_hom, Category.assoc, ← affineSpaceCoordBlowupChart_comp_affineSpaceCoordBlowupMap,
        ← Category.assoc, hfac]
    have heW' : eW.inv ≫ (Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S s hs)).ι ≫
        affineSpaceCoordBlowupMap k m S = coordBlowupSubstMap k m S s := by
      rw [← heW, Iso.inv_hom_id_assoc]
    have hleft : r ≫ (π ∣_ U) = π.resLE U dom hle := by
      rw [← cancel_mono U.ι, Category.assoc, morphismRestrict_ι, Scheme.Hom.resLE_comp_ι,
        ← Category.assoc, hrι]
    have hsq : IsPullback (g ≫ eW.hom) (π.resLE U dom hle) (coordBlowupSubstMap k m S s) c.map := by
      have h1 : IsPullback (g ≫ eW.hom) (𝟙 _) eW.inv g :=
        IsPullback.of_vert_isIso ⟨by simp⟩
      have h2 := h1.paste_vert (hpb.paste_vert hq)
      rwa [Category.id_comp, hleft, heW'] at h2
    have hetale : AlgebraicGeometry.Etale (g ≫ eW.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq.flip c.isEtale
    refine ⟨⟨dom, hle, ⟨g ≫ eW.hom, ?_, hetale⟩, hsq.w⟩, hsq, hmem⟩
    calc (g ≫ eW.hom) ≫ affineSpaceFinToSpec k m
        = (g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s ≫ affineSpaceFinToSpec k m := by
          rw [coordBlowupSubstMap_comp_affineSpaceFinToSpec]
      _ = ((g ≫ eW.hom) ≫ coordBlowupSubstMap k m S s) ≫ affineSpaceFinToSpec k m := by
          simp only [Category.assoc]
      _ = (π.resLE U dom hle ≫ c.map) ≫ affineSpaceFinToSpec k m := by rw [hsq.w]
      _ = π.resLE U dom hle ≫ c.map ≫ affineSpaceFinToSpec k m := by simp only [Category.assoc]
      _ = π.resLE U dom hle ≫ U.ι ≫ p := by rw [c.comp_struct]
      _ = (π.resLE U dom hle ≫ U.ι) ≫ p := by simp only [Category.assoc]
      _ = (dom.ι ≫ π) ≫ p := by rw [Scheme.Hom.resLE_comp_ι]
      _ = dom.ι ≫ π ≫ p := by simp only [Category.assoc]
  choose F hF1 hF2 using key
  refine ⟨F, hF1, ?_⟩
  intro x hx
  have hx' : x ∈ Set.range (π ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Opens.range_ι]
    exact hx
  obtain ⟨y, rfl⟩ := hx'
  have hy : q.base y ∈
      (⨆ i : ↥S, Scheme.Hom.opensRange (affineSpaceCoordBlowupChart k m S i.1 i.2)) := by
    rw [iSup_opensRange_affineSpaceCoordBlowupChart k m S]
    simp
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
  exact ⟨i.1, i.2, hF2 i.1 i.2 y hi⟩

def blowupChartOfIsBlowup {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) : BlowupChart π c S s :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose s hs

theorem isPullback_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (s : Fin m) (hs : s ∈ S) :
    IsPullback (blowupChartOfIsBlowup π c S hπ hZ s hs).chart.map
      (π.resLE U (blowupChartOfIsBlowup π c S hπ hZ s hs).domain
        (blowupChartOfIsBlowup π c S hπ hZ s hs).domain_le)
      (coordBlowupSubstMap k m S s) c.map :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.1 s hs

theorem exists_mem_domain_blowupChart_of_isBlowupAlongIdealSheaf {X X₁ : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} (π : X₁ ⟶ X) {U : X.Opens} {m : ℕ}
    (c : EtaleChart p U m) (S : Finset (Fin m)) {Z : X.IdealSheafData}
    (hπ : Blowup.IsBlowupAlongIdealSheaf π Z) (hZ : restrictIdeal Z U = c.coordIdeal S)
    (x : ↥X₁) (hx : x ∈ π ⁻¹ᵁ U) :
    ∃ (s : Fin m) (hs : s ∈ S), x ∈ (blowupChartOfIsBlowup π c S hπ hZ s hs).domain :=
  (exists_blowupChart_family_isPullback_covering π c S Z hπ hZ).choose_spec.2 x hx

end FunctorialResolution.EmbeddedResolution

end
end
