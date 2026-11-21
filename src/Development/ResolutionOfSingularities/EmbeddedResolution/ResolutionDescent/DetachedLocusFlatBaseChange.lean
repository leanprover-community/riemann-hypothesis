import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ChartFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IrreducibleComponentsFlatPreimage
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback

section
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace FunctorialResolution.EmbeddedResolution

variable {α : Type*} [TopologicalSpace α]

private theorem radical_ringHom_ker_eq {R S : Type*} [CommRing R] [CommRing S] [_root_.IsReduced S]
    (φ : R →+* S) : (RingHom.ker φ).radical = RingHom.ker φ := by
  refine le_antisymm ?_ Ideal.le_radical
  rintro x ⟨n, hn⟩
  rw [RingHom.mem_ker] at hn ⊢
  have hx : φ x ^ n = 0 := by rw [← map_pow]; exact hn
  exact IsNilpotent.eq_zero ⟨n, hx⟩

theorem isClosed_sUnion_irreducibleComponents [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    IsClosed (⋃₀ S) := by
  have hfin : S.Finite :=
    Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents) hS
  rw [Set.sUnion_eq_biUnion]
  refine hfin.isClosed_biUnion ?_
  intro s hs
  apply isClosed_of_mem_irreducibleComponents
  exact hS hs

theorem isOpen_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    (S : Set (Set α)) :
    IsOpen ((⋃₀ (irreducibleComponents α \ S))ᶜ) :=
  (isClosed_sUnion_irreducibleComponents Set.sdiff_subset).isOpen_compl

theorem compl_sUnion_irreducibleComponents_sdiff_subset (S : Set (Set α)) :
    (⋃₀ (irreducibleComponents α \ S))ᶜ ⊆ ⋃₀ S := by
  intro x hx
  rw [Set.mem_compl_iff] at hx
  have hmem : x ∈ irreducibleComponent x := by apply mem_irreducibleComponent
  have hcomp : irreducibleComponent x ∈ irreducibleComponents α := by
    apply irreducibleComponent_mem_irreducibleComponents
  by_cases hC : irreducibleComponent x ∈ S
  · exact ⟨irreducibleComponent x, hC, hmem⟩
  · exact (hx ⟨irreducibleComponent x, ⟨hcomp, hC⟩, hmem⟩).elim

theorem closure_compl_sUnion_irreducibleComponents_sdiff [NoetherianSpace α]
    {S : Set (Set α)} (hS : S ⊆ irreducibleComponents α) :
    closure ((⋃₀ (irreducibleComponents α \ S))ᶜ) = ⋃₀ S := by
  have hZcl : IsClosed (⋃₀ (irreducibleComponents α \ S)) :=
    isClosed_sUnion_irreducibleComponents Set.sdiff_subset
  apply Set.Subset.antisymm
  · exact closure_minimal (compl_sUnion_irreducibleComponents_sdiff_subset S)
      (isClosed_sUnion_irreducibleComponents hS)
  · rintro x ⟨C, hCS, hxC⟩
    have hCcomp : C ∈ irreducibleComponents α := hS hCS
    have hCirr : IsIrreducible C := hCcomp.1
    have hnot : ¬ C ⊆ ⋃₀ (irreducibleComponents α \ S) := by
      intro hsub
      have hfin : (irreducibleComponents α \ S).Finite :=
        Set.Finite.subset (by apply NoetherianSpace.finite_irreducibleComponents)
          Set.sdiff_subset
      obtain ⟨D, hD, hCsubD⟩ := isIrreducible_iff_sUnion_isClosed.mp hCirr hfin.toFinset
        (fun z hz => isClosed_of_mem_irreducibleComponents z (hfin.mem_toFinset.mp hz).1)
        (by rwa [hfin.coe_toFinset])
      have hD' : D ∈ irreducibleComponents α \ S := hfin.mem_toFinset.mp hD
      have hDsubC : D ⊆ C := hCcomp.2 hD'.1.1 hCsubD
      exact hD'.2 (by rw [Set.Subset.antisymm hDsubC hCsubD]; exact hCS)
    obtain ⟨y, hyC, hyZ⟩ := Set.not_subset.mp hnot
    rw [mem_closure_iff]
    intro o ho hxo
    obtain ⟨z, hz, hzo, hzZ⟩ := hCirr.2 o (⋃₀ (irreducibleComponents α \ S))ᶜ ho
      hZcl.isOpen_compl ⟨x, hxC, hxo⟩ ⟨y, hyC, hyZ⟩
    exact ⟨z, hzo, hzZ⟩

theorem vanishingIdeal_congr {X : Scheme.{u}} {Z₁ Z₂ : Closeds ↥X}
    (h : (Z₁ : Set ↥X) = (Z₂ : Set ↥X)) :
    Scheme.IdealSheafData.vanishingIdeal Z₁ = Scheme.IdealSheafData.vanishingIdeal Z₂ := by
  have hZ : Z₁ = Z₂ := SetLike.coe_injective h
  rw [hZ]

def complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) : X.Opens :=
  ⟨(⋃₀ (irreducibleComponents ↥X \ S))ᶜ,
    isOpen_compl_sUnion_irreducibleComponents_sdiff S⟩

@[simp]
theorem coe_complSUnionOtherComponents (X : Scheme.{u}) [NoetherianSpace ↥X] (S : Set (Set ↥X)) :
    (complSUnionOtherComponents X S : Set ↥X) = (⋃₀ (irreducibleComponents ↥X \ S))ᶜ :=
  rfl

private theorem radical_scheme_ker_eq {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] :
    (Scheme.Hom.ker g).radical = Scheme.Hom.ker g := by
  refine le_antisymm ?_ (Scheme.IdealSheafData.le_radical _)
  show (Scheme.Hom.ker g).radical ≤
    Scheme.IdealSheafData.ofIdeals fun U => RingHom.ker (CommRingCat.Hom.hom (g.app U.1))
  refine Scheme.IdealSheafData.le_ofIdeals_iff.mpr ?_
  intro U
  have := AlgebraicGeometry.IsReduced.component_reduced (X := X) (g ⁻¹ᵁ U.1)
  have hle : (Scheme.Hom.ker g).ideal U ≤ RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := by
    unfold AlgebraicGeometry.Scheme.Hom.ker
    exact Scheme.IdealSheafData.ideal_ofIdeals_le _ U
  rw [Scheme.IdealSheafData.radical_ideal]
  calc ((Scheme.Hom.ker g).ideal U).radical
      ≤ (RingHom.ker (CommRingCat.Hom.hom (g.app U.1))).radical := Ideal.radical_mono hle
    _ = RingHom.ker (CommRingCat.Hom.hom (g.app U.1)) := radical_ringHom_ker_eq _

private theorem ker_eq_vanishingIdeal_of_support {X Y : Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsReduced X] {Z : Closeds ↥Y}
    (hZ : ((Scheme.Hom.ker g).support : Set ↥Y) = (Z : Set ↥Y)) :
    Scheme.Hom.ker g = Scheme.IdealSheafData.vanishingIdeal Z := by
  rw [← vanishingIdeal_congr hZ, Scheme.IdealSheafData.vanishingIdeal_support,
    radical_scheme_ker_eq g]

theorem comap_vanishingIdeal_sUnion {X X' : Scheme.{u}} (f : X' ⟶ X)
    [AlgebraicGeometry.IsReduced X] [AlgebraicGeometry.IsReduced X']
    [NoetherianSpace ↥X] [NoetherianSpace ↥X'] [AlgebraicGeometry.Flat f]
    {S : Set (Set ↥X)} (hS : S ⊆ irreducibleComponents ↥X)
    {Z : Closeds ↥X} (hZ : (Z : Set ↥X) = ⋃₀ S)
    {Z' : Closeds ↥X'} (hZ' : (Z' : Set ↥X') = f.base ⁻¹' (⋃₀ S)) :
    (Scheme.IdealSheafData.vanishingIdeal Z).comap f =
      Scheme.IdealSheafData.vanishingIdeal Z' := by
  have hq1 : QuasiCompact (complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hq2 : QuasiCompact (f ⁻¹ᵁ complSUnionOtherComponents X S).ι :=
    ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hclU : closure ((complSUnionOtherComponents X S : X.Opens) : Set ↥X) = (Z : Set ↥X) := by
    rw [coe_complSUnionOtherComponents, hZ]
    exact closure_compl_sUnion_irreducibleComponents_sdiff hS
  have h1 : (complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU]
    congr 1
    exact Scheme.Opens.range_ι _
  have hclU' :
      closure ((f ⁻¹ᵁ complSUnionOtherComponents X S : X'.Opens) : Set ↥X') = (Z' : Set ↥X') := by
    have hcl : IsClosed (⇑f.base ⁻¹' (⋃₀ S)) := by
      rw [← hZ']; exact Z'.2
    rw [hZ']
    show closure (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ))
        = ⇑f.base ⁻¹' (⋃₀ S)
    apply Set.Subset.antisymm
    · exact closure_minimal
        (Set.preimage_mono (compl_sUnion_irreducibleComponents_sdiff_subset S)) hcl
    · intro x' hx'
      have hx'' : f.base x' ∈ ⋃₀ S := hx'
      obtain ⟨C, hCS, hfx⟩ := hx''
      have hCcomp : C ∈ irreducibleComponents ↥X := hS hCS
      obtain ⟨η, hη⟩ :=
        QuasiSober.sober hCcomp.1 (isClosed_of_mem_irreducibleComponents C hCcomp)
      have hηU : η ∈ (⋃₀ (irreducibleComponents ↥X \ S))ᶜ := by
        rintro ⟨D, ⟨hDcomp, hDS⟩, hηD⟩
        have hCsubD : C ⊆ D := by
          rw [← hη]
          exact (isClosed_of_mem_irreducibleComponents D hDcomp).closure_subset_iff.mpr
            (Set.singleton_subset_iff.mpr hηD)
        have hDsubC : D ⊆ C := hCcomp.2 hDcomp.1 hCsubD
        exact hDS (Set.Subset.antisymm hCsubD hDsubC ▸ hCS)
      have hspec : η ⤳ f.base x' := by
        rw [specializes_iff_mem_closure, hη]
        exact hfx
      obtain ⟨y', hy'spec, hy'eq⟩ := AlgebraicGeometry.Flat.generalizingMap f hspec
      have hy'mem : f.base y' ∈ ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ) := by
        rw [hy'eq]; exact hηU
      have hy'mem2 : y' ∈ (⇑f.base ⁻¹' ((⋃₀ (irreducibleComponents ↥X \ S))ᶜ)) := hy'mem
      exact closure_mono (Set.singleton_subset_iff.mpr hy'mem2)
        (specializes_iff_mem_closure.mp hy'spec)
  have h2 : (f ⁻¹ᵁ complSUnionOtherComponents X S).ι.ker = Scheme.IdealSheafData.vanishingIdeal Z' := by
    apply ker_eq_vanishingIdeal_of_support
    rw [Scheme.Hom.support_ker, ← hclU']
    congr 1
    exact Scheme.Opens.range_ι _
  have hpb := isPullback_morphismRestrict f (complSUnionOtherComponents X S)
  have h4 := ker_eq_comap_ker_of_isPullback_of_flat hpb
  rw [← h1, ← h2, h4]

end FunctorialResolution.EmbeddedResolution
end

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_isPullback_subschemeι_comap {X X' : Scheme.{u}} (f : X' ⟶ X)
    (I : X.IdealSheafData) :
    ∃ g : (I.comap f).subscheme ⟶ I.subscheme,
      g ≫ I.subschemeι = (I.comap f).subschemeι ≫ f ∧
        IsPullback g (I.comap f).subschemeι I.subschemeι f := by
  have hker : Scheme.Hom.ker (I.comap f).subschemeι
      = Scheme.Hom.ker (pullback.fst f I.subschemeι) :=
    (Scheme.IdealSheafData.ker_subschemeι _).trans rfl
  obtain ⟨u, hufac⟩ : ∃ u : (I.comap f).subscheme ⟶ pullback f I.subschemeι,
      u ≫ pullback.fst f I.subschemeι = (I.comap f).subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.ge, IsClosedImmersion.lift_fac _ _ hker.ge⟩
  obtain ⟨v, hvfac⟩ : ∃ v : pullback f I.subschemeι ⟶ (I.comap f).subscheme,
      v ≫ (I.comap f).subschemeι = pullback.fst f I.subschemeι :=
    ⟨IsClosedImmersion.lift _ _ hker.le, IsClosedImmersion.lift_fac _ _ hker.le⟩
  have huv : u ≫ v = 𝟙 _ := by
    apply (cancel_mono (I.comap f).subschemeι).1
    rw [Category.assoc, hvfac, hufac, Category.id_comp]
  have hvu : v ≫ u = 𝟙 _ := by
    apply (cancel_mono (pullback.fst f I.subschemeι)).1
    rw [Category.assoc, hufac, hvfac, Category.id_comp]
  have hw : (I.comap f).subschemeι ≫ f
      = (u ≫ pullback.snd f I.subschemeι) ≫ I.subschemeι := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, hufac]
  refine ⟨u ≫ pullback.snd f I.subschemeι, hw.symm, ?_⟩
  exact (IsPullback.of_iso_pullback ⟨hw⟩
    (⟨u, v, huv, hvu⟩ : (I.comap f).subscheme ≅ pullback f I.subschemeι) hufac rfl).flip

variable {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}} [AlgebraicGeometry.IsAffine Y]
  {pY : Y ⟶ Spec (CommRingCat.of k)} [AlgebraicGeometry.LocallyOfFiniteType pY]
  {k' : Type u} [Field k'] [CharZero k'] {Y' : Scheme.{u}} [AlgebraicGeometry.IsAffine Y']
  {pY' : Y' ⟶ Spec (CommRingCat.of k')} [AlgebraicGeometry.LocallyOfFiniteType pY']

namespace EmbeddedBlowupSequence

theorem noetherianSpace_strictTransform (S : EmbeddedBlowupSequence k Y pY) (i : ℕ) (hi : i ≤ S.length) :
    TopologicalSpace.NoetherianSpace ↥(S.strictTransform i) := by
  have : AlgebraicGeometry.IsNoetherian (S.schemeAt i) := S.isNoetherian_schemeAt i hi
  exact S.noetherianSpace_strictTransform_of_noetherianSpace_schemeAt i inferInstance

theorem isReduced_strictTransform (S : EmbeddedBlowupSequence k Y pY) [AlgebraicGeometry.IsReduced Y]
    (i : ℕ) (hi : i ≤ S.length) : AlgebraicGeometry.IsReduced (S.strictTransform i) :=
  S.isReduced_strictTransform_of_isNoetherian (fun j hj => S.isNoetherian_schemeAt j hj) i hi

end EmbeddedBlowupSequence

namespace ChartFlatBaseChange

variable {S : EmbeddedBlowupSequence k Y pY} {S' : EmbeddedBlowupSequence k' Y' pY'}

theorem mem_support_ambientCenter_iff (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length)
    (y : ↥(S'.strictTransform j)) :
    (S'.strictTransformι j) y ∈ (↑(S'.ambientCenter j).support : Set ↥(S'.schemeAt j)) ↔
      (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y) ∈
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j))) := by
  have hcomp : (S.strictTransformι (F.reindex j)) ((F.strictTransformComparison j hj.le) y)
      = (F.levelMap j hj.le) ((S'.strictTransformι j) y) :=
    congrArg (fun f : S'.strictTransform j ⟶ S.schemeAt (F.reindex j) => f y)
      (F.strictTransformComparison_comp_strictTransformι j hj.le)
  rw [F.center_eq j hj, FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hcomp]

theorem detachedLocus_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.detachedLocus j =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        S.detachedLocus (F.reindex j) := by
  have := F.flat_strictTransformComparison j hj.le
  have himg := F.mem_support_ambientCenter_iff j hj
  have hclosed : IsClosed
      ((fun z : ↥(S.strictTransform (F.reindex j)) => (S.strictTransformι (F.reindex j)) z) ⁻¹'
        (↑(S.ambientCenter (F.reindex j)).support : Set ↥(S.schemeAt (F.reindex j)))) := by
    rw [← FunctorialResolution.EmbeddedResolution.support_comap]
    exact ((S.ambientCenter (F.reindex j)).comap (S.strictTransformι (F.reindex j))).support.2
  refine Set.ext fun x => ?_
  simp only [Set.mem_preimage, S'.detachedLocus_eq_sUnion j, S.detachedLocus_eq_sUnion (F.reindex j), Set.mem_sUnion]
  constructor
  · rintro ⟨C', hC', hxC'⟩
    rw [S'.mem_detachedComponents] at hC'
    obtain ⟨hirr, hsub⟩ := hC'
    refine ⟨closure ((fun z : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) z) '' C'), ?_, ?_⟩
    · rw [S.mem_detachedComponents]
      refine ⟨FunctorialResolution.EmbeddedResolution.closure_image_mem_irreducibleComponents_of_flat _ hirr, ?_⟩
      rw [Set.image_subset_iff]
      refine closure_minimal ?_ hclosed
      rintro _ ⟨y, hy, rfl⟩
      exact (himg y).1 (hsub ⟨y, hy, rfl⟩)
    · exact subset_closure ⟨x, hxC', rfl⟩
  · rintro ⟨C, hC, hxC⟩
    rw [S.mem_detachedComponents] at hC
    obtain ⟨hirr, hsub⟩ := hC
    obtain ⟨C', hC'irr, hxC', hcl⟩ :=
      (FunctorialResolution.EmbeddedResolution.apply_mem_irreducibleComponent_iff_of_flat (F.strictTransformComparison j hj.le) hirr x).1 hxC
    refine ⟨C', ?_, hxC'⟩
    rw [S'.mem_detachedComponents]
    refine ⟨hC'irr, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    refine (himg y).2 ?_
    have hgy : (F.strictTransformComparison j hj.le) y ∈ C := by
      rw [← hcl]
      exact subset_closure ⟨y, hy, rfl⟩
    exact hsub ⟨_, hgy, rfl⟩

theorem coe_detachedClosure_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j)) =
      (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  rw [S'.detachedClosure_coe j, S.detachedClosure_coe (F.reindex j), F.detachedLocus_eq_preimage j hj]

theorem detachedIdeal_eq_comap (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedIdeal j = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) := by
  have : TopologicalSpace.NoetherianSpace ↥(S'.strictTransform j) :=
    S'.noetherianSpace_strictTransform j hj.le
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform (F.reindex j)) :=
    S.noetherianSpace_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := S'.isReduced_strictTransform j hj.le
  have := S.isReduced_strictTransform (F.reindex j) (F.reindex_le_length hj.le)
  have := F.flat_strictTransformComparison j hj.le
  have hS : S.detachedComponents (F.reindex j) ⊆
      irreducibleComponents ↥(S.strictTransform (F.reindex j)) :=
    fun C hC => ((S.mem_detachedComponents (F.reindex j) C).1 hC).1
  have hZ : (↑(S.detachedClosure (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j)))
      = ⋃₀ S.detachedComponents (F.reindex j) := by
    rw [S.detachedClosure_coe (F.reindex j)]
    exact S.detachedLocus_eq_sUnion (F.reindex j)
  have hZ' : (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))
      = ⇑(F.strictTransformComparison j hj.le).base ⁻¹' (⋃₀ S.detachedComponents (F.reindex j)) := by
    have h := F.coe_detachedClosure_eq_preimage j hj
    rw [S.detachedClosure_coe (F.reindex j), S.detachedLocus_eq_sUnion (F.reindex j)] at h
    exact h
  rw [S'.detachedIdeal_eq j, S.detachedIdeal_eq (F.reindex j)]
  exact (comap_vanishingIdeal_sUnion (F.strictTransformComparison j hj.le)
    (S := S.detachedComponents (F.reindex j)) (Z := S.detachedClosure (F.reindex j))
    (Z' := S'.detachedClosure j) hS hZ hZ').symm

theorem exists_isPullback_detachedScheme (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    ∃ g : S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j),
      g ≫ S.detachedι (F.reindex j) = S'.detachedι j ≫ F.strictTransformComparison j hj.le ∧
        IsPullback g (S'.detachedι j) (S.detachedι (F.reindex j)) (F.strictTransformComparison j hj.le) := by
  have key : ∀ J : (S'.strictTransform j).IdealSheafData,
      J = (S.detachedIdeal (F.reindex j)).comap (F.strictTransformComparison j hj.le) →
      ∃ g : J.subscheme ⟶ (S.detachedIdeal (F.reindex j)).subscheme,
        g ≫ (S.detachedIdeal (F.reindex j)).subschemeι =
            J.subschemeι ≫ F.strictTransformComparison j hj.le ∧
          IsPullback g J.subschemeι (S.detachedIdeal (F.reindex j)).subschemeι
            (F.strictTransformComparison j hj.le) := by
    rintro J rfl
    exact exists_isPullback_subschemeι_comap _ _
  exact key (S'.detachedIdeal j) (F.detachedIdeal_eq_comap j hj)

def detachedSchemeComparison (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    S'.detachedScheme j ⟶ S.detachedScheme (F.reindex j) :=
  (F.exists_isPullback_detachedScheme j hj).choose

theorem detachedSchemeComparison_comp_detachedι (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.1

theorem detachedSchemeComparison_comp_detachedι_assoc (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) {Z : Scheme.{u}}
    (h : S.strictTransform (F.reindex j) ⟶ Z) :
    F.detachedSchemeComparison j hj ≫ S.detachedι (F.reindex j) ≫ h =
      S'.detachedι j ≫ F.strictTransformComparison j hj.le ≫ h := by
  rw [← Category.assoc, F.detachedSchemeComparison_comp_detachedι j hj, Category.assoc]

theorem isPullback_detachedSchemeComparison (F : ChartFlatBaseChange S S') [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsReduced Y'] (j : ℕ) (hj : j < S'.length) :
    IsPullback (F.detachedSchemeComparison j hj) (S'.detachedι j) (S.detachedι (F.reindex j))
      (F.strictTransformComparison j hj.le) :=
  (F.exists_isPullback_detachedScheme j hj).choose_spec.2

theorem detachedClosureCompl_eq_preimage (F : ChartFlatBaseChange S S') (j : ℕ) (hj : j < S'.length) :
    S'.detachedClosureCompl j = (F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)) := by
  refine TopologicalSpace.Opens.ext ?_
  have h1 : (↑(S'.detachedClosureCompl j) : Set ↥(S'.strictTransform j))
      = (↑(S'.detachedClosure j) : Set ↥(S'.strictTransform j))ᶜ := S'.detachedClosureCompl_coe j
  have h2 : (↑((F.strictTransformComparison j hj.le) ⁻¹ᵁ (S.detachedClosureCompl (F.reindex j)))
        : Set ↥(S'.strictTransform j))
      = (fun x : ↥(S'.strictTransform j) => (F.strictTransformComparison j hj.le) x) ⁻¹'
        (↑(S.detachedClosureCompl (F.reindex j)) : Set ↥(S.strictTransform (F.reindex j))) := rfl
  rw [h1, h2, S.detachedClosureCompl_coe (F.reindex j), Set.preimage_compl,
    F.coe_detachedClosure_eq_preimage j hj]

theorem isEmpty_of_forall_reindex_ne (F : ChartFlatBaseChange S S') (s : ℕ) (hs : s < S.length)
    (hskip : ∀ j, j < S'.length → F.reindex j ≠ s) (P : Scheme.{u})
    (q : P ⟶ S.detachedScheme s) (p : P ⟶ S'.ambient)
    (hcomm : q ≫ S.detachedι s ≫ S.strictTransformι s ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap) :
    IsEmpty ↥P := by
  have : TopologicalSpace.NoetherianSpace ↥(S.strictTransform s) :=
    S.noetherianSpace_strictTransform s hs.le
  constructor
  intro x
  have hcsq : (q ≫ S.detachedι s ≫ S.strictTransformι s) ≫ S.ambientSeq.projectionToBase s = p ≫ F.ambientMap := by
    simp only [Category.assoc]
    exact hcomm
  have hpb := IsPullback.of_hasPullback (S.ambientSeq.projectionToBase s) F.ambientMap
  have hcomap := F.comap_center_skipped s hs hskip
    (pullback (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)
    (pullback.snd (S.ambientSeq.projectionToBase s) F.ambientMap) hpb
  have hwf : hpb.lift _ _ hcsq ≫ pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap
      = q ≫ S.detachedι s ≫ S.strictTransformι s := hpb.lift_fst _ _ hcsq
  have hpt : (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap) ((hpb.lift _ _ hcsq) x)
      = (S.strictTransformι s) ((S.detachedι s) (q x)) :=
    congrArg (fun f : P ⟶ S.schemeAt s => f x) hwf
  have hfl : (S.detachedι s) (q x) ∈ S.detachedLocus s := by
    have h1 : (S.detachedι s) (q x) ∈ (↑(S.detachedIdeal s).support : Set ↥(S.strictTransform s)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨q x, rfl⟩
    rw [S.detachedIdeal_eq s] at h1
    have h2 := (Scheme.IdealSheafData.coe_support_vanishingIdeal (S.detachedClosure s)).le h1
    rw [S.detachedClosure_coe s] at h2
    exact h2
  have hmem : (S.strictTransformι s) ((S.detachedι s) (q x)) ∈
      (↑(S.ambientCenter s).support : Set ↥(S.schemeAt s)) :=
    S.image_detachedLocus_subset_ambientCenter_support s ⟨_, hfl, rfl⟩
  have hmem2 : (hpb.lift _ _ hcsq) x ∈ (↑((S.ambientCenter s).comap
      (pullback.fst (S.ambientSeq.projectionToBase s) F.ambientMap)).support
        : Set ↥(pullback (S.ambientSeq.projectionToBase s) F.ambientMap)) := by
    rw [FunctorialResolution.EmbeddedResolution.support_comap, Set.mem_preimage, hpt]
    exact hmem
  rw [hcomap] at hmem2
  simp at hmem2

end ChartFlatBaseChange

end FunctorialResolution.EmbeddedResolution

end
end
