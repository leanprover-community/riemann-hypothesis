import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherianStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfRatPoint
import BuildAid.ForwardExisting

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem geometricallyConnected_of_smooth_of_section :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      (e : Spec (CommRingCat.of k) ⟶ X),
      Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  intro k _ X f e _ he _
  exact GlobalTheory.RatPointConn.of_section f e he

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricallyConnected_of_smooth_of_section' : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → ConnectedSpace X → GeometricallyConnected f := by
  atlas_forward_decl GlobalTheory.geometricallyConnected_of_smooth_of_section
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem preimage_connectedComponent_rationalPoint_baseChange : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  intro k k' _ _ X X' f f' p q e e' hf hP he he' hq
  have hN : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  set x : X := e (IsLocalRing.closedPoint k) with hx
  set x' : X' := e' (IsLocalRing.closedPoint k') with hx'
  have hopen : IsOpen (connectedComponent x) := GlobalTheory.T.isOpen_connectedComponent_of_isLocallyNoetherian' X hN x
  let U : X.Opens := ⟨connectedComponent x, hopen⟩
  have hsub : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have hrange : Set.range e ⊆ Set.range U.ι := by
    rintro _ ⟨y, rfl⟩
    rw [Scheme.Opens.range_ι, Subsingleton.elim y (IsLocalRing.closedPoint k)]
    exact mem_connectedComponent
  let eU : Spec (CommRingCat.of k) ⟶ U.toScheme := IsOpenImmersion.lift U.ι e hrange
  have heU : eU ≫ U.ι = e := IsOpenImmersion.lift_fac _ _ _
  have hUc : ConnectedSpace U.toScheme :=
    isConnected_iff_connectedSpace.mp (isConnected_connectedComponent (x := x))
  have hgc : GeometricallyConnected (U.ι ≫ f) :=
    GlobalTheory.T.geometricallyConnected_of_smooth_of_section' k U.toScheme (U.ι ≫ f) eU inferInstance (by rw [← Category.assoc, heU, he]) hUc
  have hP1 : IsPullback (q ∣_ U) (q ⁻¹ᵁ U).ι U.ι q := isPullback_morphismRestrict q U
  have hP2 : IsPullback (q ∣_ U) ((q ⁻¹ᵁ U).ι ≫ f') (U.ι ≫ f) p := hP1.paste_vert hP
  have hc : ConnectedSpace (q ⁻¹ᵁ U).toScheme :=
    GeometricallyConnected.geometrically_connectedSpace (f := U.ι ≫ f) p _ _ hP2
  have hc' : _root_.IsConnected (q ⁻¹' connectedComponent x) :=
    isConnected_iff_connectedSpace.mpr hc
  have hmem : x' ∈ q ⁻¹' connectedComponent x := by
    have : q x' = x := by
      have h1 : q x' = (e' ≫ q) (IsLocalRing.closedPoint k') := rfl
      have h2 : (p ≫ e) (IsLocalRing.closedPoint k') = e (p (IsLocalRing.closedPoint k')) := rfl
      rw [h1, hq, h2]
      exact congrArg e (Subsingleton.elim _ _)
    rw [Set.mem_preimage, this]
    exact mem_connectedComponent
  have hclopen : IsClopen (q ⁻¹' connectedComponent x) :=
    IsClopen.preimage ⟨isClosed_connectedComponent, hopen⟩ q.continuous
  exact Set.Subset.antisymm (hc'.subset_connectedComponent hmem)
    (hclopen.connectedComponent_subset hmem)

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt : ∀ (k k' : Type) [Field k] [Field k'] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (f' : X' ⟶ Spec (CommRingCat.of k')) (p : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of k)) (q : X' ⟶ X) (e : Spec (CommRingCat.of k) ⟶ X) (e' : Spec (CommRingCat.of k') ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' connectedComponent (e (IsLocalRing.closedPoint k)) = connectedComponent (e' (IsLocalRing.closedPoint k')) := by
  atlas_forward_decl GlobalTheory.preimage_connectedComponent_rationalPoint_baseChange
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem image_connectedComponent_of_isEmbedding {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    {q : A → B} (hq : Topology.IsEmbedding q) (a : A) :
    q '' connectedComponent a = connectedComponentIn (Set.range q) (q a) := by
  apply Set.Subset.antisymm
  · exact (isPreconnected_connectedComponent.image q hq.continuous.continuousOn).subset_connectedComponentIn
      ⟨a, mem_connectedComponent, rfl⟩ (Set.image_subset_range _ _)
  · intro x hx
    have hsub : connectedComponentIn (Set.range q) (q a) ⊆ Set.range q := connectedComponentIn_subset _ _
    have himg : q '' (q ⁻¹' connectedComponentIn (Set.range q) (q a)) = connectedComponentIn (Set.range q) (q a) :=
      Set.image_preimage_eq_of_subset hsub
    have hpc : IsPreconnected (q ⁻¹' connectedComponentIn (Set.range q) (q a)) := by
      rw [← hq.isInducing.isPreconnected_image, himg]
      exact isPreconnected_connectedComponentIn
    have hS : q ⁻¹' connectedComponentIn (Set.range q) (q a) ⊆ connectedComponent a :=
      hpc.subset_connectedComponent (mem_connectedComponentIn ⟨a, rfl⟩)
    rw [← himg] at hx
    exact Set.image_mono hS hx

theorem component_in_fibre_iff_of_isPullback :
    ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s))
      (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s →
      ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  intro X S f e s Y g q y₀ hP h0 y
  haveI : IsPreimmersion q :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) hP.flip inferInstance
  have hq : Topology.IsEmbedding q := q.isEmbedding
  have hr : Set.range q = f ⁻¹' {s} := by
    have h1 : Set.range q = Set.range (pullback.fst f (S.fromSpecResidueField s)) := by
      rw [← hP.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        Set.range_eq_univ.mpr, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hP.isoPullback)).surjective
    rw [h1, Scheme.Pullback.range_fst, Scheme.range_fromSpecResidueField]
  rw [← h0, ← hr, ← image_connectedComponent_of_isEmbedding hq]
  exact hq.injective.mem_set_image

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (e : S ⟶ X) (s : S) (Y : Scheme.{0}) (g : Y ⟶ Spec (S.residueField s)) (q : Y ⟶ X) (y₀ : Y), IsPullback q g f (S.fromSpecResidueField s) → q y₀ = e s → ∀ y : Y, q y ∈ connectedComponentIn (f ⁻¹' {s}) (e s) ↔ y ∈ connectedComponent y₀ := by
  atlas_forward_decl GlobalTheory.component_in_fibre_iff_of_isPullback
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem sectionComponents_preimage_of_isPullback :
    ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X)
      (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ →
      e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e →
      q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} =
        {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  intro X S X' S' f f' p q e e' hf hq he he' hee
  ext x'
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hfq : f (q x') = p (f' x') := by
    rw [← Scheme.Hom.comp_apply, hq.w, Scheme.Hom.comp_apply]
  rw [hfq]

  have hY := IsPullback.of_hasPullback f (S.fromSpecResidueField (p (f' x')))
  have hY' := IsPullback.of_hasPullback f' (S'.fromSpecResidueField (f' x'))
  have hsq : S'.fromSpecResidueField (f' x') ≫ p =
      Spec.map (p.residueFieldMap (f' x')) ≫ S.fromSpecResidueField (p (f' x')) :=
    (Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField p (f' x')).symm

  let eY : Spec (S.residueField (p (f' x'))) ⟶ pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (S.fromSpecResidueField (p (f' x')) ≫ e) (𝟙 _) (by simp [he])
  let eY' : Spec (S'.residueField (f' x')) ⟶ pullback f' (S'.fromSpecResidueField (f' x')) :=
    pullback.lift (S'.fromSpecResidueField (f' x') ≫ e') (𝟙 _) (by simp [he'])

  let r : pullback f' (S'.fromSpecResidueField (f' x')) ⟶
      pullback f (S.fromSpecResidueField (p (f' x'))) :=
    pullback.lift (pullback.fst _ _ ≫ q) (pullback.snd _ _ ≫ Spec.map (p.residueFieldMap (f' x')))
      (by simp only [Category.assoc]; rw [hq.w, ← Category.assoc, pullback.condition, Category.assoc, hsq])
  have hbig := hY'.paste_horiz hq
  have hr : IsPullback r (pullback.snd _ _) (pullback.snd _ _)
      (Spec.map (p.residueFieldMap (f' x'))) := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) hY
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    rw [h1, ← hsq]
    exact hbig
  have hsec : eY ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hsec' : eY' ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have hcomm : eY' ≫ r = Spec.map (p.residueFieldMap (f' x')) ≫ eY := by
    apply pullback.hom_ext
    · simp only [r, eY, eY', Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc]
      rw [hee, reassoc_of% hsq]
    · simp only [r, eY, eY', Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc, Category.id_comp, Category.comp_id]
  have hsm : Smooth (pullback.snd f (S.fromSpecResidueField (p (f' x')))) := inferInstance
  have key := GlobalTheory.T.preimage_connectedComponent_rationalPoint_fieldExt (S.residueField (p (f' x'))) (S'.residueField (f' x')) _ _
    (pullback.snd _ _) (pullback.snd _ _) (Spec.map (p.residueFieldMap (f' x'))) r eY eY'
    hsm hr hsec hsec' hcomm

  obtain ⟨y', hy'1, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f') (g := S'.fromSpecResidueField (f' x')) x' (IsLocalRing.closedPoint _)
    (Scheme.fromSpecResidueField_apply _ _).symm
  have hy₀ : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (eY (IsLocalRing.closedPoint _)) =
      e (p (f' x')) := by
    have h1 : eY ≫ pullback.fst _ _ = S.fromSpecResidueField (p (f' x')) ≫ e := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e (Scheme.fromSpecResidueField_apply _ _))
  have hy₀' : pullback.fst f' (S'.fromSpecResidueField (f' x')) (eY' (IsLocalRing.closedPoint _)) =
      e' (f' x') := by
    have h1 : eY' ≫ pullback.fst _ _ = S'.fromSpecResidueField (f' x') ≫ e' := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply eY' (pullback.fst _ _) _).symm.trans ?_
    rw [h1]
    exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg e' (Scheme.fromSpecResidueField_apply _ _))
  have hqx : pullback.fst f (S.fromSpecResidueField (p (f' x'))) (r y') = q x' := by
    have h1 : r ≫ pullback.fst _ _ = pullback.fst _ _ ≫ q := pullback.lift_fst _ _ _
    refine (Scheme.Hom.comp_apply r (pullback.fst _ _) _).symm.trans ?_
    rw [h1, Scheme.Hom.comp_apply, hy'1]
  have A := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X S f e (p (f' x')) _ (pullback.snd _ _) (pullback.fst _ _) _ hY hy₀ (r y')
  have B := GlobalTheory.T.mem_connectedComponentIn_fibre_iff_of_isPullback X' S' f' e' (f' x') _ (pullback.snd _ _) (pullback.fst _ _) _ hY' hy₀' y'
  rw [hqx] at A
  rw [hy'1] at B
  rw [A, B, ← key]
  rfl

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preimage_section_connectedComponentIn_of_isPullback : ∀ (X S X' S' : Scheme.{0}) (f : X ⟶ S) (f' : X' ⟶ S') (p : S' ⟶ S) (q : X' ⟶ X) (e : S ⟶ X) (e' : S' ⟶ X'), Smooth f → IsPullback q f' f p → e ≫ f = 𝟙 _ → e' ≫ f' = 𝟙 _ → e' ≫ q = p ≫ e → q ⁻¹' {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} = {x : X' | x ∈ connectedComponentIn (f' ⁻¹' {f' x}) (e' (f' x))} := by
  atlas_forward_decl GlobalTheory.sectionComponents_preimage_of_isPullback
end
