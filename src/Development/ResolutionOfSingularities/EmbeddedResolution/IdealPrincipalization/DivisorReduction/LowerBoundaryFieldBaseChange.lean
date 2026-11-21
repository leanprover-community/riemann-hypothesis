import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties

section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem le_ker_comp_subschemeι {X : Scheme.{u}} (D : X.IdealSheafData) {W : Scheme.{u}}
    (g : W ⟶ D.subscheme) : D ≤ AlgebraicGeometry.Scheme.Hom.ker (g ≫ D.subschemeι) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι D).ge.trans
    (AlgebraicGeometry.Scheme.Hom.le_ker_comp g _)

abbrev boundaryComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) :
    Set ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
  {x | connectedComponent x ⊆
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' FunctorialResolution.EmbeddedResolution.orderAtLeastLocus T.ideal T.mult}

abbrev boundaryComponentsInOrderLocusOpens (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length)
    (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    (T.boundary.get ⟨j, hj⟩).subscheme.Opens :=
  ⟨boundaryComponentsInOrderLocus T j hj, h⟩

theorem one_le_mult_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) : 1 ≤ T.mult :=
  hV.one_le_mult

theorem isSmoothDivisor_boundary_comap_isoObjZero (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) (s : T.SequenceOfBlowups) :
    IsSmoothDivisor (s.projectionToSpec 0) ((T.boundary.get ⟨j, hj⟩).comap s.isoZero.hom) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := by
    simp only [List.get_eq_getElem]
    exact List.getElem_mem hj
  have hD : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).1 hV.snc).1 _ hmem
  rw [MarkedSequenceOfBlowups.projectionToSpec_zero]
  exact PrincipalizationIsoTransport.isSmoothDivisor_comap_iso T.structMap s.toSequenceOfBlowups.isoZero _ hD

theorem containedComponentsIdeal_eq_ker_of_isOpen (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj =
      AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :=
  containedComponentsIdeal_eq_ker_ι_comp_subschemeι_of_isOpen T j hj h

theorem containedComponentsIdeal_eq_top_of_not_isOpen_locus (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (h : ¬ IsOpen (boundaryComponentsInOrderLocus T j hj)) :
    containedComponentsIdeal T j hj = ⊤ :=
  containedComponentsIdeal_eq_top_of_not_isOpen_setOf_connectedComponent T j hj h

theorem support_containedComponentsIdeal_subset_support_boundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) :
    ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) ⊆
      ((T.boundary.get ⟨j, hj⟩).support : Set ↥T.scheme) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h]
    exact SetLike.coe_subset_coe.mpr
      (AlgebraicGeometry.Scheme.IdealSheafData.support_antitone
        (le_ker_comp_subschemeι (T.boundary.get ⟨j, hj⟩) (boundaryComponentsInOrderLocusOpens T j hj h).ι))
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot]
    exact Set.empty_subset _

def PreimageSupportEqComponentsInOrderLocus (T : MarkedIdealWithBoundary.{u}) (j : ℕ) (hj : j < T.boundary.length) : Prop :=
  ∀ h : IsOpen (boundaryComponentsInOrderLocus T j hj),
    ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
        ((AlgebraicGeometry.Scheme.Hom.ker
            ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
              (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme) =
      boundaryComponentsInOrderLocus T j hj

theorem isOpen_preimage_support_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (hc : PreimageSupportEqComponentsInOrderLocus T j hj) :
    IsOpen (⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹'
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme)) := by
  by_cases h : IsOpen (boundaryComponentsInOrderLocus T j hj)
  · rw [containedComponentsIdeal_eq_ker_of_isOpen T j hj h, hc h]
    exact h
  · rw [containedComponentsIdeal_eq_top_of_not_isOpen_locus T j hj h,
      AlgebraicGeometry.Scheme.IdealSheafData.support_top, TopologicalSpace.Closeds.coe_bot,
      Set.preimage_empty]
    exact isOpen_empty

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end

section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem sameNontrivialBoundary_take_eraseIdx_comap {X Y : Scheme.{u}} (p : Y ⟶ X)
    (B : List X.IdealSheafData) (E' : List Y.IdealSheafData) (j : ℕ)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap p) B) E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (List.map (fun D => D.comap p) B))
    (hj : j < B.length) (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.take (E'.length - 1) (E'.eraseIdx j))
      (List.map (fun D => D.comap p) (List.take (B.length - 1) (B.eraseIdx j))) := by
  have hE : List.take (E'.length - 1) (E'.eraseIdx j) = E'.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hjE))
  have hB : List.take (B.length - 1) (B.eraseIdx j) = B.eraseIdx j :=
    List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))
  rw [hE, hB, ← List.eraseIdx_map]
  exact hBE.symm.eraseIdx j htake

private theorem isClosed_setOf_connectedComponent_subset {X : Type u} [TopologicalSpace X]
    (hop : ∀ x : X, IsOpen (connectedComponent x)) (P : Set X) :
    IsClosed {x : X | connectedComponent x ⊆ P} := by
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro x hx
  refine ⟨connectedComponent x, ?_, hop x, mem_connectedComponent⟩
  intro y hy
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq] at hx ⊢
  intro hsub
  apply hx
  rw [connectedComponent_eq hy]
  exact hsub

theorem lowerBoundaryWithoutBlowup_baseChange_sameNontrivialBoundary (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (K : Type u) [Field K] [CharZero K] (f : T.base →+* K)
    (E' : List (T.baseChange K f).scheme.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (T.baseChange K f).boundary E')
    (htake : List.take (j + 1) E' = List.take (j + 1) (T.baseChange K f).boundary)
    (hjE : j < E'.length) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E'.length - 1)
        ((lowerBoundaryWithoutBlowup ((T.baseChange K f).withBoundary E')).eraseIdx j))
      (List.map (fun D => D.comap (fieldBaseChangeProjection T K f))
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  rw [lowerBoundaryWithoutBlowup_eq ((T.baseChange K f).withBoundary E'), lowerBoundaryWithoutBlowup_eq T]
  exact sameNontrivialBoundary_take_eraseIdx_comap (fieldBaseChangeProjection T K f) T.boundary E' j hBE htake hj hjE

theorem preimageSupportEqComponentsInOrderLocus_of_isAdmissible (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) : PreimageSupportEqComponentsInOrderLocus T j hj := by
  intro h
  have := hV.isNoetherian
  have := FunctorialResolution.Blowup.noetherianSpace_subscheme (T.boundary.get ⟨j, hj⟩)
  have hnsU : TopologicalSpace.NoetherianSpace
      ↥((boundaryComponentsInOrderLocusOpens T j hj h).toScheme) :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace ↥(boundaryComponentsInOrderLocus T j hj))
  have hqc : AlgebraicGeometry.QuasiCompact
      ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) := by
    constructor
    intro V _ _
    exact TopologicalSpace.NoetherianSpace.isCompact _
  have hclosed : IsClosed (boundaryComponentsInOrderLocus T j hj) :=
    isClosed_setOf_connectedComponent_subset
      (fun x => Blowup.isOpen_connectedComponent_of_noetherianSpace _ x) _
  have hinj : Function.Injective ⇑(T.boundary.get ⟨j, hj⟩).subschemeι :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).injective
  have himg : IsClosed (⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj) :=
    (Scheme.Hom.isClosedEmbedding (T.boundary.get ⟨j, hj⟩).subschemeι).isClosedMap _ hclosed
  have hU : Set.range ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι = boundaryComponentsInOrderLocus T j hj :=
    Scheme.Opens.range_ι _
  have hcomp : ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
      = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ∘ ⇑(boundaryComponentsInOrderLocusOpens T j hj h).ι := by
    funext x
    simp
  have hrange :
      Set.range ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
        = ⇑(T.boundary.get ⟨j, hj⟩).subschemeι '' boundaryComponentsInOrderLocus T j hj := by
    rw [hcomp, Set.range_comp, hU]
  have hsupp : ((AlgebraicGeometry.Scheme.Hom.ker
        ((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫
          (T.boundary.get ⟨j, hj⟩).subschemeι)).support : Set ↥T.scheme)
      = closure (Set.range
          ⇑((boundaryComponentsInOrderLocusOpens T j hj h).ι ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
  rw [hsupp, hrange, himg.closure_eq]
  exact Set.preimage_image_eq _ hinj

end DivisorReduction

end FunctorialResolution.EmbeddedResolution
end
