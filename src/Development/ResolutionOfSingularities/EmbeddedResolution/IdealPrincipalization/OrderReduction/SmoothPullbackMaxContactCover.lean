import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsAddHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.OrderUnderStalkIsomorphism
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms

section
universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

private theorem map_iInf_of_bijective {A B : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (hφ : Function.Bijective φ) {ι : Type*} (K : ι → Ideal A) :
    Ideal.map φ (⨅ i, K i) = ⨅ i, Ideal.map φ (K i) :=
  (Ideal.relIsoOfBijective φ hφ).symm.map_iInf K

private theorem bijective_appLE_image {A B : Scheme.{u}} (g : A ⟶ B) [IsOpenImmersion g]
    (S : A.Opens) (e : S ≤ g ⁻¹ᵁ (g ''ᵁ S)) :
    Function.Bijective (CommRingCat.Hom.hom (Scheme.Hom.appLE g (g ''ᵁ S) S e)) := by
  have : IsIso (Scheme.Hom.appLE g (g ''ᵁ S) S e) := by
    rw [← Scheme.Hom.appIso_hom' g S]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

private theorem ideal_iInf {X : Scheme.{u}} {ι : Type v} [Finite ι]
    (I : ι → X.IdealSheafData) (U : X.affineOpens) :
    (⨅ i, I i).ideal U = ⨅ i, (I i).ideal U := by
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.ideal_iInf, iInf_apply]

theorem comap_iInf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {ι : Type v} [Finite ι] (J : ι → Y.IdealSheafData) :
    (⨅ i, J i).comap f = ⨅ i, (J i).comap f := by
  refine Scheme.IdealSheafData.ext ?_
  funext V
  have hU : IsAffineOpen (f ''ᵁ (V : X.Opens)) := V.2.image_of_isOpenImmersion f
  have e : (V : X.Opens) ≤ f ⁻¹ᵁ (f ''ᵁ (V : X.Opens)) :=
    (f.preimage_image_eq (V : X.Opens)).ge
  have hbij : Function.Bijective
      (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom :=
    bijective_appLE_image f (V : X.Opens) e
  have key : ∀ I : Y.IdealSheafData, (I.comap f).ideal V =
      (I.ideal ⟨f ''ᵁ (V : X.Opens), hU⟩).map
        (f.appLE (f ''ᵁ (V : X.Opens)) (V : X.Opens) e).hom := fun I =>
    Scheme.IdealSheafData.comap_ideal_eq_map_appLE I f ⟨f ''ᵁ (V : X.Opens), hU⟩ V e
  have h1 : (⨅ i, J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩
      = ⨅ i, (J i).ideal ⟨f ''ᵁ (V : X.Opens), hU⟩ :=
    ideal_iInf J ⟨f ''ᵁ (V : X.Opens), hU⟩
  have h2 : (⨅ i, (J i).comap f).ideal V = ⨅ i, ((J i).comap f).ideal V :=
    ideal_iInf (fun i => (J i).comap f) V
  rw [h2, key (⨅ i, J i), h1, map_iInf_of_bijective _ hbij]
  exact iInf_congr fun i => (key (J i)).symm

theorem ker_subschemeι_comp_comap_self {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] [QuasiCompact f]
    (I : X.IdealSheafData) :
    ((I.subschemeι ≫ f).ker).comap f = I :=
  FunctorialResolution.EmbeddedResolution.comap_ker_subschemeι_comp I f

theorem ker_subschemeι_comp_comap_eq_top_of_disjoint {X X' Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (g : X' ⟶ Y) [QuasiCompact g]
    (hdisj : ∀ (x : ↥X) (x' : ↥X'), f.base x ≠ g.base x') (J : X'.IdealSheafData) :
    ((J.subschemeι ≫ g).ker).comap f = ⊤ := by
  refine FunctorialResolution.Blowup.comap_eq_top_of_notMem_support f ((J.subschemeι ≫ g).ker) ?_
  intro x hx
  have hx' : f.base x ∈ (((J.subschemeι ≫ g).ker).support : Set ↥Y) := hx
  rw [Scheme.Hom.support_ker] at hx'
  have hopen : IsOpen (Set.range ⇑f.base) := f.isOpenEmbedding.isOpen_range
  obtain ⟨y, hy1, hy2⟩ :=
    mem_closure_iff.mp hx' (Set.range ⇑f.base) hopen (Set.mem_range_self x)
  obtain ⟨x₀, hx₀⟩ := hy1
  obtain ⟨w, hw⟩ := hy2
  have hwe : g.base (J.subschemeι.base w) = y := by
    rw [← hw]
    simp
  exact hdisj x₀ (J.subschemeι.base w) (hx₀.trans hwe.symm)

variable (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)

instance instIsClosedImmersionStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    IsClosedImmersion (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.isClosedImmersion_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

theorem quasiCompact_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  FunctorialResolution.Blowup.quasiCompact_sigmaι
    (fun j : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv j) i

instance instQuasiCompactStarι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    QuasiCompact (MaxContactOpenCover.coverPieceι T hv i) :=
  quasiCompact_coverPieceι T hv i

theorem coverPieceι_base_ne_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j)
    (x : ↥(MaxContactOpenCover.coverPiece T hv i)) (y : ↥(MaxContactOpenCover.coverPiece T hv j)) :
    (MaxContactOpenCover.coverPieceι T hv i).base x ≠ (MaxContactOpenCover.coverPieceι T hv j).base y :=
  FunctorialResolution.Blowup.sigmaι_base_ne
    (fun k : (MaxContactCoverData.chosenCoverData T hv).idx => MaxContactOpenCover.coverPiece T hv k) hij x y

theorem ker_subschemeι_comp_coverPieceι_comap_self (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal i).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv i).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i :=
  ker_subschemeι_comp_comap_self (MaxContactOpenCover.coverPieceι T hv i) _

theorem ker_subschemeι_comp_coverPieceι_comap_of_ne {i j : (MaxContactCoverData.chosenCoverData T hv).idx} (hij : i ≠ j) :
    ((((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) = ⊤ :=
  ker_subschemeι_comp_comap_eq_top_of_disjoint (MaxContactOpenCover.coverPieceι T hv i) (MaxContactOpenCover.coverPieceι T hv j)
    (coverPieceι_base_ne_of_ne T hv hij) _

theorem comap_coverMaxContactIdeal_coverPieceι (i : (MaxContactCoverData.chosenCoverData T hv).idx) :
    (MaxContactCoverData.coverMaxContactIdeal T hv).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
  have key : (⨅ j : (MaxContactCoverData.chosenCoverData T hv).idx,
      (((MaxContactCoverData.chosenCoverData T hv).localIdeal j).subschemeι ≫
        MaxContactOpenCover.coverPieceι T hv j).ker).comap (MaxContactOpenCover.coverPieceι T hv i) =
      (MaxContactCoverData.chosenCoverData T hv).localIdeal i := by
    rw [comap_iInf]
    refine le_antisymm (le_trans (iInf_le _ i) (le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv i)))
      (le_iInf fun j => ?_)
    rcases eq_or_ne j i with rfl | h
    · exact le_of_eq (ker_subschemeι_comp_coverPieceι_comap_self T hv _).symm
    · rw [ker_subschemeι_comp_coverPieceι_comap_of_ne T hv h.symm]
      exact le_top
  exact key

theorem isMaxContactHypersurface_coverMaxContactIdeal
    [AlgebraicGeometry.LocallyOfFiniteType (MaxContactCoverData.coverTriple T hv).structMap]
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T)) :
    IsMaxContactHypersurface (MaxContactCoverData.coverTriple T hv).base
      (MaxContactCoverData.coverTriple T hv).structMap (MaxContactCoverData.coverTriple T hv).ideal
      (MaxContactCoverData.tunedMult T) (MaxContactCoverData.coverMaxContactIdeal T hv) :=
  FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_coverMaxContactIdeal_of_comap_eq T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv)

theorem inStrictNormalCrossingPositionAt_of_isMaxContactCover
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (x : ↥(MaxContactCoverData.coverTriple T hv).scheme) :
    InStrictNormalCrossingPositionAt (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] x :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPositionAt_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) x

theorem inStrictNormalCrossingPosition_of_isMaxContactCover
    (hgood : MaxContactReduction.IsMaxContactCover T (MaxContactCoverData.chosenCoverData T hv) hv.locallyOfFiniteType
      (MaxContactCoverData.balancedTunedIdeal T hv) (MaxContactCoverData.tunedMult T))
    (hsm : IsSmoothDivisor (MaxContactCoverData.coverTriple T hv).structMap
      (MaxContactCoverData.coverMaxContactIdeal T hv)) :
    InStrictNormalCrossingPosition (MaxContactCoverData.coverTriple T hv).structMap
      [MaxContactCoverData.coverMaxContactIdeal T hv] :=
  FunctorialResolution.EmbeddedResolution.inStrictNormalCrossingPosition_coverMaxContactIdeal T hv hgood (comap_coverMaxContactIdeal_coverPieceι T hv) hsm

end FunctorialResolution.EmbeddedResolution.MaxContactCoverGeometry

end
end

section
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem orderAt_ideal_le_mult_along_sequence (T : MarkedIdealWithBoundary.{u}) (hT : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (s : T.SequenceOfBlowups) :
    ∀ (i : ℕ), i ≤ s.toSequenceOfBlowups.length →
      ∀ x : ↥(s.toSequenceOfBlowups.schemeAt i), orderAt (s.ideal i) x ≤ (T.mult : ℕ∞) := by
  have : CharZero T.base := hT.charZero
  intro i
  induction i with
  | zero =>
      intro _ x
      have : AlgebraicGeometry.IsOpenImmersion s.toSequenceOfBlowups.isoZero.hom := inferInstance
      rw [s.ideal_zero, orderAt_comap_of_isOpenImmersion]
      exact hord _
  | succ k ih =>
      intro hk x
      have hlt : k < s.toSequenceOfBlowups.length := hk
      have hprev := ih (le_of_lt hlt)
      have hnoeth : AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) :=
        MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hT s (k + 1) hk
      have : AlgebraicGeometry.IsLocallyNoetherian (s.toSequenceOfBlowups.schemeAt (k + 1)) := inferInstance
      have hsmooth : AlgebraicGeometry.Smooth (s.projectionToSpec k) :=
        MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hT s k (le_of_lt hlt)
      have hS : HasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.boundary k) := by
        rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
        exact s.center_snc k hlt
      have hI : s.ideal k ≤ s.toSequenceOfBlowups.center k ^ T.mult :=
        le_pow_of_hasStrictNormalCrossingsWith (s.projectionToSpec k) (s.toSequenceOfBlowups.center k) (s.ideal k)
          (s.boundary k) hS T.mult (s.center_order k hlt)
      have hEq : s.ideal (k + 1) =
          controlledTransform (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
            (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI :=
        eq_controlledTransform_of_mul_eq_comap (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k)
          (s.ideal k) T.mult (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) hI
          (s.ideal (k + 1)) (s.ideal_succ k hlt)
      rw [hEq]
      exact orderAt_controlledTransform_le_of_forall_le T.base (s.projectionToSpec k)
        (s.toSequenceOfBlowups.transitionMapSucc k) (s.toSequenceOfBlowups.center k) (s.boundary k) hS
        (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism k hlt) (s.ideal k) T.mult hI hprev x

end FunctorialResolution.EmbeddedResolution
end

section
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace OrderReduction

def ValidPullbackAlongSmooth : Prop :=
  ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
      (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
      [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
      h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible

theorem validPullbackAlongSmooth_iff :
    ValidPullbackAlongSmooth.{u} ↔
      ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible → ∀ (Y : Scheme.{u})
        (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h] [AlgebraicGeometry.QuasiCompact q],
        h ≫ T.structMap = q → (T.pullbackAlong Y q h).IsAdmissible :=
  Iff.rfl

end OrderReduction

namespace MaxContactCoverData

private theorem support_pow_subset {X : Scheme.{u}} (I : X.IdealSheafData) (s : ℕ) :
    ((I ^ s).support : Set ↥X) ⊆ (I.support : Set ↥X) := by
  intro x hx
  simp only [SetLike.mem_coe] at hx ⊢
  rw [mem_support_iff_stalkIdeal_ne_top] at hx ⊢
  intro hI
  apply hx
  rw [stalkIdeal_pow, hI, Ideal.top_pow]

private theorem prod_map_range_pow_ite_eq_pow {X : Scheme.{u}} (A : ℕ → X.IdealSheafData) (n s : ℕ) :
    (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range (n + 1))).prod = A n ^ s := by
  have h1 : (List.map (fun j => A j ^ (if j = n then s else 0)) (List.range n)).prod = 1 := by
    apply List.prod_eq_one
    intro y hy
    simp only [List.mem_map, List.mem_range] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    rw [if_neg (Nat.ne_of_lt hj), pow_zero]
  rw [List.range_succ, List.map_append, List.prod_append, h1, one_mul]
  simp

private theorem exists_le_and_pow_le_tunedSheaf (k : Type u) [Field k] [IsNoetherianRing k]
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType p] (I : X.IdealSheafData) (m s : ℕ) (hm : 1 ≤ m) :
    ∃ J : X.IdealSheafData, I ≤ J ∧ J ^ s ≤ tunedSheaf k p I m s := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  refine ⟨derivIdealSheafIterate k p n I, le_derivIdealSheafIterate k p n I, ?_⟩
  have h0 : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0))
      = (n + 1 - n) * (if n = n then s else 0) := by
    refine Finset.sum_eq_single n (fun b _ hb => by simp [hb]) (fun h => ?_)
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self n)) h
  have hsum : (∑ j ∈ Finset.range (n + 1), (n + 1 - j) * (if j = n then s else 0)) = s := by
    rw [h0, if_pos rfl, Nat.add_sub_cancel_left, one_mul]
  have h := prod_pow_derivIdealSheafIterate_le_tunedSheaf k p I (n + 1) s
    (fun j => if j = n then s else 0) hsum.ge
  rw [prod_map_range_pow_ite_eq_pow] at h
  exact h

theorem balancedTunedIdeal_eq_balancedTunedSheaf (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    [AlgebraicGeometry.LocallyOfFiniteType T.structMap] :
    balancedTunedIdeal T hv = FunctorialResolution.EmbeddedResolution.balancedTunedSheaf T.base T.structMap T.ideal T.mult :=
  rfl

theorem nonzeroOnComponents_balancedTunedIdeal (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) :
    NonzeroOnComponents (balancedTunedIdeal T hv) := by
  have := hv.locallyOfFiniteType
  obtain ⟨J, hIJ, hJ⟩ :=
    exists_le_and_pow_le_tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) hv.one_le_mult
  have hle : J ^ tuningExponent T.mult ≤ balancedTunedIdeal T hv := by
    rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    exact hJ
  have hnz := hv.nonzeroOnComponents
  rw [nonzeroOnComponents_iff] at hnz ⊢
  intro C hC hsub
  refine hnz C hC ?_
  intro x hx
  have h1 := hsub hx
  have h2 := SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hle) h1
  have h3 := support_pow_subset J (tuningExponent T.mult) h2
  exact SetLike.coe_subset_coe.2 (Scheme.IdealSheafData.support_antitone hIJ) h3

theorem orderAt_balancedTunedIdeal_le_tunedMult (htf : TunedSheafProperties.{u}) (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) (x : ↥T.scheme) :
    orderAt (balancedTunedIdeal T hv) x ≤ ((tunedMult T : ℕ) : ℕ∞) := by
  have := hv.locallyOfFiniteType
  have := hv.charZero
  have := hv.smooth
  by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
  · have htop : balancedTunedIdeal T hv = ⊤ := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv]
      exact balancedTunedSheaf_eq_top_of_orderAtLeastLocus_eq_empty T.base T.structMap T.ideal hv.one_le_mult hemp
    rw [htop, orderAt_top]
    simp
  · have hmax : MaxOrderEq T.ideal T.mult :=
      ⟨(orderLE_iff T.ideal T.mult).2 hord, Set.nonempty_iff_ne_empty.2 hemp⟩
    have hLE := htf.coSupport_tunedSheaf_eq_and_orderLE.orderLE T.base T.scheme T.structMap
      T.ideal T.mult hv.one_le_mult hmax (tuningExponent T.mult) (one_le_tuningExponent T.mult)
    rw [orderLE_iff] at hLE
    have h2 : balancedTunedIdeal T hv = tunedSheaf T.base T.structMap T.ideal T.mult (tuningExponent T.mult) := by
      rw [balancedTunedIdeal_eq_balancedTunedSheaf T hv, balancedTunedSheaf_eq]
    rw [h2]
    exact hLE x

theorem isAdmissible_coverTriple_of_validPullbackAlongSmooth (hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    (coverTriple T hv).IsAdmissible := by
  have hvt := MaxContactOpenCover.isAdmissible_tunedTriple T hv (nonzeroOnComponents_balancedTunedIdeal T hv)
  have hqc := MaxContactOpenCover.quasiCompact_coverMap_comp_structureMorphism T hv hgood
  rw [MaxContactOpenCover.coverTriple_eq_tunedTriple_pullbackAlong T hv]
  exact @hpb (MaxContactOpenCover.tunedTriple T hv) hvt (chosenCoverData T hv).disjointUnion
    (coverMap T hv ≫ T.structMap) (coverMap T hv) (MaxContactCoverData.instSmoothCoverMap T hv) hqc rfl

theorem isSmoothDivisor_coverMaxContactIdeal (_hpb : OrderReduction.ValidPullbackAlongSmooth.{u})
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible)
    (hgood : MaxContactReduction.IsMaxContactCover T (chosenCoverData T hv) hv.locallyOfFiniteType
      (balancedTunedIdeal T hv) (tunedMult T)) :
    IsSmoothDivisor (coverTriple T hv).structMap (coverMaxContactIdeal T hv) := by
  refine FunctorialResolution.EmbeddedResolution.isSmoothDivisor_of_locally_coordIdeal (coverMaxContactIdeal T hv) ?_
  intro x
  obtain ⟨U, hxU, m, c, a, _hinj, hnone, hsome⟩ :=
    (MaxContactCoverGeometry.inStrictNormalCrossingPositionAt_of_isMaxContactCover T hv hgood x).exists_etaleChart
  refine ⟨U, hxU, m, c, ?_⟩
  rcases ha : a 0 with _ | t
  · exact Or.inl (hnone 0 (by simp) ha)
  · exact Or.inr ⟨t, hsome 0 (by simp) t ha⟩

end MaxContactCoverData

namespace OrderReduction

theorem maxContactCoverProperties_of_tunedSheafProperties (htf : TunedSheafProperties.{u}) (hdim : DimensionNonincreasingAlongBlowups.{u})
    (hpb : ValidPullbackAlongSmooth.{u}) : MaxContactCoverProperties.{u} := by
  refine
    { strictTransform_admissible := ?_
      coSupport_le_preimage := ?_
      schemeDim_level_le := ?_
      exists_goodCover := ?_
      hasSNCWith_cons := ?_
      valid_level := ?_
      orderAt_level_le := ?_
      coverTriple_dim_le := ?_
      coverTriple_valid := ?_
      coverContact_admissible := ?_
      coverContact_snc := ?_
      tuning := htf }
  · intro k _ _ P P₁ p _ _ _ π _ Z E hZ hπ A A₁ μ hμ hordA hsupp htr H hH
    exact FunctorialResolution.EmbeddedResolution.isMaxContactHypersurface_strictTransform_of_orderAt_le k p π Z E hZ hπ A A₁ μ hμ hordA
      hsupp htr H hH
  · intro X X₁ π Z hπ A A₁ μ htr hsupp
    exact FunctorialResolution.EmbeddedResolution.OrderLocusBlowup.orderAtLeastLocus_subset_preimage_of_isBlowupAlongIdealSheaf π Z hπ A A₁ μ htr hsupp
  · intro T hT s i hi
    exact hdim T hT s i hi
  · intro T hv hord
    exact MaxContactOpenCover.exists_isMaxContactCover T hv (MaxContactCoverData.orderAt_balancedTunedIdeal_le_tunedMult htf T hv hord)
  · intro k _ P p _ Z H N _hsmZ hsnc hZN hHZ
    exact FunctorialResolution.EmbeddedResolution.hasStrictNormalCrossingsWith_cons_of_le p Z H N hsnc hZN hHZ
  · intro T hT s i hi
    exact MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hT s i hi
  · intro T hT hord s i hi x
    exact FunctorialResolution.EmbeddedResolution.orderAt_ideal_le_mult_along_sequence T hT hord s i hi x
  · intro T hv
    exact MaxContactOpenCover.krullDimSucc_coverTriple_scheme_le_dim T hv
  · intro T hv _hord hgood
    exact MaxContactCoverData.isAdmissible_coverTriple_of_validPullbackAlongSmooth hpb T hv hgood
  · intro T hv hgood _
    exact MaxContactCoverGeometry.isMaxContactHypersurface_coverMaxContactIdeal T hv hgood
  · intro T hv hgood
    exact MaxContactCoverGeometry.inStrictNormalCrossingPosition_of_isMaxContactCover T hv hgood
      (MaxContactCoverData.isSmoothDivisor_coverMaxContactIdeal hpb T hv hgood)

end OrderReduction

end FunctorialResolution.EmbeddedResolution

end
end
