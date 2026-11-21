import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.GeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.LocallyMonomial

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def OrderAtPullbackInvariant (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) : Prop :=
  ∀ (B : Scheme.{u}) (b : B ⟶ T.scheme) (pB : B ⟶ Spec (CommRingCat.of T.base))
    (IB : B.IdealSheafData) (EB : List B.IdealSheafData),
    (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB).IsAdmissible →
    b ≫ T.structMap = pB →
    ∀ (Q : Scheme.{u}) (q : Q ⟶ B) (p : Q ⟶ Y), IsPullback q p b g →
    ∀ (A : B.IdealSheafData) (y : ↥Q),
      orderAt (A.comap q) y = orderAt A (q.base y)

theorem orderAtPullbackInvariant_of_smooth (T : MarkedIdealWithBoundary.{u}) (_hT : T.IsAdmissible)
    {Y : Scheme.{u}} (g : Y ⟶ T.scheme) [AlgebraicGeometry.Smooth g] :
    OrderAtPullbackInvariant T g := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have : CharZero T.base := hB.charZero
  have : AlgebraicGeometry.Smooth pB := hB.smooth
  have : AlgebraicGeometry.Smooth q :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @AlgebraicGeometry.Smooth) hpb.flip inferInstance
  exact orderAt_comap T.base pB q A y

theorem orderAtPullbackInvariant_baseChange_field (hG : PrincipalizationGeometryHypotheses.{u}) (T : MarkedIdealWithBoundary.{u})
    (_hT : T.IsAdmissible) (L : Type u) [Field L] [CharZero L] (f : T.base →+* L) :
    OrderAtPullbackInvariant T (pullback.fst T.structMap (specMapOfFieldHom T.base L f)) := by
  intro B b pB IB EB hB hcomm Q q p hpb A y
  have hbig : IsPullback q (p ≫ pullback.snd T.structMap (specMapOfFieldHom T.base L f)) pB
      (specMapOfFieldHom T.base L f) := by
    rw [← hcomm]
    exact hpb.paste_vert (IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base L f))
  have he : hbig.isoPullback.hom ≫ pullback.fst pB (specMapOfFieldHom T.base L f) = q :=
    hbig.isoPullback_hom_fst
  have : IsOpenImmersion hbig.isoPullback.hom := inferInstance
  have hkey := hG.orderAt_baseChange (MarkedIdealWithBoundary.mk T.base B pB IB T.mult EB) hB L f A
      (hbig.isoPullback.hom.base y)
  have hq : (pullback.fst pB (specMapOfFieldHom T.base L f)).base (hbig.isoPullback.hom.base y)
      = q.base y := congrArg (fun m : Q ⟶ B => m.base y) he
  calc orderAt (A.comap q) y
      = orderAt (A.comap (hbig.isoPullback.hom ≫
          pullback.fst pB (specMapOfFieldHom T.base L f))) y := by
        rw [he]
    _ = orderAt ((A.comap (pullback.fst pB (specMapOfFieldHom T.base L f))).comap
          hbig.isoPullback.hom) y := by
        rw [Scheme.IdealSheafData.comap_comp]
    _ = orderAt (A.comap (pullback.fst pB (specMapOfFieldHom T.base L f)))
          (hbig.isoPullback.hom.base y) :=
        orderAt_comap_of_isOpenImmersion _ _ y
    _ = orderAt A ((pullback.fst pB (specMapOfFieldHom T.base L f)).base
          (hbig.isoPullback.hom.base y)) := hkey
    _ = orderAt A (q.base y) := by rw [hq]

end FunctorialResolution.EmbeddedResolution

end
end

section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

structure MarkedPullbackSquare (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) where
  baseScheme : Scheme.{u}
  topScheme : Scheme.{u}
  bottom : baseScheme ⟶ T.scheme
  structMap : baseScheme ⟶ Spec (CommRingCat.of T.base)
  ideal : baseScheme.IdealSheafData
  mult : ℕ
  boundary : List baseScheme.IdealSheafData
  left : topScheme ⟶ baseScheme
  top : topScheme ⟶ Y
  bottom_structMap : bottom ≫ T.structMap = structMap
  dim_le : krullDimSucc baseScheme ≤ T.krullDimSucc
  isPullback : IsPullback left top bottom g
  valid : (MarkedIdealWithBoundary.mk T.base baseScheme structMap ideal mult boundary).IsAdmissible

namespace MarkedPullbackSquare

variable {T : MarkedIdealWithBoundary.{u}} {Y : Scheme.{u}} {g : Y ⟶ T.scheme}

abbrev lowerTriple (S : MarkedPullbackSquare T g) : MarkedIdealWithBoundary.{u} :=
  MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal S.mult S.boundary

abbrev upperTriple (S : MarkedPullbackSquare T g) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) (E : List S.topScheme.IdealSheafData) :
    MarkedIdealWithBoundary.{u} :=
  (S.lowerTriple.pullbackOverField S.topScheme k' (S.top ≫ q) S.left).withBoundary E

theorem orderAt_comap_verticalMap (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData) (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y = orderAt A (S.left.base y) := by
  have hval :
      (MarkedIdealWithBoundary.mk T.base S.baseScheme S.structMap S.ideal T.mult S.boundary).IsAdmissible :=
    { charZero := S.valid.charZero
      locallyOfFiniteType := S.valid.locallyOfFiniteType
      nonzeroOnComponents := S.valid.nonzeroOnComponents
      one_le_mult := hT.one_le_mult
      quasiCompact := S.valid.quasiCompact
      smooth := S.valid.smooth
      snc := S.valid.snc }
  exact hg S.baseScheme S.bottom S.structMap S.ideal S.boundary hval S.bottom_structMap
    S.topScheme S.left S.top S.isPullback A y

theorem orderAt_comap_verticalMap_le (S : MarkedPullbackSquare T g) (hT : T.IsAdmissible)
    (hg : OrderAtPullbackInvariant T g) (A : S.baseScheme.IdealSheafData) (c : ℕ∞)
    (hA : ∀ x : ↥S.baseScheme, orderAt A x ≤ c) (y : ↥S.topScheme) :
    orderAt (A.comap S.left) y ≤ c := by
  rw [S.orderAt_comap_verticalMap hT hg A y]
  exact hA (S.left.base y)

theorem flat_verticalMap (S : MarkedPullbackSquare T g) [AlgebraicGeometry.Flat g] :
    AlgebraicGeometry.Flat S.left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @AlgebraicGeometry.Flat) S.isPullback.flip ‹AlgebraicGeometry.Flat g›

end MarkedPullbackSquare

def NonMonomialPartBaseChange (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme)
    (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g) (E : List S.topScheme.IdealSheafData),
    MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
    (S.upperTriple k' q E).IsAdmissible →
      nonMonomialPart E (S.ideal.comap S.left)
        = (nonMonomialPart S.boundary S.ideal).comap S.left

def PrincipalizationBaseChange (F : PrincipalizationAssignment.{u}) (n : ℕ) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    (∀ x : ↥S.baseScheme, orderAt S.ideal x ≤ (S.mult : ℕ∞)) →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      (S.upperTriple k' q E).IsAdmissible →
      krullDimSucc S.topScheme ≤ n →
        IsPullbackBlowupSequence S.left (F (S.upperTriple k' q E)).toSequenceOfBlowups (F S.lowerTriple).toSequenceOfBlowups

def MonomialPrincipalizationBaseChange (τ : ComapIsoInvariance.{u}) (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}}
    (g : Y ⟶ T.scheme) (k' : Type u) [Field k'] (q : Y ⟶ Spec (CommRingCat.of k')) : Prop :=
  ∀ (S : MarkedPullbackSquare T g),
    MonomialCenter.IsLocallyMonomialTriple S.lowerTriple →
    ∀ (E : List S.topScheme.IdealSheafData),
      MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap S.left) S.boundary) E →
      MonomialCenter.IsLocallyMonomialTriple (S.upperTriple k' q E) →
        IsPullbackBlowupSequence S.left
          (monomialPrincipalization τ (S.upperTriple k' q E)).toSequenceOfBlowups
          (monomialPrincipalization τ S.lowerTriple).toSequenceOfBlowups

structure BaseChangeCompatible (τ : ComapIsoInvariance.{u}) (F : PrincipalizationAssignment.{u}) (n : ℕ)
    (T : MarkedIdealWithBoundary.{u}) {Y : Scheme.{u}} (g : Y ⟶ T.scheme) (k' : Type u) [Field k']
    (q : Y ⟶ Spec (CommRingCat.of k')) : Prop where
  rule : PrincipalizationBaseChange F n T g k' q
  flat : AlgebraicGeometry.Flat g
  monomialBody : MonomialPrincipalizationBaseChange τ T g k' q
  nonMonomial : NonMonomialPartBaseChange T g k' q
  order : OrderAtPullbackInvariant T g

end FunctorialResolution.EmbeddedResolution

end
end
