module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.StrongResolution
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsClopen
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineBoundaryStrictNormalCrossings
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineCentersOverSingularLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineDetachedConditions
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.ClosedEmbeddingsIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.GlobalResolutionFromAffine
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SingularPreimageBoundary
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SmoothLocusPreimageDense
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem isStrongResolution_canonicalAffineResolutionRule (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] :
    IsStrongResolution k Y p (canonicalAffineResolutionRule k Y p) := by
  have hIso : EmbeddedPrincipalizationDiscardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters
  have hsmooth : AffineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
    affineDetachedSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
  have hCen : AffineCentersLieOverSingularLocus principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :=
    affineCentersLieOverSingularLocus_principalizationWithRadicalCenters
  show IsStrongResolution k Y p
    (affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters k Y p)
  exact isStrongResolution_blowupSequenceWithoutIsos_ofAffine principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    (affineStrictTransformEmptyAtLast_of_isFunctorialPrincipalization principalizationWithRadicalCenters.{u}
      isFunctorialPrincipalization_principalizationWithRadicalCenters affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth)
    hsmooth
    (affineSmoothLocusPreimageDenseInDetached principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    hCen
    (affineDetachedClopenInCenter principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedComponentsNotInBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineDetachedSingularPreimageEqBoundary_of_centersLieOverSing principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth hIso hsmooth
      embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters hCen)
    (affineCentersHaveStrictNormalCrossingsWithBoundary principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineAllLevelsSmooth principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    (affineBoundaryInStrictNormalCrossingPosition principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictNormalCrossingsRestrictToClopen Blowup.blowupIsProper k Y p

theorem strongResolutionOfSingularitiesCharZero :
    StrongResolutionOfSingularitiesCharZero.{u} :=
  strongResolutionOfSingularitiesCharZero_of_principalizationAlgorithm principalizationWithRadicalCenters.{u}
    affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    isFunctorialPrincipalization_principalizationWithRadicalCenters
    transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters
    embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters
    closedEmbeddingsRelatedByAutomorphism
    isStrongResolution_canonicalAffineResolutionRule

end FunctorialResolution.EmbeddedResolution
