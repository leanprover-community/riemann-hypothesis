module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupClosedSubscheme
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.ChartIsolation
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealAssignment
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.RadicalCenterIdeal
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineEmbeddingIntoAffineSpace
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineSpaceSmooth
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalRulesCorrect
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.ClosedImmersionCommutation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.StrictTransformAvoidance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformIsolation.VanishingIdealHypotheses
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem canonicalAlgorithmRules_isCorrect :
    (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme.{u}).ReducesInductivelyOnDimension :=
  isCorrect_canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme

noncomputable abbrev principalizationWithRadicalCenters : PrincipalizationAlgorithm.{u} :=
  canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme smoothSubschemeIdealIsRadical.{u}

theorem embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen (A : PrincipalizationAlgorithm.{u}) (h : DetachedLocusIsOpenForEmbeddings.{u} A) :
    EmbeddedPrincipalizationDiscardedLocusIsOpen.{u} A affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact h k Y pY
    (affineSpaceEmbeddingDatum affineEmbedsIntoAffineSpace nilIsStrictNormalCrossingsOnAffineSpace
      affineSpaceIsSmooth k Y pY) i hi

theorem chartIsolationHypotheses_principalizationWithRadicalCenters :
    OpenImmersionRestriction.ChartIsolationHypotheses OpenImmersionRestriction.vanishingIdealAssignment.{u} principalizationWithRadicalCenters.{u} := by
  have h : OpenImmersionRestriction.reducedVanishingAssignment.{u} = OpenImmersionRestriction.vanishingIdealAssignment.{u} := by
    funext X T
    rw [OpenImmersionRestriction.vanishingIdealAssignment_apply]
    rfl
  have h2 := OpenImmersionRestriction.chartIsolationHypotheses_reducedVanishingAssignment principalizationWithRadicalCenters.{u}
  rwa [h] at h2

theorem detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters :
    DetachedLocusIsOpenForEmbeddings.{u} principalizationWithRadicalCenters.{u} :=
  OpenImmersionRestriction.detachedLocusIsOpenForEmbeddings_canonicalPrincipalization OpenImmersionRestriction.idealSheafGeometryHypotheses_vanishingIdealAssignment.{u}
    strictTransformIsBlowupOfClosedSubscheme.{u} canonicalAlgorithmRules_isCorrect smoothSubschemeIdealIsRadical.{u}
    chartIsolationHypotheses_principalizationWithRadicalCenters.{u}

theorem transitionsAreBlowupsForEmbeddings_principalizationWithRadicalCenters :
    TransitionsAreBlowupsForEmbeddings principalizationWithRadicalCenters.{u} :=
  transitionsAreBlowupsForEmbeddings_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
    detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters

theorem embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters :
    EmbeddedPrincipalizationYieldsBlowups principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth :=
  embeddedPrincipalizationYieldsBlowups_of_discardedLocusIsOpen principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth
    (embeddedPrincipalizationDiscardedLocusIsOpen_of_detachedLocusIsOpen principalizationWithRadicalCenters.{u}
      detachedLocusIsOpenForEmbeddings_principalizationWithRadicalCenters)
    (embeddedPrincipalizationAmbientIsNoetherian principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
      nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth)
    strictTransformIsBlowupOfClosedSubscheme

theorem isFunctorialPrincipalization_principalizationWithRadicalCenters : IsFunctorialPrincipalization principalizationWithRadicalCenters.{u} :=
  isFunctorialPrincipalization_canonicalPrincipalization strictTransformIsBlowupOfClosedSubscheme canonicalAlgorithmRules_isCorrect
    smoothSubschemeIdealIsRadical
    (commutesWithClosedImmersion_of_isCorrect (canonicalAlgorithmRules strictTransformIsBlowupOfClosedSubscheme) canonicalAlgorithmRules_isCorrect)

noncomputable def canonicalAffineResolutionRule : AffineResolutionRule.{u} :=
  affineResolutionRuleOfPrincipalization principalizationWithRadicalCenters.{u} affineEmbedsIntoAffineSpace
    nilIsStrictNormalCrossingsOnAffineSpace affineSpaceIsSmooth embeddedPrincipalizationYieldsBlowups_principalizationWithRadicalCenters

end FunctorialResolution.EmbeddedResolution
