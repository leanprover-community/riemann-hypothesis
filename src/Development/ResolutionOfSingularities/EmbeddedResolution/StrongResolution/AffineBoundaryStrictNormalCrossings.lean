module

public import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.AffineResolutionConditions
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsNil
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
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

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem centersHaveStrictNormalCrossingsWithBoundary {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.CentersHaveStrictNormalCrossingsWithBoundary := fun i hi => S.principalizationSequence.center_snc i hi

private theorem smooth_schemeAtToSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    ∀ i, i ≤ S.ambientLength → AlgebraicGeometry.Smooth (S.schemeAtToSpec i) := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth S.ambientToSpec := S.ambient_smooth
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_zero]
      infer_instance
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have hsm0 : AlgebraicGeometry.Smooth (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) :=
        ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := smooth_comp_of_isBlowupAlongIdealSheaf hZE hb
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc]
      exact hres

private theorem boundaryInStrictNormalCrossingPosition {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) :
    S.BoundaryInStrictNormalCrossingPosition := by
  intro i
  induction i with
  | zero =>
      intro _
      have : AlgebraicGeometry.Smooth (S.schemeAtToSpec 0) :=
        smooth_schemeAtToSpec S 0 (Nat.zero_le _)
      have h0 : S.boundary 0 = ([] : List (S.ambientLevel 0).IdealSheafData) := by
        rw [AffineSpacePrincipalizationData.boundary_def, IdealBlowupSequence.boundary_zero]
        rfl
      rw [h0]
      exact inStrictNormalCrossingPosition_nil (S.schemeAtToSpec 0)
  | succ n ih =>
      intro hn
      have hlt : n < S.ambientLength := hn
      have : AlgebraicGeometry.IsNoetherian (S.ambientLevel (n + 1)) :=
        isNoetherian_ambientLevel S (n + 1) hn
      have : TopologicalSpace.NoetherianSpace ↥(S.ambientLevel (n + 1)) := inferInstance
      have hE : InStrictNormalCrossingPosition (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec)
          (S.principalizationSequence.boundary n) := ih (Nat.le_of_lt hlt)
      have hZE : HasStrictNormalCrossingsWith (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.center n)
          (S.principalizationSequence.boundary n) := S.principalizationSequence.center_snc n hlt
      have hb : Blowup.IsBlowupAlongIdealSheaf (S.ambientBlowups.transitionMapSucc n) (S.ambientBlowups.center n) :=
        S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hlt
      have hres := inStrictNormalCrossingPosition_strictTransform_append
        (S.ambientBlowups.projectionToBase n ≫ S.ambientToSpec) (S.ambientBlowups.transitionMapSucc n)
        (S.ambientBlowups.center n) (S.principalizationSequence.boundary n) hb hE hZE
      rw [AffineSpacePrincipalizationData.schemeAtToSpec_def, SequenceOfBlowups.projectionToBase_succ, Category.assoc,
        AffineSpacePrincipalizationData.boundary_def, S.principalizationSequence.boundary_succ n hlt]
      exact hres

theorem affineCentersHaveStrictNormalCrossingsWithBoundary (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineCentersHaveStrictNormalCrossingsWithBoundary A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact centersHaveStrictNormalCrossingsWithBoundary (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineAllLevelsSmooth (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineAllLevelsSmooth A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact smooth_schemeAtToSpec (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

theorem affineBoundaryInStrictNormalCrossingPosition (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    AffineBoundaryInStrictNormalCrossingPosition A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _
  exact boundaryInStrictNormalCrossingPosition (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY)

end FunctorialResolution.EmbeddedResolution

end
