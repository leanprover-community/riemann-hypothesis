module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelFlatBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.SupportFlatPullback
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

structure PresentedSelection where
  sel : EmbeddingChoice.{u}
  pres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], ClosedEmbeddingIntoAffineSpace (sel k Y p)
  basePres : ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    (hker : NonzeroOnComponents (Scheme.Hom.ker ((sel k Y p).baseChangeEmb K)))
    (hsnc : InStrictNormalCrossingPosition (baseChangeToSpec (sel k Y p).ambientStruct K) []),
    ClosedEmbeddingIntoAffineSpace ((sel k Y p).baseChange K hker hsnc)

theorem isCompatibleWithFieldBaseChange_toAffineResolutionRule (R : EmbeddedResolutionRule.{u})
    (C : PresentedSelection.{u}) (hinv : R.IsIndependentOfPresentedEmbedding)
    (hfield : R.IsCompatibleWithFieldBaseChange)
    (hsnc : ∀ (k : Type u) [Field k] [CharZero k] (A : Scheme.{u})
      (q : A ⟶ Spec (CommRingCat.of k)), AlgebraicGeometry.Smooth q → InStrictNormalCrossingPosition q []) :
    IsCompatibleWithFieldBaseChange (R.toAffineResolutionRule C.sel) := by
  intro k _ _ Y p _ _ _ _ K _ _ _ _ _
  have hlft : AlgebraicGeometry.LocallyOfFiniteType (baseChangeToSpec p K) :=
    locallyOfFiniteType_baseChangeToSpec p K
  have hqcb : AlgebraicGeometry.QuasiCompact (baseChangeToSpec p K) :=
    quasiCompact_baseChangeToSpec p K
  have hsncK : InStrictNormalCrossingPosition
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      ([] : List (baseChange (C.sel k Y p).ambientStruct K).IdealSheafData) :=
    hsnc K (baseChange (C.sel k Y p).ambientStruct K)
      (baseChangeToSpec (C.sel k Y p).ambientStruct K)
      (EmbeddingDatum.smooth_baseChangeToSpec_ambientToSpec (C.sel k Y p) K)
  have hsq : IsPullback (baseChangeProjection p K) ((C.sel k Y p).baseChangeEmb K)
      (C.sel k Y p).emb (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    (EmbeddingDatum.isPullback_baseChangeEmb (C.sel k Y p) K).flip
  have hflat : AlgebraicGeometry.Flat (baseChangeProjection (C.sel k Y p).ambientStruct K) :=
    inferInstance
  have hqc1 : AlgebraicGeometry.QuasiCompact (C.sel k Y p).emb := inferInstance
  have hqc2 : AlgebraicGeometry.QuasiCompact ((C.sel k Y p).baseChangeEmb K) :=
    quasiCompact_of_isPullback hsq
  have hkerK : NonzeroOnComponents (Scheme.Hom.ker ((C.sel k Y p).baseChangeEmb K)) := by
    rw [ker_eq_comap_ker_of_isPullback_of_flat hsq]
    exact NonzeroOnComponents.comap_of_flat (C.sel k Y p).nonzeroOnComponents_ker _
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback (hfield k Y p (C.sel k Y p) K hkerK hsncK)
    (hinv K (baseChange p K) (baseChangeToSpec p K)
      ((C.sel k Y p).baseChange K hkerK hsncK)
      (C.sel K (baseChange p K) (baseChangeToSpec p K))
      (C.basePres k Y p K hkerK hsncK)
      (C.pres K (baseChange p K) (baseChangeToSpec p K)))

def affineSpacePresentedSelection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    PresentedSelection.{u} where
  sel := affineSpaceEmbeddingChoice hemb hsncE hsm
  pres := fun k _ _ Y p _ _ _ _ => affineSpaceChartPresentation hemb hsncE hsm k Y p
  basePres := fun k _ _ Y p _ _ _ _ K _ _ _ _ _ =>
    let n := (hemb k Y p).choose
    presentationOfAmbientIso hsm _ n
      (baseChangeAffineSpaceIso k K (ULift.{u, 0} (Fin n)))
      (baseChangeAffineSpaceIso_hom_comp_toSpec k K (ULift.{u, 0} (Fin n)))

@[simp]
theorem affineSpacePresentedSelection_selection (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsncE : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    (affineSpacePresentedSelection hemb hsncE hsm).sel = affineSpaceEmbeddingChoice hemb hsncE hsm :=
  rfl

end FunctorialResolution.EmbeddedResolution

end
