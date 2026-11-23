module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.IsoBlowupRemoval
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ClosedEmbedding.PushforwardUniqueness
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.BlowupSequenceFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
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

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isStrictPullbackBlowupSeq_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsStrictPullbackBlowupSeq h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsStrictPullbackBlowupSeq h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) s'.toSequenceOfBlowups
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hpb hstrict
  have hequiv : ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpushTb
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsStrictPullbackBlowupSeq.of_isomorphic_pullback hstrict hequiv

theorem isPullbackBlowupSequence_ambientBlowupSequence_of_flat
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    {X Y S S' : Scheme.{u}} (ι : S ⟶ X) (ι' : S' ⟶ Y) (h : Y ⟶ X) (h' : S' ⟶ S)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsClosedImmersion ι']
    [AlgebraicGeometry.Flat h]
    [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]
    (hsq : IsPullback ι' h' h ι)
    (s : BlowupSequenceData S) (s' : BlowupSequenceData S')
    (hs : s.CentersContainNoComponent) (hs' : s'.CentersContainNoComponent)
    (hpb : IsPullbackBlowupSequence h' s'.toSequenceOfBlowups s.toSequenceOfBlowups) :
    IsPullbackBlowupSequence h (ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups
      (ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups := by
  have : AlgebraicGeometry.Flat h' := by
    rw [← hsq.isoPullback_hom_snd]
    infer_instance
  have hUstrict : IsStrictPullbackBlowupSeq h' (s.toSequenceOfBlowups.baseChange h') s.toSequenceOfBlowups :=
    isStrictPullbackSequenceOfBlowups_baseChange s.toSequenceOfBlowups h'
  have hstrict : IsStrictPullbackBlowupSeq h
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) :=
    isStrictPullbackSequenceOfBlowups_baseChange ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) h
  have hN : ∀ i : ℕ, i ≤ ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).length →
      AlgebraicGeometry.IsLocallyNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).schemeAt i) :=
      isNoetherian_ambientBlowupSequence_schemeAt ι s hres hno hs i hi
    infer_instance
  have hN' : ∀ i : ℕ, i ≤ (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).length →
      AlgebraicGeometry.IsLocallyNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) := by
    intro i hi
    have : AlgebraicGeometry.IsNoetherian
        ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h).schemeAt i) :=
      isNoetherian_schemeAt
        (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) i hi
    infer_instance
  have hpushTb : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) :=
    IsPushforwardBlowupSeq.of_flat_isPullback ι ι' h h' hsq s.toSequenceOfBlowups
      ((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups) (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN hN'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι s hres hno hs) hUstrict hstrict
  have hpushPrune : IsPushforwardBlowupSeq ι' (s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    isPushforwardSequenceOfBlowups_withoutIsoBlowups ι' (s.toSequenceOfBlowups.baseChange h')
      (((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h) hN' hpushTb
  have heq : ((s.toSequenceOfBlowups.baseChange h').withoutIsoBlowups).Isomorphic s'.toSequenceOfBlowups :=
    IsPullbackBlowupSequence.isomorphic hUstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hpb
  have hpush' : IsPushforwardBlowupSeq ι' s'.toSequenceOfBlowups
      ((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups :=
    IsPushforwardBlowupSeq.of_isomorphic_source ι' heq hpushPrune
  have hequivT : (((((ambientBlowupSequence ι s hres hno hs).toSequenceOfBlowups).baseChange h)).withoutIsoBlowups).Isomorphic
      ((ambientBlowupSequence ι' s' hres hno hs').toSequenceOfBlowups) :=
    IsPushforwardBlowupSeq.isomorphic ι' hpush'
      (isPushforwardBlowupSeq_ambientBlowupSequence ι' s' hres hno hs')
  exact IsPullbackBlowupSequence.of_isomorphic hstrict.isPullbackSequenceOfBlowups_withoutIsoBlowups hequivT

end FunctorialResolution.EmbeddedResolution
