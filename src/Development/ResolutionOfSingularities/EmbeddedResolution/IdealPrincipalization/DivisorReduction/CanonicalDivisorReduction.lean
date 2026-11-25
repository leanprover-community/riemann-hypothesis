module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization
public import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling
public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter
public import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingFlatPullback
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.NonMonomialOrderReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.ReduceModChar
import Std.Tactic.BVDecide.Normalize.Prop
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Std.Tactic.BVDecide.Normalize.BitVec
import Mathlib.RingTheory.Henselian
import Mathlib.Tactic.Linter.HaveILetI
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PreimageSupportOfAdmissible
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange
public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing, Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport", "h": "module\n\npublic import Mathlib.AlgebraicGeometry.IdealSheaf.Basic\npublic import Mathlib.Combinatorics.Quiver.ReflQuiver\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

namespace FunctorialResolution.EmbeddedResolution

open CategoryTheory AlgebraicGeometry

theorem support_ker_comp_subset_support_ker {T S Y : Scheme}
    (g : T ⟶ S) (f : S ⟶ Y) :
    ((g ≫ f).ker.support : Set Y) ⊆ (f.ker.support : Set Y) := by
  intro x hx
  exact Scheme.IdealSheafData.support_antitone (Scheme.Hom.le_ker_comp g f) hx

end FunctorialResolution.EmbeddedResolution
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ControlledTransformRestriction\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealAfterBlowup\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform\nimport Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.GoingUpInvariant\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem toMarkedSequence_projectionToBase_eq {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (d : BlowupSequenceData X) (h : d.IsMarked p I m E) (n : ℕ) :
    ((d.toMarkedBlowupSequenceData p I m E h).toMarkedSequenceOfBlowups).projectionToBase n = d.projectionToBase n :=
  BlowupSequenceData.toSequenceOfBlowups_projectionToBase d n

private theorem embeddingIntoAmbientBlowupSequence_comp_projectionToBase {S X : Scheme.{u}} (ι : S ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsNoetherian X]
    (d : BlowupSequenceData S) (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u})
    (hcen : ∀ i < d.length, ∀ W ∈ irreducibleComponents ↥(d.obj i), ¬W ⊆ ↑(d.center i).support)
    (n : ℕ) :
    embeddingIntoAmbientBlowupSequence ι d hres hno hcen n ≫ (ambientBlowupSequence ι d hres hno hcen).projectionToBase n =
      d.projectionToBase n ≫ ι := by
  induction n with
  | zero =>
    have hiso : (ambientBlowupSequence ι d hres hno hcen).isoZero.hom = 𝟙 X :=
      congrArg (fun e => Iso.hom e) (ambientBlowupSequence_isoObjZero ι d hres hno hcen)
    rw [BlowupSequenceData.projectionToBase_zero, BlowupSequenceData.projectionToBase_zero, embeddingIntoAmbientBlowupSequence_zero, hiso]
    exact Category.comp_id _
  | succ m ih =>
    rw [BlowupSequenceData.projectionToBase_succ, BlowupSequenceData.projectionToBase_succ, ← Category.assoc,
      embeddingIntoAmbientBlowupSequence_succ_comp_map ι d hres hno hcen m, Category.assoc, ih, ← Category.assoc]

theorem embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase t =
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbientBlowupSequence_comp_projectionToBase (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
  rw [MarkedBlowupSequenceData.projectionToBase_eq_toBlowupSequenceData_projectionToBase (MarkedBlowupSequenceData.ofMarkedSequence s) t]
  exact h

theorem projectionToSpec_eq_comp_ambientMarkedSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hB : (pushedMarkedSeq hres hno T j hj s hpr hmk).projectionToBase t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t :=
    toMarkedSequence_projectionToBase_eq _ hmk t
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (pushedMarkedSeq hres hno T j hj s hpr hmk) t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t ≫ T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).projectionToBase t) ≫ T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

theorem projectionToSpec_eq_comp_prependedAmbientSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    MarkedSequenceOfBlowups.projectionToSpec s t =
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) := by
  have h6 := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj
    (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase] at h6
  have hA : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).projectionToBase (t + 1) :=
    toMarkedSequence_projectionToBase_eq _ hmk (t + 1)
  have hB : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToBase (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t :=
    hA.trans (BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) t)
  have hstruct : MarkedSequenceOfBlowups.projectionToSpec (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact congrArg (fun f => f ≫ T.structMap) hB
  have e1 : embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
          T.structMap)
      = (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap := (Category.assoc _ _ _).symm
  have e2 : (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t) ≫
            T.structMap
      = (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap :=
    congrArg (fun f => f ≫ T.structMap) h6
  have e3 : (s.projectionToBase t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) ≫ T.structMap
      = s.projectionToBase t ≫ ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    Category.assoc _ _ _
  rw [hstruct, MarkedSequenceOfBlowups.projectionToSpec_eq]
  exact ((e1.trans e2).trans e3).symm

private def unionSupportsExcept {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) : Set ↥Y :=
  ⋃ i : Fin L.length, ⋃ (_ : (i : ℕ) ≠ j), ((L.get i).support : Set ↥Y)

private theorem support_subset_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j i : ℕ)
    (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept L j := by
  intro x hx
  exact Set.mem_iUnion.2 ⟨⟨i, hi⟩, Set.mem_iUnion.2 ⟨hij, hx⟩⟩

private theorem exists_mem_support_of_mem_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ)
    {x : ↥Y} (hx : x ∈ unionSupportsExcept L j) :
    ∃ i : ℕ, ∃ h : i < L.length, i ≠ j ∧ x ∈ ((L[i].support : Set ↥Y)) := by
  obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
  obtain ⟨h1, h2⟩ := Set.mem_iUnion.1 hi
  exact ⟨i.1, i.2, h1, h2⟩

private theorem isClosed_iUnion_prop {α : Type u} [TopologicalSpace α] {p : Prop} {A : Set α}
    (h : IsClosed A) : IsClosed (⋃ _ : p, A) :=
  isClosed_iUnion_of_finite fun _ => h

private theorem isClosed_otherLocusOfList {Y : Scheme.{u}} (L : List Y.IdealSheafData) (j : ℕ) :
    IsClosed (unionSupportsExcept L j) := by
  refine isClosed_iUnion_of_finite ?_
  intro i
  exact isClosed_iUnion_prop ((L.get i).support).2

private theorem apply_eq_apply_of_comp_eq {A B C D : Scheme.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (f' : A ⟶ D) (g' : D ⟶ C) (e : f ≫ g = f' ≫ g') (x : ↥A) : ⇑g (⇑f x) = ⇑g' (⇑f' x) :=
  congrArg (fun m : A ⟶ C => ⇑m x) e

private theorem otherBoundaryLocus_eq_otherLocusOfList {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (j t : ℕ) :
    MarkedSequenceOfBlowups.otherBoundaryLocus S j t = unionSupportsExcept (S.boundary t) j := rfl

private theorem support_subset_otherLocusOfList_append_left {Y : Scheme.{u}} (L M : List Y.IdealSheafData)
    (j i : ℕ) (hi : i < L.length) (hij : i ≠ j) :
    ((L[i].support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ M) j := by
  have h1 : i < (L ++ M).length := by
    rw [List.length_append]
    omega
  have h2 := support_subset_otherLocusOfList (L ++ M) j i h1 hij
  rwa [List.getElem_append_left hi] at h2

private theorem support_subset_otherLocusOfList_append_singleton {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (e : Y.IdealSheafData) (j : ℕ) (hj : j < L.length) :
    ((e.support : Set ↥Y)) ⊆ unionSupportsExcept (L ++ [e]) j := by
  have h1 : L.length < (L ++ [e]).length := by
    rw [List.length_append]
    simp
  have h2 := support_subset_otherLocusOfList (L ++ [e]) j L.length h1 (by omega)
  have h3 : (L ++ [e])[L.length]'h1 = e := by simp
  rwa [h3] at h2

private theorem embeddingIntoAmbient_zero_comp_isoObjZero_hom (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0 ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom =
      s.isoZero.hom ≫ (T.boundary.get ⟨j, hj⟩).subschemeι := by
  have h := embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres hno T j hj I₀ E₀ s hpr 0
  rw [MarkedBlowupSequenceData.ofMarkedSequence_projectionToBase, MarkedSequenceOfBlowups.projectionToBase_zero,
    BlowupSequenceData.projectionToBase_zero] at h
  exact h

private theorem comap_embeddingIntoAmbient_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) = s.center t := by
  have := instIsClosedImmersionPushedEmb hres hno T j hj I₀ E₀ s hpr t
  rw [ambientBlowupSeq_center_eq_imageIdealSheaf]
  exact Blowup.comap_schemeImageIdeal (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) (s.center t)

private theorem preimage_support_center_ambientBlowupSeq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support : Set _)) =
      (((s.center t).support : Set ↥(s.schemeAt t))) := by
  ext x
  have h : x ∈ (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).comap
        (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t)).support ↔
      ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) x ∈
        ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center t).support) : Set _) :=
    Scheme.IdealSheafData.mem_support_comap ..
  rw [comap_embeddingIntoAmbient_center_ambientBlowupSeq] at h
  exact h.symm

private theorem isNoetherian_boundary_subscheme (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length) :
    AlgebraicGeometry.IsNoetherian (T.boundary.get ⟨j, hj⟩).subscheme := by
  have : AlgebraicGeometry.LocallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι :=
    inferInstance
  have : AlgebraicGeometry.QuasiCompact (T.boundary.get ⟨j, hj⟩).subschemeι := inferInstance
  exact isNoetherian_of_locallyOfFiniteType (T.boundary.get ⟨j, hj⟩).subschemeι

private theorem isNoetherian_schemeAt_restrictToBoundaryDivisor (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups) (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.IsNoetherian (s.schemeAt i) :=
  @isNoetherian_schemeAt _ s.toSequenceOfBlowups (isNoetherian_boundary_subscheme T j hj) i hi

private theorem boundaryLocus_subset_preimage_otherLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hjE : j < E₀.length) :
    ∀ t, t ≤ s.length →
      MarkedSequenceOfBlowups.boundaryLocus s t ⊆
        ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr t) ⁻¹'
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ t) j := by
  intro t
  induction t with
  | zero =>
      intro _ x hx
      obtain ⟨D, hD, hxD⟩ := (_root_.FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.mem_boundaryLocus_iff s 0 x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_zero] at hD
      obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD
      have hD₀' : D₀ ∈ List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
          (List.take (T.boundary.length - 1) (E₀.eraseIdx j)) := hD₀
      obtain ⟨D₁, hD₁, rfl⟩ := List.mem_map.1 hD₀'
      have hD₁' : D₁ ∈ E₀.eraseIdx j := List.mem_of_mem_take hD₁
      obtain ⟨i, hi, hij, hget⟩ := List.mem_eraseIdx_iff_getElem.1 hD₁'
      subst hget
      have hlen0 : i < ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0).length := by
        rw [BlowupSequenceData.boundary_length]
        omega
      have hentry0 : ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0)[i]'hlen0
          = (E₀[i]'hi).comap (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom := by
        simp [BlowupSequenceData.boundary_zero]
      have hmem0 : x ∈ ((((E₀[i]'hi).comap (T.boundary.get ⟨j, hj⟩).subschemeι).comap
          s.isoZero.hom).support : Set _) := hxD
      have hmem1 := Scheme.IdealSheafData.mem_support_comap.mp hmem0
      have hmem2 := Scheme.IdealSheafData.mem_support_comap.mp hmem1
      have hkey := apply_eq_apply_of_comp_eq (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0)
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom s.isoZero.hom
        (T.boundary.get ⟨j, hj⟩).subschemeι
        (embeddingIntoAmbient_zero_comp_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr) x
      have hmem3 : ⇑(ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom
          (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x) ∈ (E₀[i]'hi).support := by
        rw [hkey]
        exact hmem2
      show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr 0) x ∈
        unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ 0) j
      refine support_subset_otherLocusOfList _ j i hlen0 hij ?_
      rw [hentry0]
      exact Scheme.IdealSheafData.mem_support_comap.mpr hmem3
  | succ n ih =>
      intro ht x hx
      have hn : n < s.length := ht
      have ihn := ih (Nat.le_of_lt hn)
      have : AlgebraicGeometry.IsNoetherian (s.schemeAt (n + 1)) :=
        isNoetherian_schemeAt_restrictToBoundaryDivisor T j hj I₀ E₀ s (n + 1) hn
      have : AlgebraicGeometry.IsNoetherian
          ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).obj (n + 1)) :=
        isNoetherian_ambientBlowupSeq_schemeAt hres hno T j hj I₀ E₀ s hpr (n + 1) hn
      have hmapeq : ∀ y : ↥(s.schemeAt (n + 1)),
          ⇑((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y)
            = ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y) := by
        intro y
        exact apply_eq_apply_of_comp_eq _ _ _ _
          (embeddingIntoAmbient_comp_blowupMorphism hres hno T j hj I₀ E₀ s hpr n) y
      have hcenter := preimage_support_center_ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr n
      obtain ⟨D, hD, hxD⟩ := (_root_.FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.mem_boundaryLocus_iff s (n + 1) x).1 hx
      rw [MarkedSequenceOfBlowups.boundary_succ s n hn] at hD
      rcases List.mem_append.1 hD with hD' | hD'
      · obtain ⟨D₀, hD₀, rfl⟩ := List.mem_map.1 hD'
        have hCclosed : IsClosed (⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) ⁻¹'
            unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j) :=
          (isClosed_otherLocusOfList _ _).preimage
            (embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)).continuous
        rw [support_strictTransform_eq_closure_sdiff (s.transitionMapSucc n) (s.center n) D₀] at hxD
        refine hCclosed.closure_subset_iff.2 ?_ hxD
        intro y hy
        have hy1 : ⇑(s.transitionMapSucc n) y ∈ (D₀.support : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hy.1
        have hy2 : ⇑(s.transitionMapSucc n) y ∉ (((s.center n).support) : Set _) := fun hcon =>
          hy.2 ((Scheme.IdealSheafData.mem_support_comap ..).2 hcon)
        have hIH0 := ihn ((_root_.FunctorialResolution.EmbeddedResolution.MarkedSequenceOfBlowups.mem_boundaryLocus_iff s n _).2 ⟨D₀, hD₀, hy1⟩)
        have hIH : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∈ unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j := hIH0
        obtain ⟨i, hi, hij, hmem⟩ :=
          exists_mem_support_of_mem_otherLocusOfList ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n) j hIH
        have hnotZ : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr n) (⇑(s.transitionMapSucc n) y)
            ∉ ((((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n).support : Set _)) := by
          intro hcon
          exact hy2 ((Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) y)).1 hcon)
        have hstep : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
            ((Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi)).support : Set _) := by
          rw [support_strictTransform_eq_closure_sdiff]
          refine subset_closure ?_
          refine ⟨?_, ?_⟩
          · refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
            rw [hmapeq y]
            exact hmem
          · intro hcon
            have hcon' := (Scheme.IdealSheafData.mem_support_comap ..).1 hcon
            rw [hmapeq y] at hcon'
            exact hnotZ hcon'
        have hlen : i < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map]
          exact hi
        have hentry : (List.map
              (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))[i]'hlen
            = Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
                ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)
                (((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)[i]'hi) := by
          simp
        have hfin := support_subset_otherLocusOfList_append_left
          (List.map (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n))
          [Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)] j i hlen hij
        rw [hentry] at hfin
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) y ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact hfin hstep
      · have hDe : D = Blowup.exceptionalIdeal (s.transitionMapSucc n) (s.center n) := by
          simpa using hD'
        subst hDe
        rw [Blowup.exceptionalIdeal_eq_comap] at hxD
        have hxD' : ⇑(s.transitionMapSucc n) x ∈ (((s.center n).support) : Set _) :=
          (Scheme.IdealSheafData.mem_support_comap ..).1 hxD
        have hjlen : j < (List.map
            (Blowup.strictTransform ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n))
            ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ n)).length := by
          rw [List.length_map, BlowupSequenceData.boundary_length]
          omega
        have hmem : ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
            ((Blowup.exceptionalIdeal ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).map n)
              ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).center n)).support : Set _) := by
          rw [Blowup.exceptionalIdeal_eq_comap]
          refine (Scheme.IdealSheafData.mem_support_comap ..).2 ?_
          rw [hmapeq x]
          exact (Set.ext_iff.1 hcenter (⇑(s.transitionMapSucc n) x)).2 hxD'
        show ⇑(embeddingIntoAmbient hres hno T j hj I₀ E₀ s hpr (n + 1)) x ∈
          unionSupportsExcept ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).boundaryFrom E₀ (n + 1)) j
        rw [BlowupSequenceData.boundary_succ]
        exact support_subset_otherLocusOfList_append_singleton _ _ j hjlen hmem

private theorem ambientMarkedSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

private theorem prependedAmbientSeq_boundary (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary t =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary t :=
  BlowupSequenceData.toMarkedBlowupSequenceData_boundary _ _ _ _ _ hmk t

private theorem prepend_boundary_succ_eq (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (t : ℕ) :
    (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr)).boundaryFrom T.boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t := by
  induction t with
  | zero =>
      rw [boundary_prepend_ambientBlowupSeq_one, BlowupSequenceData.boundary_zero]
  | succ m ih =>
      rw [BlowupSequenceData.boundary_succ, ih, BlowupSequenceData.boundary_succ, BlowupSequenceData.prepend_blowupMorphism_succ,
        BlowupSequenceData.prepend_center_succ]
      rfl

theorem boundaryLocus_subset_preimage_otherBoundaryLocus (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (s : (restrictToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t := by
  have hlowerEq : lowerBoundaryWithoutBlowup T = T.boundary := by simp [lowerBoundaryWithoutBlowup_eq]
  have hjE : j < (lowerBoundaryWithoutBlowup T).length := by
    rw [hlowerEq]
    exact hj
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T)
    s hpr hjE t (le_of_lt ht)
  have h1 : (pushedMarkedSeq hres hno T j hj s hpr hmk).boundary t =
      (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
        (lowerBoundaryWithoutBlowup T) t := by
    rw [ambientMarkedSeq_boundary]
    exact congrArg
      (fun E => (ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom E t)
      hlowerEq.symm
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (pushedMarkedSeq hres hno T j hj s hpr hmk) j t
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealWithoutBlowup T) (lowerBoundaryWithoutBlowup T) s hpr).boundaryFrom
          (lowerBoundaryWithoutBlowup T) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j t).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

theorem boundaryLocus_subset_preimage_otherBoundaryLocus_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (t : ℕ) (ht : t < s.length) :
    MarkedSequenceOfBlowups.boundaryLocus s t ⊆
      ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t) ⁻¹'
        MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1) := by
  have hjE : j < (lowerBoundaryAfterBlowup T j hj).length := by
    show j < (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
      (List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary) ++
      [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)]).length
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil]
    omega
  have hmain := boundaryLocus_subset_preimage_otherLocus hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr hjE t (le_of_lt ht)
  have h1 : (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (t + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).boundaryFrom
        (lowerBoundaryAfterBlowup T j hj) t := by
    rw [prependedAmbientSeq_boundary, prepend_boundary_succ_eq]
  have hset : MarkedSequenceOfBlowups.otherBoundaryLocus (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (t + 1)
      = unionSupportsExcept ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj)
          s hpr).boundaryFrom (lowerBoundaryAfterBlowup T j hj) t) j :=
    (otherBoundaryLocus_eq_otherLocusOfList _ j (t + 1)).trans (congrArg (fun L => unionSupportsExcept L j) h1)
  rw [hset]
  exact hmain

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.CanonicalPrincipalization\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.ControlledTransformOrderBound\nimport Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback\nimport Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.BlowupDataOfSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.DisjointCentersPullback\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReductionEmptyOrderLocus

private theorem blowupMorphism_mem_orderAtLeastLocus {k : Type u} [Field k] [CharZero k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (hm : 1 ≤ m)
    (hsm : ∀ i, i ≤ s.length → AlgebraicGeometry.Smooth (MarkedSequenceOfBlowups.projectionToSpec s i))
    (hno : ∀ i, i ≤ s.length → AlgebraicGeometry.IsNoetherian (s.schemeAt i))
    (i : ℕ) (hi : i < s.length) (z : s.schemeAt (i + 1))
    (hz : z ∈ orderAtLeastLocus (s.ideal (i + 1)) m) :
    (s.transitionMapSucc i) z ∈ orderAtLeastLocus (s.ideal i) m := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, (Nat.succ_pred_eq_of_pos hm).symm⟩
  have := hsm i hi.le
  have := hno (i + 1) hi
  have hsnc : HasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.boundary i) := by
    rw [MarkedSequenceOfBlowups.projectionToSpec_eq]
    exact s.center_snc i hi
  have hord : (↑(s.center i).support : Set (s.schemeAt i)) ⊆ orderAtLeastLocus (s.ideal i) n :=
    (s.center_order i hi).trans
      (orderAtLeastLocus_subset_of_le (s.ideal i) (Nat.le_succ n))
  have hI : s.ideal i ≤ s.center i ^ n :=
    le_pow_of_hasStrictNormalCrossingsWith (MarkedSequenceOfBlowups.projectionToSpec s i) (s.center i) (s.ideal i)
      (s.boundary i) hsnc n hord
  have hpb : Blowup.IsBlowupAlongIdealSheaf (s.transitionMapSucc i) (s.center i) := s.isBlowupAlongIdealSheaf_blowupMorphism i hi
  have key := orderAtLeastLocus_controlledTransform_subset_preimage k
      (MarkedSequenceOfBlowups.projectionToSpec s i) (s.transitionMapSucc i) (s.center i) (s.boundary i) hsnc hpb
      (s.ideal i) n hI
  have hmul : Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) ^ n *
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1))
      = (s.ideal i).comap (s.transitionMapSucc i) := by
    rw [← mul_assoc, ← pow_succ]
    exact s.ideal_succ i hi
  have heq := eq_controlledTransform_of_mul_eq_comap (s.transitionMapSucc i) (s.center i) (s.ideal i) n hpb hI
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) hmul
  have hz' : z ∈ orderAtLeastLocus
      (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i) * s.ideal (i + 1)) (n + 1) := by
    rw [mem_orderAtLeastLocus_iff] at hz ⊢
    exact hz.trans ((self_le_add_left _ _).trans
      (add_orderAt_le_orderAt_mul (Blowup.exceptionalIdeal (s.transitionMapSucc i) (s.center i))
        (s.ideal (i + 1)) z))
  rw [heq] at hz'
  exact key hz'

private theorem projectionToBase_mem_orderAtLeastLocus {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) (s : T.SequenceOfBlowups) :
    ∀ i, i ≤ s.length → ∀ z : s.schemeAt i,
      z ∈ orderAtLeastLocus (s.ideal i) T.mult → (s.projectionToBase i) z ∈ orderAtLeastLocus T.ideal T.mult := by
  have := hV.charZero
  intro i
  induction i with
  | zero =>
      intro _ z hz
      rw [markedSequenceOfBlowups_ideal_zero s, MarkedSequenceOfBlowups.projectionToBase_zero s, orderAtLeastLocus_comap_iso_hom_eq_preimage] at hz
      rw [MarkedSequenceOfBlowups.projectionToBase_zero s]
      exact hz
  | succ i ih =>
      intro hi z hz
      rw [MarkedSequenceOfBlowups.projectionToBase_succ_apply]
      refine ih (Nat.le_of_succ_le hi) _ ?_
      exact blowupMorphism_mem_orderAtLeastLocus s hV.one_le_mult
        (fun j hj => MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV s j hj)
        (fun j hj => MarkedSequenceOfBlowups.isNoetherian_schemeAt effectiveCartierSupportContainsNoComponent hV s j hj)
        i (Nat.lt_of_succ_le hi) z hz

theorem center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups) :
    ∀ i < s.length, ∀ z : s.schemeAt i, z ∈ (s.center i).support →
      ∀ y : Y, h y ≠ (s.projectionToBase i) z := by
  intro i hi z hz y hy
  have hz' : z ∈ (↑((s.center i).support) : Set (s.schemeAt i)) := hz
  have hzc : z ∈ orderAtLeastLocus (s.ideal i) T.mult := s.center_order i hi hz'
  have himg := projectionToBase_mem_orderAtLeastLocus hV s i hi.le z hzc
  rw [← hy] at himg
  have hmem : y ∈ (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) := himg
  rw [hempty] at hmem
  simp at hmem

theorem isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty
    {T : MarkedIdealWithBoundary.{u}} (hV : T.IsAdmissible) {Y : Scheme.{u}} (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Flat h]
    (hempty : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) = ∅) (s : T.SequenceOfBlowups)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' s.toSequenceOfBlowups := by
  have hdisj := center_disjoint_range_of_preimage_orderAtLeastLocus_eq_empty hV h hempty s
  refine (SequenceOfBlowupsPullback.ofBlowupDataOfSeq
      (SequenceOfBlowupsPullback.ofCentersMissImage h (BlowupSequenceData.ofSequenceOfBlowups s.toSequenceOfBlowups)
        (by
          intro i hi z hz y
          rw [BlowupSequenceData.ofSequenceOfBlowups_projectionToBase]
          exact hdisj i hi z hz y)
        (BlowupSequenceData.ofSequenceOfBlowups B') (by exact hB'))).isPullbackSequenceOfBlowups

theorem divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (L : PrincipalizationAssignment.{u}) (j : ℕ) (T : MarkedIdealWithBoundary.{u})
    (hV : T.IsAdmissible)
    (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
    [AlgebraicGeometry.Smooth h]
    (E' : List Y.IdealSheafData)
    (hempty : orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult = ∅)
    (B' : SequenceOfBlowups Y) (hB' : B'.length = 0) :
    IsPullbackBlowupSequence h B' ((canonicalAlgorithmRules hres).divisorFamily L j T).toSequenceOfBlowups := by
  have := hV.charZero
  have := hV.smooth
  have hsub : (⇑h ⁻¹' orderAtLeastLocus T.ideal T.mult) ⊆ ∅ := by
    intro y hy
    have hy' : y ∈ orderAtLeastLocus (T.ideal.comap h) T.mult := by
      rw [orderAtLeastLocus_comap T.base T.structMap h T.ideal T.mult]
      exact hy
    have hy2 : y ∈ orderAtLeastLocus ((T.pullbackAlong Y q h).withBoundary E').ideal T.mult := hy'
    rw [hempty] at hy2
    exact hy2
  exact isPullbackSequenceOfBlowups_of_preimage_orderAtLeastLocus_empty hV h (Set.subset_empty_iff.mp hsub)
    ((canonicalAlgorithmRules hres).divisorFamily L j T) B' hB'

end DivisorReductionEmptyOrderLocus

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothBaseChangeOnDivisor\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.IsoBlowupRemovalBaseChange\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceIsomorphism\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.BoundaryRelabeling\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransformOffCenter\nimport Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformFlatBaseChange\nimport Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem map_comap_id {W : Scheme.{u}} (l : List W.IdealSheafData) :
    List.map (fun D : W.IdealSheafData => D.comap (𝟙 W)) l = l := by
  induction l with
  | nil => rfl
  | cons a t ih => simp [Scheme.IdealSheafData.comap_id]

private theorem take_eraseIdx_append_singleton {α : Type*} (A : List α) (e : α) (j n : ℕ)
    (hj : j < A.length) (hn : n = A.length - 1) :
    List.take n ((A ++ [e]).eraseIdx j) = A.eraseIdx j := by
  subst hn
  have hlen : (A.eraseIdx j).length = A.length - 1 := by
    rw [List.length_eraseIdx, ite_eq_left hj]
  rw [List.eraseIdx_append_of_lt_length hj, ← hlen, List.take_left]

private theorem take_length_sub_one_eraseIdx {α : Type*} (A : List α) (j n : ℕ) (hj : j < A.length)
    (hn : n = A.length - 1) : List.take n (A.eraseIdx j) = A.eraseIdx j := by
  subst hn
  refine List.take_of_length_le ?_
  rw [List.length_eraseIdx, ite_eq_left hj]

private theorem top_pow {Y : Scheme.{u}} (m : ℕ) :
    (⊤ : Y.IdealSheafData) ^ m = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

private theorem residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor {X Y : Scheme.{u}} (g : Y ⟶ X)
    (A F : X.IdealSheafData) (F' : Y.IdealSheafData) (m : ℕ) (hF' : F' = F.comap g)
    (hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor F') (hex : ∃ B : X.IdealSheafData, F ^ m * B = A) :
    residualByPow (A.comap g) F' m = (residualByPow A F m).comap g := by
  have hdown : F ^ m * residualByPow A F m = A := pow_mul_residualByPow A F m hex
  have hup : F' ^ m * (residualByPow A F m).comap g = A.comap g := by
    rw [hF', ← Scheme.IdealSheafData.comap_pow, ← Scheme.IdealSheafData.comap_mul, hdown]
  have hup2 : F' ^ m * residualByPow (A.comap g) F' m = A.comap g :=
    pow_mul_residualByPow (A.comap g) F' m ⟨_, hup⟩
  exact (hcart.pow m).eq_of_mul_eq_mul (hup2.trans hup.symm)

private theorem sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat {X Y : Scheme.{u}} (g : Y ⟶ X)
    (hX : AlgebraicGeometry.IsNoetherian X) (hY : AlgebraicGeometry.IsNoetherian Y)
    (hflat : AlgebraicGeometry.Flat g)
    (Z : X.IdealSheafData) (hZ : Blowup.IsBlowupAlongIdealSheaf (𝟙 X) Z) (Z' : Y.IdealSheafData) (hZ' : Z' = Z.comap g)
    (B : List X.IdealSheafData) (E : List Y.IdealSheafData)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (List.map (fun D => D.comap g) B) E)
    (j : ℕ) (hj : j < B.length) (hjE : j < E.length)
    (htake : List.take (j + 1) E = List.take (j + 1) (List.map (fun D => D.comap g) B)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (E.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 Y) Z') (List.map (fun D => D.comap (𝟙 Y)) E)
          ++ [Blowup.exceptionalIdeal (𝟙 Y) Z']).eraseIdx j))
      (List.map (fun D => D.comap g)
        (List.take (B.length - 1)
          ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
            ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx j))) := by
  have := hX
  have := hY
  have := hflat
  subst hZ'
  have hst : ∀ D : X.IdealSheafData,
      (Blowup.strictTransform (𝟙 X) Z D).comap g
        = Blowup.strictTransform (𝟙 Y) (Z.comap g) (D.comap g) := fun D =>
    comap_strictTransform_of_flat_of_isLocallyNoetherian (𝟙 X) g (𝟙 Y) g
      (CategoryTheory.IsPullback.id_vert g) Z D hZ
  have hcomp : List.map ((fun D : X.IdealSheafData => D.comap g)
        ∘ Blowup.strictTransform (𝟙 X) Z) B
      = List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
          (List.map (fun D : X.IdealSheafData => D.comap g) B) := by
    rw [List.map_map]
    exact List.map_congr_left (fun D _ => hst D)
  rw [map_comap_id, map_comap_id,
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 Y) (Z.comap g)) E)
      (Blowup.exceptionalIdeal (𝟙 Y) (Z.comap g)) j (E.length - 1) (by simpa using hjE) (by simp),
    take_eraseIdx_append_singleton (List.map (Blowup.strictTransform (𝟙 X) Z) B)
      (Blowup.exceptionalIdeal (𝟙 X) Z) j (B.length - 1) (by simpa using hj) (by simp),
    ← List.eraseIdx_map, List.map_map, hcomp]
  refine ((MarkedIdealWithBoundary.SameNontrivialBoundary.map (Blowup.strictTransform (𝟙 Y) (Z.comap g))
    (strictTransform_top (𝟙 Y) (Z.comap g)) hBE).eraseIdx j ?_).symm
  rw [← List.map_take, ← List.map_take, ← List.map_take, htake, List.map_take]

theorem lowerIdealAfterBlowup_pullbackAlong_of_smooth
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              lowerIdealAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE =
                (lowerIdealAfterBlowup T j hj).comap h := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hOx : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞) :=
    (MarkedIdealWithBoundary.isOrderBoundedByMult_iff T).1 hO
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hOx j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hcart : Blowup.IsLocallyGeneratedByNonZeroDivisor (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) := by
    have hb := hblow ((T.pullbackAlong Y q h).withBoundary E') hV' j hjE
    have hc := isLocallyGeneratedByNonZeroDivisor_exceptionalIdeal hb
    rwa [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id] at hc
  have key := residualByPow_comap_of_isLocallyGeneratedByNonZeroDivisor h T.ideal (containedComponentsIdeal T j hj)
      (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) T.mult hpre hcart hex
  simp only [lowerIdealAfterBlowup, Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  exact key

theorem lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
    (hblow : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (j : ℕ) (hj : j < T.boundary.length), Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj)) :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec (CommRingCat.of T.base)) (h : Y ⟶ T.scheme)
        [AlgebraicGeometry.Smooth h], h ≫ T.structMap = q →
        ∀ (E' : List Y.IdealSheafData),
          MarkedIdealWithBoundary.SameNontrivialBoundary (T.pullbackAlong Y q h).boundary E' →
          ∀ (j : ℕ) (hj : j < T.boundary.length) (hjE : j < E'.length),
            List.take (j + 1) E' = List.take (j + 1) (T.pullbackAlong Y q h).boundary →
            ((T.pullbackAlong Y q h).withBoundary E').IsAdmissible →
            T.IsOrderBoundedByMult →
            containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE = (containedComponentsIdeal T j hj).comap h →
              MarkedIdealWithBoundary.SameNontrivialBoundary
                (List.take (E'.length - 1)
                  ((lowerBoundaryAfterBlowup ((T.pullbackAlong Y q h).withBoundary E') j hjE).eraseIdx j))
                (List.map (fun D => D.comap h)
                  (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j))) := by
  intro T hV Y q h hsm hq E' hBE j hj hjE htake hV' hO hpre
  have hsmooth : AlgebraicGeometry.Smooth h := hsm
  have hbdry : (T.pullbackAlong Y q h).boundary
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) T.boundary :=
    MarkedIdealWithBoundary.pullbackAlong_boundary T Y q h
  rw [hbdry] at hBE htake
  exact sameNontrivialBoundary_eraseIdx_strictTransform_comap_of_flat h hV.isNoetherian hV'.isNoetherian inferInstance
    (containedComponentsIdeal T j hj) (hblow T hV j hj)
    (containedComponentsIdeal ((T.pullbackAlong Y q h).withBoundary E') j hjE) hpre
    T.boundary E' hBE j hj hjE htake

theorem comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup
    (htwist : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
      ∀ (j : ℕ) (hj : j < T.boundary.length),
        ∃ B : T.scheme.IdealSheafData, B * containedComponentsIdeal T j hj ^ T.mult = T.ideal)
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hO : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    (lowerIdealAfterBlowup T j hj).comap h = (lowerIdealWithoutBlowup T).comap h := by
  have hex : ∃ B : T.scheme.IdealSheafData, containedComponentsIdeal T j hj ^ T.mult * B = T.ideal := by
    obtain ⟨B, hB⟩ := htwist T hV hO j hj
    exact ⟨B, by rw [mul_comm]; exact hB⟩
  have hdown : containedComponentsIdeal T j hj ^ T.mult * residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult = T.ideal :=
    pow_mul_residualByPow T.ideal (containedComponentsIdeal T j hj) T.mult hex
  have hup := congrArg (fun I : T.scheme.IdealSheafData => I.comap h) hdown
  simp only [Scheme.IdealSheafData.comap_mul, Scheme.IdealSheafData.comap_pow, htop,
    top_pow, Scheme.IdealSheafData.top_mul] at hup
  simp only [lowerIdealAfterBlowup, lowerIdealWithoutBlowup, Blowup.exceptionalIdeal_eq_comap,
    Scheme.IdealSheafData.comap_id]
  exact hup

theorem comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
    (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) (Y : Scheme.{u}) (h : Y ⟶ T.scheme)
    (htop : (containedComponentsIdeal T j hj).comap h = ⊤) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryAfterBlowup T j hj).eraseIdx j)))
      (List.map (fun D => D.comap h)
        (List.take (T.boundary.length - 1) ((lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
  have hnoT : AlgebraicGeometry.IsNoetherian T.scheme := hV.isNoetherian
  have hstT : ∀ D : T.scheme.IdealSheafData,
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj) D).comap h = D.comap h := by
    intro D
    have hg : ((containedComponentsIdeal T j hj).comap (𝟙 T.scheme)).comap h = ⊤ := by
      rw [Scheme.IdealSheafData.comap_id]; exact htop
    have h2 := strictTransform_comap_of_comap_center_eq_top (𝟙 T.scheme) (containedComponentsIdeal T j hj) D h hg
    rw [h2, Scheme.IdealSheafData.comap_id]
  have hR0 : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj))
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (𝟙 T.scheme)) T.boundary)
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := rfl
  have hR : lowerBoundaryAfterBlowup T j hj
      = List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary
        ++ [Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)] := by
    rw [hR0, map_comap_id]
  have key : List.map (fun D : T.scheme.IdealSheafData => D.comap h)
        ((List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary).eraseIdx j)
      = List.map (fun D : T.scheme.IdealSheafData => D.comap h) (T.boundary.eraseIdx j) := by
    rw [← List.eraseIdx_map, ← List.eraseIdx_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun D _ => hstT D)
  rw [hR, lowerBoundaryWithoutBlowup_eq T,
    take_eraseIdx_append_singleton
      (List.map (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)) T.boundary)
      (Blowup.exceptionalIdeal (𝟙 T.scheme) (containedComponentsIdeal T j hj)) j (T.boundary.length - 1)
      (by simpa using hj) (by simp),
    take_length_sub_one_eraseIdx T.boundary j (T.boundary.length - 1) hj rfl, key]
  exact MonomialCenter.sameNontrivialBoundary_refl _

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BoundaryReindexing\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.TypeStar\nimport Std.Tactic.BVDecide.Normalize.BitVec\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

namespace DivisorReduction

private theorem filter_map_eq_of_filter_eq {α : Type*} (p : α → Bool) (g : α → α)
    (hpg : ∀ a, p a = false → p (g a) = false) {A B : List α}
    (hAB : List.filter p A = List.filter p B) :
    List.filter p (A.map g) = List.filter p (B.map g) := by
  have key : ∀ L : List α,
      List.filter p (L.map g) = List.filter p ((List.filter p L).map g) := by
    intro L
    induction L with
    | nil => rfl
    | cons a t ih =>
      by_cases ha : p a = true
      · simp [List.filter_cons, ha, ih]
      · have ha' : p a = false := by simpa using ha
        have hga : p (g a) = false := hpg a ha'
        simp [ha', hga, ih]
  rw [key A, key B, hAB]

private theorem sameNontrivialBoundary_map {X : Scheme.{u}} (g : X.IdealSheafData → X.IdealSheafData)
    (hg : g ⊤ = ⊤) {A B : List X.IdealSheafData} (h : MarkedIdealWithBoundary.SameNontrivialBoundary A B) :
    MarkedIdealWithBoundary.SameNontrivialBoundary (A.map g) (B.map g) := by
  rw [MarkedIdealWithBoundary.sameNontrivialBoundary_iff] at h ⊢
  unfold MarkedIdealWithBoundary.nontrivialPart at h ⊢
  refine filter_map_eq_of_filter_eq _ g ?_ h
  intro a ha
  have ha' : a = ⊤ := by simpa using ha
  subst ha'
  simp [hg]

private theorem sameNontrivialBoundary_take_eraseIdx_strictTransform {X : Scheme.{u}} (Z : X.IdealSheafData)
    (A B : List X.IdealSheafData) (a b : ℕ) (ha : a < A.length) (hb : b < B.length)
    (h : MarkedIdealWithBoundary.SameNontrivialBoundary (A.eraseIdx a) (B.eraseIdx b)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (A.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) A)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx a))
      (List.take (B.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) B)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx b)) := by
  have hcomap : ∀ I : X.IdealSheafData, I.comap (𝟙 X) = I := by
    intro I
    simp
  have hgtop : (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) ⊤
      = (⊤ : X.IdealSheafData) := by
    show Blowup.strictTransform (𝟙 X) Z ((⊤ : X.IdealSheafData).comap (𝟙 X)) = ⊤
    rw [hcomap]
    have h1 := comap_le_strictTransform (𝟙 X) Z (⊤ : X.IdealSheafData)
    rw [hcomap] at h1
    exact le_antisymm le_top h1
  have key : ∀ (C : List X.IdealSheafData) (c : ℕ), c < C.length →
      List.take (C.length - 1)
        ((List.map (Blowup.strictTransform (𝟙 X) Z) (List.map (fun D => D.comap (𝟙 X)) C)
          ++ [Blowup.exceptionalIdeal (𝟙 X) Z]).eraseIdx c)
        = List.map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
            (C.eraseIdx c) := by
    intro C c hc
    have hlen : (List.map (fun D : X.IdealSheafData =>
        Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X))) (C.eraseIdx c)).length = C.length - 1 := by
      rw [List.length_map]
      exact List.length_eraseIdx_of_lt hc
    have hmap : ∀ f : X.IdealSheafData → X.IdealSheafData, c < (C.map f).length := by
      intro f
      rw [List.length_map]
      exact hc
    simp only [List.map_map, Function.comp_def]
    rw [List.eraseIdx_append_of_lt_length (hmap _)]
    rw [List.eraseIdx_map, ← hlen, List.take_append_of_le_length (Nat.le_refl _),
      List.take_length]
  rw [key A a ha, key B b hb]
  exact sameNontrivialBoundary_map (fun D : X.IdealSheafData => Blowup.strictTransform (𝟙 X) Z (D.comap (𝟙 X)))
    hgtop h

theorem lowerIdealAfterBlowup_withBoundary_eq_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩) :
    lowerIdealAfterBlowup (T.withBoundary L₂) j₂ hj₂ = lowerIdealAfterBlowup (T.withBoundary L₁) j₁ hj₁ := by
  unfold lowerIdealAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  rfl

theorem sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq (T : MarkedIdealWithBoundary.{u}) (L₁ L₂ : List T.scheme.IdealSheafData)
    (j₁ : ℕ) (hj₁ : j₁ < L₁.length) (j₂ : ℕ) (hj₂ : j₂ < L₂.length)
    (heq : L₁.get ⟨j₁, hj₁⟩ = L₂.get ⟨j₂, hj₂⟩)
    (hBE : MarkedIdealWithBoundary.SameNontrivialBoundary (L₂.eraseIdx j₂) (L₁.eraseIdx j₁)) :
    MarkedIdealWithBoundary.SameNontrivialBoundary
      (List.take (L₂.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₂) j₂ hj₂).eraseIdx j₂))
      (List.take (L₁.length - 1) ((lowerBoundaryAfterBlowup (T.withBoundary L₁) j₁ hj₁).eraseIdx j₁)) := by
  unfold lowerBoundaryAfterBlowup
  rw [containedComponentsIdeal_withBoundary_congr T L₁ L₂ j₁ hj₁ j₂ hj₂ heq]
  exact sameNontrivialBoundary_take_eraseIdx_strictTransform
    (containedComponentsIdeal (T.withBoundary L₂) j₂ hj₂) L₂ L₁ j₂ j₁ hj₂ hj₁ hBE

theorem boundaryReindexingInvariance : BoundaryReindexingInvariance.{u} :=
  ⟨smooth_id, surjective_id, lowerIdealAfterBlowup_withBoundary_eq_of_get_eq, sameNontrivialBoundary_lowerBoundaryAfterBlowup_of_get_eq⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing =====

-- ===== clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction =====
-- clump-header: {"m": "Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction", "h": "module\n\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionHypotheses\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.KernelSupport\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientEmbeddingCompatibility\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BalancedDivisorReduction\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.BaseChangeMorphismProperties\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsSmoothPullback\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.EmptyOrderLocus\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.InducedSubschemePullback\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PreimageSupportOfAdmissible\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerIdealFunctoriality\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.NontrivialBoundaryReindexing\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PrependedAmbientSequence\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.MarkedPullbackSquare\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.SmoothBaseChangeCompatibility\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplittingFlatPullback\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.StrictPullbackComposition\nimport Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.DimensionNonincreasing\npublic import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.OrderOffExceptionalDivisor\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\n\n"}
section -- clump:auto
@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le : ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
    (∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞)) →
    ∀ (j : ℕ) (hj : j < T.boundary.length),
      ∃ B : T.scheme.IdealSheafData, B * DivisorReduction.containedComponentsIdeal T j hj ^ T.mult = T.ideal := by
  intro T hV _ j hj
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  exact ⟨J, by rw [mul_comm]; exact hJ⟩

private theorem orderAtComapOffExceptionalLocus : OrderAtComapOffExceptionalLocus.{u} := by
  delta OrderAtComapOffExceptionalLocus
  exact fun T hT X' π Z hπ x' hx' A =>
    orderAt_comap_eq_of_notMem_exceptionalIdeal T Z X' π hπ x' hx' A

private theorem smoothPullbackCompatibility_of_divisorReductionTermination (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hfacts : DivisorReductionTerminationProperties hres blowupPreservesNoetherian) :
    DivisorReduction.SmoothPullbackCompatibility.{u} := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact comap_ne_top_of_surjective
  · intro T hV Y q h inst hq m
    exact DivisorReduction.orderAtLeastLocus_comap_of_smooth T hV Y q h m
  · exact DivisorReduction.isPullback_subschemeMapOfComap
  · exact DivisorReduction.smooth_of_isPullback
  · exact DivisorReduction.lowerIdealAfterBlowup_pullbackAlong_of_smooth exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_smooth
      isBlowupAlongIdealSheaf_id_containedComponentsIdeal
  · exact DivisorReduction.containedComponentsIdeal_pullbackAlong_of_smooth hfacts

private theorem emptyPulledBackCenterCompatibility : DivisorReduction.EmptyPulledBackCenterCompatibility.{u} := by
  refine ⟨?_, ?_⟩
  · intro T hV hO j hj Y h htop
    exact DivisorReduction.comap_lowerIdealAfterBlowup_eq_comap_lowerIdealWithoutBlowup exists_mul_containedComponentsIdeal_pow_eq_ideal_of_orderAt_le
      T hV hO j hj Y h htop
  · intro T hV j hj Y h htop
    exact DivisorReduction.comap_lowerBoundaryAfterBlowup_sameNontrivialBoundary_of_eq_top
      T hV j hj Y h htop

private theorem pushedBlowupSequenceProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    PushedBlowupSequenceProperties hres blowupPreservesNoetherian := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T hV j hj
    exact DivisorReduction.isOpen_preimage_support_containedComponentsIdeal T j hj
      (DivisorReduction.preimageSupportEqComponentsInOrderLocus_of_isAdmissible T hV j hj)
  · intro T inst j hj s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_isoObjZero hres blowupPreservesNoetherian T j hj s hpr hmk
  · intro T inst j hj hb s hpr hmk
    exact DivisorReduction.ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres blowupPreservesNoetherian T j hj hb s hpr
      hmk
  · intro T hV j hj S
    exact DivisorReduction.isSmoothDivisor_boundary_comap_isoObjZero T hV j hj S
  · intro T inst j hj s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus hres blowupPreservesNoetherian T j hj s hpr
      hmk t ht
  · intro T inst j hj hb s hpr hmk t ht
    exact DivisorReduction.boundaryLocus_subset_preimage_otherBoundaryLocus_succ hres blowupPreservesNoetherian T j hj hb s
      hpr hmk t ht
  · intro T hV
    exact DivisorReduction.one_le_mult_of_isAdmissible T hV
  · intro T hV hOB hbal j hj hpre hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient_of_eq_top hres blowupPreservesNoetherian T hV
      hOB hbal j hj hpre hlow s hpr hmk t ht
  · intro T hV hOB hbal j hj hne hb hlow inst s hpr hmk t ht
    exact DivisorReduction.isSmoothDivisor_ker_embeddingIntoAmbient hres blowupPreservesNoetherian
      T hV hOB j hj hb hlow s hpr hmk
      (fun t _ => DivisorReduction.embeddingIntoAmbient_comp_projectionToBase_eq_comp_subschemeι hres
        blowupPreservesNoetherian T j hj (DivisorReduction.lowerIdealAfterBlowup T j hj)
        (DivisorReduction.lowerBoundaryAfterBlowup T j hj) s hpr t) t ht
  · intro T inst j hj s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_ambientMarkedSeq hres blowupPreservesNoetherian T j hj s hpr hmk t
  · intro T inst j hj hb s hpr hmk t
    exact DivisorReduction.projectionToSpec_eq_comp_prependedAmbientSeq hres blowupPreservesNoetherian T j hj hb s hpr hmk t
  · intro X Y f inst I
    exact support_ker_comp_subset_support_ker I.subschemeι f
  · intro T hV j hj
    exact DivisorReduction.support_containedComponentsIdeal_subset_support_boundary T j hj

private theorem divisorReductionStepProperties_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReductionStepProperties hres blowupPreservesNoetherian :=
  (divisorReductionProperties_of_blowupPreservesNoetherian hres blowupPreservesNoetherian).toDivisorReductionStepProperties

theorem divisorReductionHypotheses_canonicalAlgorithmRules (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u}) :
    DivisorReduction.DivisorReductionHypotheses hres := by
  have hstepProps := divisorReductionStepProperties_canonicalAlgorithmRules hres
  have hfacts := hstepProps.toDivisorReductionTerminationProperties
  refine
    { trivial_of_coSupport_empty := ?_
      baseChange := smoothPullbackCompatibility_of_divisorReductionTermination hres hfacts
      smoothImpliesFlat := ⟨fun X Y f hf => by have := hf; infer_instance⟩
      degenerateTransversal := emptyPulledBackCenterCompatibility
      boundaryReindexingInvariance := DivisorReduction.boundaryReindexingInvariance
      divisorReduction := hstepProps
      pushedBlowupSequenceProperties := pushedBlowupSequenceProperties_canonicalAlgorithmRules hres }
  intro L j T hV hj Y q h inst hq E' hV' hne hempty B' hB'
  exact DivisorReductionEmptyOrderLocus.divisorFamily_isPullbackSequenceOfBlowups_of_orderAtLeastLocus_empty hres L j T hV Y q h E'
    hempty B' hB'

end FunctorialResolution.EmbeddedResolution
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.CanonicalDivisorReduction =====
