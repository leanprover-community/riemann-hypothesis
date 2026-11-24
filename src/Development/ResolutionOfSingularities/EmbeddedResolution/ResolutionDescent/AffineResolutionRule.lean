module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
public import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
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

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def AffineEmbedsIntoAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p],
    ∃ (n : ℕ) (e : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))),
      AlgebraicGeometry.IsClosedImmersion e ∧ NonzeroOnComponents e.ker ∧
        e ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p

def NilIsStrictNormalCrossingsOnAffineSpace : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    InStrictNormalCrossingPosition (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))
      ([] : List (affineSpaceIndexedBy k (ULift.{u} (Fin n))).IdealSheafData)

def AffineSpaceIsSmooth : Prop :=
  ∀ (k : Type u) [Field k] (n : ℕ),
    AlgebraicGeometry.Smooth (affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)))

def ClosedEmbeddingsRelatedByAutomorphism : Prop :=
  ∀ (k : Type u) [Field k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p] (n m : ℕ)
    (e₁ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n)))
    [AlgebraicGeometry.IsClosedImmersion e₁]
    (e₂ : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m)))
    [AlgebraicGeometry.IsClosedImmersion e₂],
    e₁ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) = p →
    e₂ ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin m)) = p →
    ∃ Φ : affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)) ≅
            affineSpaceIndexedBy k (ULift.{u} (Fin n ⊕ Fin m)),
      Φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) =
          affineSpaceIndexedByToSpec k (ULift.{u} (Fin n ⊕ Fin m)) ∧
        AffineSpace.homOfVector p (coordVectorInl n m e₁) ≫ Φ.hom =
          AffineSpace.homOfVector p (coordVectorInr n m e₂)

abbrev AffineResolutionRule : Type (u + 1) :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y], SequenceOfBlowups Y

def IsCompatibleWithOpenImmersions (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y V : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pV : V ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pV] [AlgebraicGeometry.QuasiCompact pV]
    [AlgebraicGeometry.IsReduced V] [AlgebraicGeometry.IsAffine V]
    (φ : V ⟶ Y) [AlgebraicGeometry.IsOpenImmersion φ],
    φ ≫ pY = pV → IsPullbackBlowupSequence φ (R k V pV) (R k Y pY)

def IsCompatibleWithEtaleCovers (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y W : Scheme.{u})
    (pY : Y ⟶ Spec (CommRingCat.of k)) (pW : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pY] [AlgebraicGeometry.QuasiCompact pY]
    [AlgebraicGeometry.IsReduced Y] [AlgebraicGeometry.IsAffine Y]
    [AlgebraicGeometry.LocallyOfFiniteType pW] [AlgebraicGeometry.QuasiCompact pW]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ pY = pW → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) →
    IsStrictPullbackBlowupSeq φ (R k W pW) (R k Y pY)

def IsCompatibleWithFieldBaseChange (R : AffineResolutionRule.{u}) : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y]
    [AlgebraicGeometry.IsAffine Y] (K : Type u) [Field K] [CharZero K] [Algebra k K]
    [AlgebraicGeometry.IsReduced (baseChange p K)]
    [AlgebraicGeometry.IsAffine (baseChange p K)],
    IsStrictPullbackBlowupSeq (baseChangeProjection p K)
      (R K (baseChange p K) (baseChangeToSpec p K)) (R k Y p)

def IsInducedByAffineRule (R : AffineResolutionRule.{u}) (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) (B : SequenceOfBlowups Y) : Prop :=
  ∀ (W : Scheme.{u}) (q : W ⟶ Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType q] [AlgebraicGeometry.QuasiCompact q]
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.IsAffine W]
    (φ : W ⟶ Y) [AlgebraicGeometry.Etale φ],
    φ ≫ p = q → (∀ y : ↥Y, ∃ w : ↥W, φ.base w = y) → IsStrictPullbackBlowupSeq φ (R k W q) B

def ExistsGluedBlowupSequence (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithEtaleCovers R →
  ∀ (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u})
    (p : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType p]
    [AlgebraicGeometry.QuasiCompact p] [AlgebraicGeometry.IsReduced Y],
    ∃ B : SequenceOfBlowups Y, (∀ i, i < B.length → B.center i ≠ ⊤) ∧ IsInducedByAffineRule R k Y p B

def InducedRuleCompatibleWithFieldExtension (R : AffineResolutionRule.{u}) : Prop :=
  IsCompatibleWithOpenImmersions R → IsCompatibleWithFieldBaseChange R →
  ∀ F : ResolutionRule.{u},
    (∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
      (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
      [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
      IsInducedByAffineRule R k X f (F k X f)) →
    IsCompatibleWithFieldExtension F

end FunctorialResolution.EmbeddedResolution
