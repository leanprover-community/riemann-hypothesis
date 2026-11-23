module

public import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsStrongResolution (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (s : SequenceOfBlowups X) : Prop :=
  AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) ∧
  AlgebraicGeometry.IsProper s.lastStructMap ∧
  CategoryTheory.IsIso
    (AlgebraicGeometry.morphismRestrict s.lastStructMap f.smoothLocus) ∧
  Dense (s.lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
  s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
  IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f))

theorem isStrongResolutionRule_iff (R : ResolutionRule.{u}) :
    IsStrongResolutionRule R ↔
      ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
        (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
        IsStrongResolution k X f (R k X f) :=
  Iff.rfl

end FunctorialResolution.EmbeddedResolution

end
