module

public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
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

namespace FunctorialResolution.Blowup

def StrictTransformIsBlowupOfClosedSubscheme : Prop :=
  ∀ (X X₁ S : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X]
    (j : S ⟶ X) [AlgebraicGeometry.IsClosedImmersion j] (π : X₁ ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z →
    (∀ T ∈ irreducibleComponents (↥S), ¬ (j.base '' T) ⊆ (Z.support : Set ↥X)) →
    ∃ ψ : (strictTransform π Z j.ker).subscheme ⟶ S,
      ψ ≫ j = (strictTransform π Z j.ker).subschemeι ≫ π ∧
        IsBlowupAlongIdealSheaf ψ (Z.comap j)

def BlowupIsProper : Prop :=
  ∀ (X X' : Scheme.{u}) [AlgebraicGeometry.IsLocallyNoetherian X] (π : X' ⟶ X)
    (Z : X.IdealSheafData), IsBlowupAlongIdealSheaf π Z → AlgebraicGeometry.IsProper π

def BlowupIsIsoOffCenter : Prop :=
  ∀ (X X' : Scheme.{u}) (π : X' ⟶ X) (Z : X.IdealSheafData),
    IsBlowupAlongIdealSheaf π Z →
      CategoryTheory.IsIso (AlgebraicGeometry.morphismRestrict π Z.support.compl)

end FunctorialResolution.Blowup
