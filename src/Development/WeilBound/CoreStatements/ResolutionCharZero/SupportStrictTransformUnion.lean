module

public import Development.ResolutionOfSingularities.Statements
public import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MarkedBlowupSequenceBoundary
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

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

namespace PositivityTheory.ResPlug.WeightsCompactStabilizer

open FunctorialResolution

def GTransform : Prop :=
  ∀ (X X₁ : Scheme.{0}) (π : X₁ ⟶ X) (Z D : X.IdealSheafData), IsLocallyNoetherian X → IsLocallyNoetherian X₁ →
    IsBlowup π Z →
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X)

theorem strictTransform_eq_blowup {X X₁ : Scheme.{0}} (π : X₁ ⟶ X) (Z D : X.IdealSheafData) :
    strictTransform π Z D = Blowup.strictTransform π Z D := rfl

theorem support_strictTransform_union {X X₁ : Scheme.{0}} [IsLocallyNoetherian X₁] (π : X₁ ⟶ X)
    (Z D : X.IdealSheafData) :
    ((strictTransform π Z D).support : Set X₁) ∪ π.base ⁻¹' (Z.support : Set X) =
      π.base ⁻¹' (D.support : Set X) ∪ π.base ⁻¹' (Z.support : Set X) := by
  rw [strictTransform_eq_blowup]
  apply Set.Subset.antisymm
  · refine Set.union_subset_union_left _ ?_
    exact EmbeddedResolution.support_strictTransform_subset_preimage π Z D
  · rintro x (hx | hx)
    · by_cases hz : π.base x ∈ (Z.support : Set X)
      · exact Or.inr hz
      · exact Or.inl ((EmbeddedResolution.mem_support_strictTransform_iff_of_notMem_support π Z D x hz).2 hx)
    · exact Or.inr hx

theorem gTransform : GTransform := fun _ _ π Z D _ _ _ => support_strictTransform_union π Z D

end PositivityTheory.ResPlug.WeightsCompactStabilizer
