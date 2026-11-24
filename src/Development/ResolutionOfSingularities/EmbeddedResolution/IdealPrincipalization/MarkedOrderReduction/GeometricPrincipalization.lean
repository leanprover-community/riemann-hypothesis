module

public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.TransformedComponentHypotheses
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.StrictTransformComponents
public import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.TransformedBoundaryComponents
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem MonomialStrictTransformComponents.transformedComponentHypotheses :
    MonomialStrictTransformComponents.TransformedComponentHypotheses.{u} := by
  exact {
    transformed_components := intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf
    strictTransform_components := exists_eq_closure_of_isIrreducibleComponentOf_strictTransform }

theorem principalizationGeometryHypotheses : PrincipalizationGeometryHypotheses.{u} := by
  have h := StrictTransformCase.strictTransformHypotheses_of_residualHypotheses
    (MonomialStrictTransformComponents.strictTransformHypotheses_of_transformedComponents
      MonomialStrictTransformComponents.transformedComponentHypotheses)
  have hOrder : OrderReductionHypotheses.{u} := {
    controlledTransform_orderAt_le := orderAt_controlledTransform_le_of_orderAt_eq_on_center
    strictTransform_components := h.strictTransform_components
    monomial := h.monomial }
  exact geometricHypotheses_of_orderReductionHypotheses hOrder

end FunctorialResolution.EmbeddedResolution

end
