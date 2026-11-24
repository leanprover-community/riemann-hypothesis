module

public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.StatementsFiniteAlgebraLengthSum
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.LengthSumLocalizations
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FieldNumbers

open Module

theorem FiniteAlgebraLengthSum.proof : FiniteAlgebraLengthSum.Statement := by
  classical
  intro A B _ _ _ _ _ ι _ 𝔪 h𝔪 hinj hall C _ _ hC α
  have : ∀ i, (𝔪 i).IsMaximal := h𝔪
  have : ∀ i, IsLocalization.AtPrime (C i) (𝔪 i) := hC
  have hrange : LinearMap.range (LinearMap.lsmul A B α) =
      (Ideal.span {algebraMap A B α}).restrictScalars A := by
    ext b
    simp only [LinearMap.mem_range, LinearMap.lsmul_apply, Submodule.restrictScalars_mem,
      Ideal.mem_span_singleton', Algebra.smul_def, mul_comm]
  rw [(Submodule.quotEquivOfEq _ _ hrange).length_eq,
    (Submodule.Quotient.restrictScalarsEquiv A (Ideal.span {algebraMap A B α})).length_eq,
    LengthSumLocalizations.length_eq_sum 𝔪 C hinj hall A]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ring.ord, ← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (C i)
    (Ideal.span {algebraMap A B α})).toLinearEquiv.length_eq, Ideal.map_span, Set.image_singleton]

end GroundTheory.Heights₂.Heights.FieldNumbers
