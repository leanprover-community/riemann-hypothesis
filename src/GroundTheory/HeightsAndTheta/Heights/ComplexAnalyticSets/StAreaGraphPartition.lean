module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open scoped ENNReal NNReal

noncomputable section

def AreaGraphPartition.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U →
      ∀ r : (EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)) → ℝ≥0, (∀ A, r A ≠ 0) →
        ∃ (t : ℕ → Set (EuclideanSpace ℝ (Fin k)))
          (A : ℕ → EuclideanSpace ℝ (Fin k) →L[ℝ] EuclideanSpace ℝ (Fin m)),
          Pairwise (Function.onFun Disjoint t) ∧ (∀ n, MeasurableSet (t n)) ∧ (∀ n, t n ⊆ U) ∧
            U ⊆ ⋃ n, t n ∧ (∀ n, ApproximatesLinearOn F (A n) (t n) (r (A n))) ∧
              ∀ n, ∀ x ∈ t n, ‖fderiv ℝ F x - A n‖₊ ≤ r (A n)

end

end GroundTheory.Heights₂.Heights
