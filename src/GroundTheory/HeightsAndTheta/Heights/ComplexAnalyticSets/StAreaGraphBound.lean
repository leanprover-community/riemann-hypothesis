module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StGraphJacContinuous
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open MeasureTheory

open scoped ENNReal NNReal

noncomputable section

def AreaGraphBound.Statement : Prop :=
  ∀ (k m : ℕ) (U : Set (EuclideanSpace ℝ (Fin k)))
    (F : EuclideanSpace ℝ (Fin k) → EuclideanSpace ℝ (Fin m)),
    IsOpen U → ContDiffOn ℝ 1 F U → ∀ A ⊆ U, MeasurableSet A →
      ∀ δ : ℝ≥0, 0 < δ → δ < 1 →
        μH[(k : ℝ)] (realGraphPt F '' A) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) ^ (k + 1) *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ∧
          ((1 - δ : ℝ≥0) : ℝ≥0∞) ^ k *
              ∫⁻ x in A, ENNReal.ofReal (graphJac (fderiv ℝ F x :
                EuclideanSpace ℝ (Fin k) →ₗ[ℝ] EuclideanSpace ℝ (Fin m))) ∂(μH[(k : ℝ)]) ≤
            ((1 + δ : ℝ≥0) : ℝ≥0∞) * μH[(k : ℝ)] (realGraphPt F '' A)

end

end GroundTheory.Heights₂.Heights
