module

public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsConeTangentAverage
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsArea
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

open scoped ENNReal

noncomputable section

def ConeGraphCover.Statement : Prop :=
  ∀ (n m : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)), IsProjPrime J → 0 < m → m ≤ n →
    (∀ᵐ π : Fin m → Fin n → ℂ, ∀ᵐ w : EuclideanSpace ℂ (Fin m), fibreCount h J π w ≠ ⊤) →
    ∃ (e : ℕ → (Fin n ≃ Fin m ⊕ Fin (n - m))) (Ω : ℕ → Set (EuclideanSpace ℂ (Fin m)))
      (Φ : ℕ → EuclideanSpace ℂ (Fin m) → EuclideanSpace ℂ (Fin (n - m))),
      (∀ i, IsOpen (Ω i) ∧ DifferentiableOn ℂ (Φ i) (Ω i) ∧
        graphPt (e i) (Φ i) '' Ω i ⊆ coneSet h J ∧
        ∀ x ∈ Ω i, coneTangent h J (graphPt (e i) (Φ i) x) =
          LinearMap.range (fderiv ℂ (graphPt (e i) (Φ i)) x :
            EuclideanSpace ℂ (Fin m) →ₗ[ℂ] EuclideanSpace ℂ (Fin n))) ∧
      Measure.hausdorffMeasure ((2 * m : ℕ) : ℝ) (coneSet h J \ ⋃ i, graphPt (e i) (Φ i) '' Ω i) = 0

end

end GroundTheory.Heights₂.Heights
