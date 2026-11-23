module

public import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.BergmanObjects
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
import GroundTheory.HeightsAndTheta.Heights.ComplexProjective

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.CP

noncomputable section

def ChartTaylorCover.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] [MeasurableSpace X]
    [BorelSpace X] (A : FinHolAtlas D X) (L : HolLineBundle A) (W₀ W₁ : Weight L)
    (dV : SmoothVolume A),
    ∃ r : ℝ, 0 < r ∧ ∃ M c : ℝ, 0 < c ∧ ∀ x : X, ∃ j : Fin A.n, x ∈ (A.chart j).source ∧
      Metric.closedBall (A.chart j x) r ⊆ (A.chart j).target ∧
      (∀ y ∈ Metric.closedBall (A.chart j x) r, c ≤ dV.dens j y) ∧
      ∀ W ∈ [W₀, W₁], ∃ ℓ : (Fin D → ℂ) →L[ℝ] ℝ, ∀ z : Fin D → ℂ, ‖z‖ ≤ r →
        W.φ j ((A.chart j).symm (A.chart j x + z)) ≤ W.φ j x + ℓ z + M * ∑ i, ‖z i‖ ^ 2

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
