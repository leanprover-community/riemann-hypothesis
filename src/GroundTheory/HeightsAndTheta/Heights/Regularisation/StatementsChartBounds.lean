module

public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Statements
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Regular

open Metric
open ReciprocityTheory.AnForm.A (Mollifier)

noncomputable section

def ChartMollifiedBounds.Statement : Prop :=
  ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ)
    (A : ReciprocityTheory.AnForm.M.FinHolAtlas D X) (R : RegChartData A) (ρ : Mollifier D),
    ∃ C t₀ : ℝ, 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      (∀ j, ∀ x ∈ closure (R.mid j), closedBall (R.chart j x) t ⊆ (R.chart j).target) ∧
      ∀ K : ℝ, 0 ≤ K → ∀ j : Fin R.N, ∀ x ∈ R.mid j,
        -K - C ≤ R.phReg ρ K t j x ∧ R.phReg ρ K t j x ≤ C ∧
          (x ∈ R.Yo → R.ph x ≤ R.phReg ρ K t j x)

end

end GroundTheory.Heights₂.Heights.Regular
