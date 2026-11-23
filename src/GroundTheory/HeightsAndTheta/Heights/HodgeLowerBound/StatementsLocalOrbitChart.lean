module

public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
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

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def LocalOrbitChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
    (y : (Σ k, ι k) → Ω) (n : ℕ), IsArithVar (mCoordIdeal y) (n + 1) → SmoothGenericFibreM y →
    ∀ z₀ ∈ mcPts (mCoordIdeal y), ∃ N : Set ((Σ k, ι k) → ℂ), IsOpen N ∧ z₀ ∈ N ∧
      ∃ κ : ((Σ k, ι k) → ℂ) → (Fin n → ℂ), AnalyticOnNhd ℂ κ N ∧
        (∀ z ∈ N, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ N ∧ κ (torusSmul c z) = κ z) ∧
        ∀ z ∈ N ∩ mcPts (mCoordIdeal y), ∀ z' ∈ N ∩ mcPts (mCoordIdeal y), κ z = κ z' →
          ∃ c : K → ℂ, (∀ k, c k ≠ 0) ∧ z' = torusSmul c z

namespace Line

end Line

end GroundTheory.Heights₂.Heights.LowerBoundFree
