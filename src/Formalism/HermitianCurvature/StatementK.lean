module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.FourierDecayAlt.K

open Matrix Finset Real

def JointTheoremA : Prop :=
  ∀ C₀ : ℝ, 1 ≤ C₀ → ∃ C' C : ℝ, ∀ (Kx Θ : ℝ) (f r : ℕ) (e σ : ℕ → ℝ),
    4 ≤ Kx → 1 ≤ f → C' ≤ Θ → (r : ℝ) * (C₀ / Θ) ^ f ≤ 1 →
    (∀ i, 0 ≤ e i) → (∀ i, 0 ≤ σ i) →
    (∀ i, 1 ≤ i → i ≤ r + 1 →
      σ i ≤ (1 + (C₀ * Θ ^ (-(Kx - 5/2))) ^ f) * √(1 + e i) * σ (i - 1) +
        ∑ t ∈ Icc 2 i, ((C₀ / Θ) ^ f) ^ (t - 1) * σ (i - t)) →
    σ (r + 1) ^ 2 ≤
      (1 + C * ((r : ℝ) + 1) * (C₀ / Θ) ^ f) * (∏ i ∈ Icc 1 (r + 1), (1 + e i)) * σ 0 ^ 2

end Formalism.FourierDecayAlt.K
