module

public import Formalism.LogVandermondeBounds.LogRatioUpperBound
public import Formalism.LogVandermondeBounds.LogRatioLowerBound
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

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

def UpperPlace : Prop :=
  ∀ (ε x : ℝ), 0 < ε → 1 ≤ x → ∀ (k m : ℕ) (Δ C₃ : ℝ) (u v b w : ℕ → ℝ),
    2 ≤ m → Even m → 2 ≤ k → (m : ℝ) ≤ k → 1 ≤ Δ → 1 ≤ C₃ →
    PlaceData x Δ (x * Real.exp (x ^ ε)) (Real.exp (x ^ ε)) k m u v b w →
    (∀ i j, i < j → j < k → 1 ≤ u i - u j) →
    0 < dimVN u k ∧ 0 < dTau k m (rowPar k v b) ∧
    Real.log (4 * dTau k m (rowPar k v b) *
        (C₃ * ((k - 1 + m / 2 : ℕ) : ℝ) * ((m / 2 : ℕ) : ℝ) * ((k - 1 + m : ℕ) : ℝ) * (v 0 + b (m - 1))) ^
          ((k - 1 + m / 2) * (m / 2))) - Real.log (dimVN u k)
      ≤ (k : ℝ) * m * (Real.log C₃ + 5 * Real.log (2 * k) + 5 * x ^ ε + 10)

end Formalism.LogVandermondeBounds.StandardLattice
