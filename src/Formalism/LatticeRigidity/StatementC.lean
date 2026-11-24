module

public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import Mathlib.RingTheory.FractionalIdeal.Norm
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

namespace Formalism.SA.C

open Finset Real NumberField

def RecHyp (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ) : Prop :=
  0 ≤ ε ∧ 0 ≤ δ ∧ s 0 ≤ M ∧ (∀ i, 0 ≤ s i) ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(s i) ≤ (1 + ε) * √(s (i-1)) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  m 0 = 1 ∧
  (∀ i, 1 ≤ i → i ≤ r + 1 →
    √(m i) ≤ √(m (i-1) + ε * s (i-1)) * (1 + ε) + ∑ t ∈ Icc 2 i, δ ^ (t-1) * √(s (i-t))) ∧
  r * (ε + δ) ≤ 1/10

def RecursionUnrestricted : Prop :=
  ∃ C : ℝ, ∀ (r : ℕ) (ε δ M : ℝ) (s m : ℕ → ℝ), RecHyp r ε δ M s m →
    (∀ i ≤ r + 1, s i ≤ 2 * M) ∧ √(m (r+1)) ≤ 1 + C * r * (ε * M + δ * √M)

noncomputable def chebPt (α β : ℝ) (n : ℕ) (j : Fin (n+1)) : ℝ :=
  (α + β) / 2 + (β - α) / 2 * Real.cos (π * (j : ℕ) / n)


open NumberField in
def BoxSum : Prop :=
  ∃ C : ℝ, ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsTotallyComplex E]
    (b : FractionalIdeal (nonZeroDivisors (𝓞 E)) E), b ≠ 0 →
    ∀ (x : InfinitePlace E → ℝ) (Θ Kx : ℝ), (∀ w, 0 < x w) → 2 < Θ → 3 ≤ Kx →
      Θ ^ Fintype.card (InfinitePlace E) =
        √(FractionalIdeal.absNorm b : ℝ) / ∏ w, x w →
      ∀ S : Finset E, (∀ l ∈ S, l ∈ b ∧ l ≠ 0) →
        ∑ l ∈ S, ∏ w, min 1 ((x w / w l) ^ Kx) ≤
          (C * Θ ^ (-(Kx - 5/2))) ^ Fintype.card (InfinitePlace E)

end Formalism.SA.C
