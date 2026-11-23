module

public import Formalism.TruncatedSeriesCounting.AprimeArith
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace Formalism.ExponentWindows

def AprimeCuts : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ ℓ : ℕ, 11 ≤ ℓ →
    ∀ (n j : ℕ) [NeZero n] (size : ZMod n → ℕ) (b w S η : ℕ) (rr : ℝ),
      1 ≤ j → j + 1 ≤ n →
      (∀ i, (b ≤ size i ∧ size i ≤ b + η) ∨ size i ≤ w) →
      C * ((j : ℝ) + 1) * ((w + S + η : ℕ) + 1 : ℝ) ≤ b →
      (∀ a : ZMod n, (b ≤ size a ∧ size a ≤ b + η) → ∀ k : ℕ, 1 ≤ k → k ≤ j →
        (b ≤ size (a - k) ∧ size (a - k) ≤ b + η) →
        ∀ k' : ℕ, 1 ≤ k' → k' ≤ j → ¬ (b ≤ size (a - k - k') ∧ size (a - k - k') ≤ b + η)) →
      rr ≤ 20 * (((w + S + η : ℕ) : ℝ) / ℓ + ((b + η + S : ℕ) : ℝ) / ((ℓ : ℝ) - 1) ^ (j + 1) +
        Real.logb ℓ (b + η + S : ℕ) + 1) →
      ∃ (cuts : Finset (ZMod n)) (ell : ZMod n → ℕ), cuts.Nonempty ∧
        ∀ c ∈ cuts,
          (∀ k : ℕ, 1 ≤ k → k ≤ j → ¬ (b ≤ size (c + k) ∧ size (c + k) ≤ b + η)) ∧
          j ≤ ell c ∧ ell c ≤ 3 * j + 1 ∧ c - (ell c : ZMod n) ∈ cuts ∧
          (∀ k : ℕ, 1 ≤ k → k < ell c → c - k ∉ cuts) ∧
          ((Finset.range (ell c)).filter
            (fun k : ℕ => b ≤ size (c - (k : ZMod n)) ∧ size (c - (k : ZMod n)) ≤ b + η)).card ≤ 2 ∧
          (∀ k : ℕ, k < ell c → (b ≤ size (c - k) ∧ size (c - k) ≤ b + η) →
            max (w + S + η) 1 < size (c - k)) ∧
          (∀ k k' : ℕ, k < ell c → k' < k →
            (b ≤ size (c - k) ∧ size (c - k) ≤ b + η) →
            (b ≤ size (c - k') ∧ size (c - k') ≤ b + η) →
            (size (c - k') : ℝ) < ℓ * size (c - k) ∧ (size (c - k') : ℝ) ≤ ℓ * size (c - k) / 2 ∧
            Formalism.TruncatedSeriesCounting.WachCoordinates.a0E ℓ (max (w + S + η) 1) (b + η + S) j (3 * j + 1) rr <
              (size (c - k) : ℝ) / 2)

end Formalism.ExponentWindows
