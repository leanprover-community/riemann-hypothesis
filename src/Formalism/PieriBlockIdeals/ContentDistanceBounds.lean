module

public import Formalism.PieriBlockIdeals.Statement
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

noncomputable section

open Finset

namespace Formalism.CohomologicalDescent

open Classical

def NoResidue : Prop :=
  ∀ (l : ℕ) (b : ℤ) (t κ : ℕ) (U : Finset ℤ),
    (∀ u ∈ U, u ∉ Finset.Icc b (b + t - 1) → ∀ x ∈ Finset.Icc (b - κ) (b + t - 1 + κ),
      (0 < |u - x| ∧ |u - x| < (l : ℤ)) ∨ ¬ ((l : ℤ) ∣ u - x)) →
    mwCount l b t κ U = 0

def PrimeCount : Prop :=
  ∀ (L : ℝ) (T : Finset ℤ) (P : Finset ℕ), 0 ≤ L → (∀ n ∈ T, n ≠ 0 ∧ ((|n| : ℤ) : ℝ) < L ^ 2) →
    (∀ l ∈ P, l.Prime ∧ L < (l : ℝ) ∧ ∃ n ∈ T, (l : ℤ) ∣ n) → P.card ≤ T.card

def ISum : Prop :=
  ∀ (h : ℕ) (L : ℝ) (xm xp mB : ℤ) (P : Finset ℕ), 0 ≤ L → (h : ℝ) < L ^ 2 → 0 ≤ mB → mB < xm →
    xm ≤ xp → xp ≤ (h : ℤ) → (∀ l ∈ P, l.Prime ∧ L < (l : ℝ)) →
    ∑ l ∈ P, IlInd l xm xp mB * Real.log (l : ℝ) ≤ (((xp - xm : ℤ) : ℝ) + 1) * Real.log (h : ℝ)

end Formalism.CohomologicalDescent
