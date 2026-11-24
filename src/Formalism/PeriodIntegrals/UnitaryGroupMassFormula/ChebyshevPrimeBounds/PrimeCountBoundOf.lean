module

public import Formalism.PeriodIntegrals.PrimeCount
public import Mathlib.NumberTheory.Chebyshev
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

namespace PI.PC

open Real

def chA : ℝ := log 2 / 2 + log 3 / 3 + log 5 / 5 - log 30 / 30

def lf (x : ℝ) : ℝ := log ((Nat.factorial ⌊x⌋₊ : ℕ) : ℝ)

def chD (x : ℝ) : ℝ := lf x - lf (x / 2) - lf (x / 3) - lf (x / 5) + lf (x / 30)

def LfUpper : Prop := ∀ y : ℝ, 1 ≤ y → lf y ≤ y * log y - y + log y / 2 + 1

def LfLower : Prop := ∀ y : ℝ, 1 ≤ y → y * log y - y - log y / 2 + 9 / 10 ≤ lf y

def ANum : Prop := 0.92129 ≤ chA ∧ chA ≤ 0.9213

def DUpper : Prop := ∀ x : ℝ, 30 ≤ x → chD x ≤ chA * x + 5 / 2 * log x - 4

def Sandwich : Prop := ∀ x : ℝ, 0 ≤ x →
  Chebyshev.psi x - Chebyshev.psi (x / 6) ≤ chD x ∧ chD x ≤ Chebyshev.psi x

def CHUpper : Prop := ∀ x : ℝ, 1 ≤ x → Chebyshev.psi x ≤ 1.1056 * x + 0.7 * (log x) ^ 2

def PCLarge (x₀ : ℝ) : Prop := ∀ y : ℝ, x₀ ≤ y → ((pr y).card : ℝ) < 1.26 * y / log y

def PCSmall (x₀ : ℝ) : Prop := ∀ y : ℝ, 1 < y → y < x₀ → ((pr y).card : ℝ) < 1.26 * y / log y

theorem primeCountBound_of (x₀ : ℝ) (hL : PCLarge x₀) (hS : PCSmall x₀) : PI.PrimeCountBound := by
  intro y hy
  by_cases h : x₀ ≤ y
  · exact hL y h
  · exact hS y hy (lt_of_not_ge h)

end PI.PC
