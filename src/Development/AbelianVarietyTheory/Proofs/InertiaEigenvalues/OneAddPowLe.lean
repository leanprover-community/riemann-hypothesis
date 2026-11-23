module

public import Mathlib.Basic.Real.Basic
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

namespace GlobalTheory.OneAddPowBound

theorem one_add_pow_le : ∀ {t : ℝ}, (0 : ℝ) ≤ t → ∀ (k : ℕ),
    ((1 : ℝ) + t) ^ k ≤ (2 : ℝ) ^ k * ((1 : ℝ) + t ^ k) := by
  intro t ht k
  have htk : 0 ≤ t ^ k := pow_nonneg ht k
  have h2 : (0 : ℝ) ≤ 2 ^ k := pow_nonneg (by norm_num) k
  have h1 : (0 : ℝ) ≤ 1 + t := by linarith
  rcases le_total t 1 with h | h
  · have ha : (1 + t) ^ k ≤ (2 : ℝ) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    have hb : (2 : ℝ) ^ k * 1 ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith
  · have ha : (1 + t) ^ k ≤ (2 * t) ^ k := pow_le_pow_left₀ h1 (by linarith) k
    rw [mul_pow] at ha
    have hb : (2 : ℝ) ^ k * t ^ k ≤ 2 ^ k * (1 + t ^ k) :=
      mul_le_mul_of_nonneg_left (by linarith) h2
    linarith

end GlobalTheory.OneAddPowBound
