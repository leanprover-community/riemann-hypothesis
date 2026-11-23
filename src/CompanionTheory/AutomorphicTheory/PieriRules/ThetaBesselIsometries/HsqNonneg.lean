module

public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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

namespace GlobalTheory
end GlobalTheory

open GlobalTheory

namespace Gp91
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SupTau

theorem hsq_nonneg (r : ℕ) (T b : ℝ) : 0 ≤ Hsq r T b := by
  show 0 ≤ max 1 T * b ^ (20 * (r + 1))
  have h1 : 0 ≤ max 1 T := le_trans zero_le_one (le_max_left _ _)
  have h2 : 0 ≤ b ^ (20 * (r + 1)) := by
    rw [pow_mul]
    exact pow_nonneg (by positivity) _
  exact mul_nonneg h1 h2

theorem arith (a a' d e A A' : ℝ) (n : ℕ) (ha : 0 ≤ a) (ha' : 0 ≤ a') (hd : 0 < d) (he : 0 < e) (hA : 0 ≤ A)
    (hA' : 0 ≤ A') (h : a ^ 2 * d / e ≤ A ^ n) (h' : a' ^ 2 * d / e ≤ A' ^ n) :
    a' * a * d / e ≤ Real.sqrt (A * A') ^ n := by
  have he0 : e ≠ 0 := ne_of_gt he
  have hsq : (Real.sqrt (A * A') ^ n) ^ 2 = A ^ n * A' ^ n := by
    rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt (mul_nonneg hA hA'), mul_pow]
  have hprod : (a' * a * d / e) ^ 2 = (a ^ 2 * d / e) * (a' ^ 2 * d / e) := by
    field_simp <;> ring
  have key : (a' * a * d / e) ^ 2 ≤ (Real.sqrt (A * A') ^ n) ^ 2 := by
    rw [hprod, hsq]
    exact mul_le_mul h h' (by positivity) (pow_nonneg hA n)
  have hl : 0 ≤ a' * a * d / e := by positivity
  have hr : 0 ≤ Real.sqrt (A * A') ^ n := pow_nonneg (Real.sqrt_nonneg _) n
  calc a' * a * d / e = Real.sqrt ((a' * a * d / e) ^ 2) := (Real.sqrt_sq hl).symm
    _ ≤ Real.sqrt ((Real.sqrt (A * A') ^ n) ^ 2) := Real.sqrt_le_sqrt key
    _ = Real.sqrt (A * A') ^ n := Real.sqrt_sq hr

end GlobalTheory.SupTau
