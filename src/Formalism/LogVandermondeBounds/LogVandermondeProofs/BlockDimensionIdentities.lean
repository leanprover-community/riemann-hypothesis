module

public import Formalism.LogVandermondeBounds.LogVandermondeVariationUnbounded
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace Formalism.LogVandermondeBounds.StandardLattice

open Finset

theorem eulerProductBounds : EulerProductBounds := by
  intro q hq n
  set x := q⁻¹ with hx
  have hx0 : 0 < x := inv_pos.mpr (by linarith)
  have hxq : x * q = 1 := inv_mul_cancel₀ (by linarith)
  have hx3 : x ≤ 1 / 3 := by nlinarith
  have hx1 : x ≤ 1 := by linarith
  have key : ∀ n : ℕ, 1 - 2 * x + x ^ (n + 1) ≤ (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) := by
    intro n
    induction n with
    | zero => simp; linarith
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc]
      set y := x ^ (n + 1) with hy
      have hy0 : 0 ≤ y := pow_nonneg hx0.le _
      have hyx : y ≤ x := pow_le_of_le_one hx0.le hx1 (by omega)
      have hc : 0 ≤ 1 - y := by have : y ≤ 1 := pow_le_one₀ hx0.le hx1; linarith
      have h1 := mul_le_mul_of_nonneg_right ih hc
      have h2 : y * y ≤ y * x := mul_le_mul_of_nonneg_left hyx hy0
      have e : x ^ (n + 1 + 1) = y * x := by rw [hy, pow_succ]
      rw [e]
      nlinarith
  have hfac : ∀ i ∈ range n, 0 ≤ 1 - x ^ (i + 1) ∧ 1 - x ^ (i + 1) ≤ 1 := by
    intro i _
    exact ⟨by have : x ^ (i + 1) ≤ 1 := pow_le_one₀ hx0.le hx1; linarith,
      by have : 0 ≤ x ^ (i + 1) := pow_nonneg hx0.le _; linarith⟩
  refine ⟨?_, Finset.prod_le_one₀ (fun i hi => (hfac i hi).1) (fun i hi => (hfac i hi).2)⟩
  by_contra hlt
  push_neg at hlt
  have h1 : (1 - x) * ∏ i ∈ range n, (1 - x ^ (i + 1)) < (1 - x) * (1 / 2) :=
    mul_lt_mul_of_pos_left hlt (by linarith)
  have := key n
  have := pow_pos hx0 (n + 1)
  linarith

end Formalism.LogVandermondeBounds.StandardLattice
