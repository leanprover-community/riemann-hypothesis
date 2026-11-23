module

public import Formalism.RealPlaceAnalysis.StatementA
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Finset

noncomputable section

namespace Formalism.REAL

theorem iteratedGrowthBound_holds : GrowthIter := by
  intro V _ _ X U B C hB hC hX j k
  induction k generalizing j with
  | zero => intro w _; simp
  | succ k ih =>
    intro w hw
    obtain ⟨hXw, hnorm⟩ := hX j w hw
    have h1 := ih (j + 1) (X w) hXw
    have e : B + ((j + 1 : ℕ) : ℝ) + (k : ℝ) = B + (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    rw [e] at h1
    rw [show ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
    have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hBj : 0 ≤ B + (j : ℝ) := by linarith
    have hL : 0 ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hBjL : B + (j : ℝ) ≤ B + (j : ℝ) + ((k : ℝ) + 1) := by linarith
    have hCk : 0 ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k := by positivity
    calc ‖(X ^ (k + 1)) w‖ = ‖(X ^ k) (X w)‖ := by rw [pow_succ, Module.End.mul_apply]
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * ‖X w‖ := h1
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k * (C * (B + j) * ‖w‖) := by gcongr
      _ ≤ C ^ k * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ k *
            (C * (B + (j : ℝ) + ((k : ℝ) + 1)) * ‖w‖) := by gcongr
      _ = C ^ (k + 1) * (B + (j : ℝ) + ((k : ℝ) + 1)) ^ (k + 1) * ‖w‖ := by ring

theorem taylorSummable_holds : TaylorRadius := by
  intro C m t hC hm ht h
  have hCt : 0 ≤ C * t := mul_nonneg hC ht
  have hr0 : 0 ≤ C * t * Real.exp 1 := by positivity
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    ((summable_geometric_of_lt_one hr0 h).mul_left (Real.exp m))
  have hx : 0 ≤ m + (k : ℝ) := by positivity
  have h1 := Real.pow_div_factorial_le_exp (m + k) hx k
  have h2 : Real.exp (m + k) = Real.exp m * Real.exp 1 ^ k := by
    rw [Real.exp_add, ← Real.exp_nat_mul, mul_one]
  have hCtk : 0 ≤ (C * t) ^ k := pow_nonneg hCt k
  calc (C * t) ^ k * (m + k) ^ k / (k.factorial : ℝ)
      = (C * t) ^ k * ((m + k) ^ k / (k.factorial : ℝ)) := by ring
    _ ≤ (C * t) ^ k * Real.exp (m + k) := by gcongr
    _ = Real.exp m * (C * t * Real.exp 1) ^ k := by rw [h2]; ring

end Formalism.REAL
