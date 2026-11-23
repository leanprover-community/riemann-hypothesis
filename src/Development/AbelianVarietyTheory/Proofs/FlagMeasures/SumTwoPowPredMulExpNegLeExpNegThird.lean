module

public import Mathlib.Analysis.Complex.Exponential
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.SharpRestriction.CuspSpanNormBounds.Point

@[expose] public section

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem sum_two_pow_pred_mul_pow_le (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 4) (q : ℕ) :
    ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * r ^ J ≤ 2 * r * (1 - (1 / 2) ^ q) := by
  induction q with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Nat.add_sub_cancel]
    have h2 : (2 * r) ^ n ≤ (1 / 2 : ℝ) ^ n :=
      pow_le_pow_left₀ (by positivity) (by linarith) n
    have h3 : (2 : ℝ) ^ n * r ^ (n + 1) = r * (2 * r) ^ n := by rw [mul_pow]; ring
    have h4 : r * (2 * r) ^ n ≤ r * (1 / 2 : ℝ) ^ n := mul_le_mul_of_nonneg_left h2 h0
    have h5 : 2 * r * (1 - (1 / 2 : ℝ) ^ (n + 1))
        = 2 * r * (1 - (1 / 2) ^ n) + r * (1 / 2 : ℝ) ^ n := by ring
    rw [h3, h5]
    linarith

theorem sum_two_pow_pred_mul_exp_neg_le :
    ∀ (q : ℕ) (x : ℝ), 15 ≤ x → ∑ J ∈ Finset.Icc 1 q, (2 : ℝ) ^ (J - 1) * Real.exp (-(1 / 2 * J * x)) ≤ Real.exp (-(1 / 3 * x)) := by
  intro q x hx
  have hr : ∀ J : ℕ, Real.exp (-(1 / 2 * J * x)) = Real.exp (-(x / 2)) ^ J := by
    intro J
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  simp only [hr]
  have h0 : 0 < Real.exp (-(x / 2)) := Real.exp_pos _
  have h1 : Real.exp (-(x / 2)) ≤ 1 / 4 := by
    rw [Real.exp_neg, one_div]
    apply inv_anti₀ (by norm_num)
    have := Real.add_one_le_exp (x / 2)
    linarith
  refine (sum_two_pow_pred_mul_pow_le _ h0.le h1 q).trans ?_
  have h2 : Real.exp (-(1 / 3 * x)) = Real.exp (x / 6) * Real.exp (-(x / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h3 : (2 : ℝ) ≤ Real.exp (x / 6) := by
    have := Real.add_one_le_exp (x / 6)
    linarith
  have h4 : (0 : ℝ) ≤ (1 / 2) ^ q := by positivity
  rw [h2]
  nlinarith [mul_nonneg h0.le h4, mul_le_mul_of_nonneg_right h3 h0.le]

end GlobalTheory
