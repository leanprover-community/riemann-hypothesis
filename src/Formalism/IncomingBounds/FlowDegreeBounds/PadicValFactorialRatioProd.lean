module

public import Formalism.IncomingBounds.IncomingBound
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section
open scoped BigOperators

namespace Formalism.IncomingBounds

private theorem one_add_mul_le_one_add_pow (x : ℝ) (hx : 0 ≤ x) (k : ℕ) : 1 + k * x ≤ (1 + x) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    push_cast
    nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℝ) ≤ k) (mul_nonneg hx hx),
      mul_le_mul_of_nonneg_right ih (by linarith : (0:ℝ) ≤ 1 + x)]

theorem padicValuationGain : ValGain := by
  intro l hl
  have hlR : (2 : ℝ) ≤ l := by exact_mod_cast hl.two_le
  have hB : 0 < (l : ℝ) - 1 := by linarith
  refine ⟨?_, ?_⟩
  · intro n hn
    have hle : l ^ padicValNat l n ≤ n := Nat.le_of_dvd (by omega) (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _))
    have hleR : (l : ℝ) ^ padicValNat l n ≤ n := by exact_mod_cast hle
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) - 1) hB.le (padicValNat l n)
    rw [show (1 : ℝ) + ((l : ℝ) - 1) = l by ring] at hb
    rw [le_sub_iff_add_le, div_add' _ _ _ hB.ne', div_le_div_iff_of_pos_right hB]
    linarith
  · intro e
    unfold rho
    have hA : 0 < (l : ℝ) ^ 2 - 1 := by nlinarith
    have hq : ((l : ℝ) ^ 2 - 1) * (1 / ((l : ℝ) ^ 2 - 1)) = 1 := mul_one_div_cancel hA.ne'
    have hb := one_add_mul_le_one_add_pow ((l : ℝ) ^ 2 - 1) hA.le e
    rw [show (1 : ℝ) + ((l : ℝ) ^ 2 - 1) = (l : ℝ) ^ 2 by ring] at hb
    have hm := mul_le_mul_of_nonneg_right hb (one_div_pos.2 hA).le
    have he : (1 + (e : ℝ) * ((l : ℝ) ^ 2 - 1)) * (1 / ((l : ℝ) ^ 2 - 1)) =
        1 / ((l : ℝ) ^ 2 - 1) + e := by
      linear_combination (e : ℝ) * hq
    linarith

end Formalism.IncomingBounds
