module

public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree
public import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
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

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

theorem numeric_bound_two_a_le_b1 (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hH : H ≤ b + 2 * η + S)
    (hsm : 40 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η ≤ (b : ℝ) / 4) (a : ℝ)
    (ha : a ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    2 * a + η + 1 ≤ (b₁ : ℝ) := by
  have hl' : (11 : ℝ) ≤ l := by exact_mod_cast hl
  have hbR : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hηR : 20 * (η : ℝ) ≤ b := by exact_mod_cast hη
  have hSR : 20 * (S : ℝ) ≤ b := by exact_mod_cast hS
  have hb₁R : (b : ℝ) ≤ b₁ := by exact_mod_cast hb₁
  have hHR : (H : ℝ) ≤ b + 2 * η + S := by exact_mod_cast hH
  have hcW := cW_le l hl (b + η + S) η H (by omega) (by omega)
  have hlog0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
    Real.logb_nonneg (by linarith) (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
  have hSg : Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) + 1 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  have hfrac : (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 ≤ (H : ℝ) * (21 / 100) := by
    rw [div_le_iff₀ (by nlinarith)]
    have h3 : (2 * (l : ℝ) - 1) ≤ 21 / 100 * ((l : ℝ) - 1) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hl') (by linarith : (0 : ℝ) ≤ l - 1)]
    nlinarith [Nat.cast_nonneg (α := ℝ) H]
  have hη0 := Nat.cast_nonneg (α := ℝ) η
  have hS0 := Nat.cast_nonneg (α := ℝ) S
  linarith

theorem numeric_bound_exponent_eg (l : ℕ) (hl : 11 ≤ l) (b wm S η b₁ H : ℕ) (hb : 1 ≤ b) (hη : 20 * η ≤ b) (hS : 20 * S ≤ b)
    (hwm : 20 * wm ≤ b) (hb₁ : b ≤ b₁) (hb₁' : b₁ ≤ b + η) (hH : H ≤ b + 2 * η + S) (A : ℕ)
    (ha : (A : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1) :
    (EG l A S η b₁ : ℝ) ≤ 8 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg l (b + η + S) wm S η := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have hl0 : (0 : ℝ) < l - 1 := by linarith
  have hcW : (0 : ℝ) ≤ (cW l H : ℝ) := Nat.cast_nonneg _
  have hHl : (0 : ℝ) ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 := by
    apply div_nonneg _ (sq_nonneg _)
    exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
  have ha' : max (A : ℝ) 1 ≤ (H : ℝ) * (2 * l - 1) / ((l : ℝ) - 1) ^ 2 + cW l H + 1 :=
    max_le ha (by linarith)
  have h5 := div_add_logb_le_eight_mul_errorScale l hl b wm S η b₁ H hb hη hS hwm hb₁ hb₁' hH (max (A : ℝ) 1) (le_max_right _ _) ha'
  have hmono : ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) ≤
      (3 * max (A : ℝ) 1 + S + 2 * η - 2) / ((l : ℝ) - 1) := by
    apply div_le_div_of_nonneg_right _ hl0.le
    linarith [le_max_left (A : ℝ) 1]
  have hSg : 0 ≤ Sg l (b + η + S) wm S η := by
    unfold Sg
    have h0 : 0 ≤ Real.logb l (2 * ((b + η + S : ℕ) : ℝ)) :=
      Real.logb_nonneg hl1 (by
        push_cast
        have : (1 : ℝ) ≤ b := by exact_mod_cast hb
        linarith [Nat.cast_nonneg (α := ℝ) η, Nat.cast_nonneg (α := ℝ) S])
    have h1 : 0 ≤ ((b + η + S : ℕ) : ℝ) / (l : ℝ) ^ 2 := by positivity
    have h2 : 0 ≤ ((wm : ℝ) + S + η) / l := by positivity
    linarith
  unfold EG
  by_cases hY : 0 ≤ ((3 * (A : ℝ) + S + 2 * η : ℝ) - 2) / ((l : ℝ) - 1) + Real.logb l ((b₁ : ℝ) + η - 1)
  · exact (Nat.floor_le hY).trans (by linarith)
  · rw [Nat.floor_of_nonpos (not_le.1 hY).le, Nat.cast_zero]
    linarith

end Formalism.MainNotions.N.FrobeniusPowerSeries
