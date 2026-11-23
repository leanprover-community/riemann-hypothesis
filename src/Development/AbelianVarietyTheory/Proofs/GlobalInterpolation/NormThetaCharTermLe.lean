module

public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.JacobiThetaHalfCharacteristic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke

namespace GlobalTheory.Glob.EvenThetaBound

open Complex

theorem norm_thetaChar_term_le (a b : Fin 2) (τ : ℂ) (hτ : 1 / 2 ≤ τ.im) (n : ℤ) :
    ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ ≤
      Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) := by
  set r : ℝ := (n : ℝ) + ((a : ℕ) : ℝ) / 2 with hr
  have hw : (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
      2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2) =
      ((Real.pi * r ^ 2 : ℝ) : ℂ) * τ * I + ((Real.pi * r * ((b : ℕ) : ℝ) : ℝ) : ℂ) * I := by
    rw [hr]; push_cast; ring
  rw [hw, Complex.norm_exp, Real.exp_le_exp, add_re, mul_I_re, mul_I_re, im_ofReal_mul,
    ofReal_im, neg_zero, add_zero]
  have ha : ((a : ℕ) : ℝ) = 0 ∨ ((a : ℕ) : ℝ) = 1 := by
    rcases a with ⟨_ | _ | k, hk⟩
    · left; simp
    · right; simp
    · omega
  have hpi := Real.pi_pos
  have hr2 : (n : ℝ) ^ 2 / 2 - |(n : ℝ)| ≤ r ^ 2 / 2 := by
    have h1 : -|(n : ℝ)| ≤ (n : ℝ) := neg_abs_le _
    have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
    rcases ha with h | h <;> rw [hr, h] <;> nlinarith
  have hr3 : r ^ 2 / 2 ≤ r ^ 2 * τ.im := by nlinarith [sq_nonneg r]
  have h0 : 0 ≤ |(n : ℝ)| := abs_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (hr2.trans hr3) hpi.le]

theorem evenThetaConst_bounded :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (a b : Fin 2) (τ : ℂ), 1 / 2 ≤ τ.im → ‖JacobiThetaHalfCharacteristic.thetaChar a b 0 τ‖ ≤ C₀ := by
  have hs := summable_pow_mul_jacobiTheta₂_term_bound 1 (by norm_num : (0 : ℝ) < 1 / 2) 0
  simp only [pow_zero, one_mul] at hs
  have hs' : Summable (fun n : ℤ => Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|))) := by
    simpa [Int.cast_abs] using hs
  refine ⟨1 + ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)), ?_, ?_⟩
  · have : 0 ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
      tsum_nonneg fun n => (Real.exp_pos _).le
    linarith
  · intro a b τ hτ
    rw [JacobiThetaHalfCharacteristic.thetaChar_eq_tsum]
    have hb : Summable (fun n : ℤ => ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
        2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖) :=
      hs'.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_thetaChar_term_le a b τ hτ)
    calc _ ≤ ∑' n : ℤ, ‖cexp ((Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) ^ 2 * τ +
          2 * (Real.pi : ℂ) * I * ((n : ℂ) + ((a : ℕ) : ℂ) / 2) * (0 + ((b : ℕ) : ℂ) / 2))‖ :=
          norm_tsum_le_tsum_norm hb
      _ ≤ ∑' n : ℤ, Real.exp (-Real.pi * (1 / 2 * (n : ℝ) ^ 2 - 2 * 1 * |(n : ℝ)|)) :=
          hb.tsum_le_tsum (norm_thetaChar_term_le a b τ hτ) hs'
      _ ≤ _ := le_add_of_nonneg_left zero_le_one

end GlobalTheory.Glob.EvenThetaBound
