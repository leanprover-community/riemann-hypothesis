module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ImportsAlt
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.Per GlobalTheory.PSer
open scoped Formalism.Per

namespace GlobalTheory.PSer.PwLaws
variable {l : ℕ} [Fact l.Prime]
theorem pw_apply_eq (k : ℤ) (x : Fl l) :
    pw k x = ((frobeniusEquiv (Fl l) l : RingAut (Fl l)) ^ k : RingAut (Fl l)) x := rfl
theorem pw_zadd (a b : ℤ) (x : Fl l) : pw (a + b) x = pw a (pw b x) := by
  simp only [pw_apply_eq, zpow_add, RingAut.mul_apply]
theorem pw_one (x : Fl l) : pw 1 x = x ^ l := by
  rw [pw_apply_eq, zpow_one]
  show frobeniusEquiv (Fl l) l x = _
  rw [frobeniusEquiv_apply, frobenius_def]
theorem pw_nat (n : ℕ) (x : Fl l) : pw (n : ℤ) x = x ^ l ^ n := by
  induction n with
  | zero => simp [pw_apply_eq]
  | succ n ih =>
    have h : ((n + 1 : ℕ) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
    rw [h, pw_zadd, ih, pw_one, ← pow_mul, pow_succ]

theorem pw_zero_int (x : Fl l) : pw 0 x = x := by
  simp [pw_apply_eq]
theorem sh_pow' (x : Fl l) (m : ℕ) : sh (x ^ m) = sh x ^ m := by
  simp only [sh, map_pow, SubmonoidClass.coe_pow]
theorem norm_sh_pw_nat (n : ℕ) (x : Fl l) : ‖sh (pw (n : ℤ) x)‖ = ‖sh x‖ ^ (l ^ n) := by
  rw [pw_nat, sh_pow', norm_pow]
theorem norm_sh_pw (k : ℤ) (x : Fl l) : ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k) := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
  · rw [norm_sh_pw_nat, zpow_natCast, ← Real.rpow_natCast]
    push_cast
    rfl
  · set y := pw (-(n : ℤ)) x with hy
    have hx : x = pw (n : ℤ) y := by
      rw [hy, ← pw_zadd, add_neg_cancel, pw_zero_int]
    have hne : l ^ n ≠ 0 := pow_ne_zero _ (Fact.out : l.Prime).ne_zero
    have e : ((l : ℝ) ^ (-(n : ℤ))) = (((l ^ n : ℕ) : ℝ))⁻¹ := by
      rw [zpow_neg, zpow_natCast]
      push_cast
      rfl
    conv_rhs => rw [hx, norm_sh_pw_nat, e]
    exact (Real.pow_rpow_inv_natCast (norm_nonneg _) hne).symm

theorem pw_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (k : ℤ) (x y : Fl l), pw k (x + y) = pw k x + pw k y) ∧ (∀ (k : ℤ) (x y : Fl l), pw k (x * y) = pw k x * pw k y) ∧ (∀ k : ℤ, pw k (0 : Fl l) = 0) ∧ (∀ (a b : ℤ) (x : Fl l), pw (a + b) x = pw a (pw b x)) ∧ (∀ (n : ℕ) (x : Fl l), pw n x = x ^ l ^ n) ∧ (∀ (k : ℤ) (n : ℕ) (x : Fl l), pw k (x ^ n) = pw k x ^ n) ∧ (∀ (k : ℤ) (x : Fl l), ‖sh (pw k x)‖ = ‖sh x‖ ^ ((l : ℝ) ^ k)) := by
  intro l _
  refine ⟨fun k x y => ?_, fun k x y => ?_, fun k => ?_, pw_zadd, pw_nat, fun k n x => ?_, norm_sh_pw⟩
  · simp only [pw_apply_eq, map_add (f := _)]
  · simp only [pw_apply_eq, map_mul]
  · simp only [pw_apply_eq, map_zero]
  · simp only [pw_apply_eq, map_pow]

end GlobalTheory.PSer.PwLaws
