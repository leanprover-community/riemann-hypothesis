module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam.AddCharZMod

theorem ch_eq (N : ℕ) [NeZero N] (j : ZMod N) : ch N j = ZMod.stdAddChar j := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  rfl

theorem main : ∀ (N : ℕ) [NeZero N], (∀ n : ℤ, ch N (n : ZMod N) = Complex.exp (2 * Real.pi * Complex.I * n / N)) ∧ (∀ i j, ch N (i + j) = ch N i * ch N j) ∧ ch N 0 = 1 ∧ (∀ j, ch N j = 1 ↔ j = 0) ∧ (∀ (m : ℕ) j, ch N ((m : ZMod N) * j) = ch N j ^ m) ∧ (∀ j, ch N (-j) = (ch N j)⁻¹) ∧ (∀ j, ‖ch N j‖ = 1) ∧ (∀ j, IsIntegral ℤ (ch N j)) := by
  intro N _
  have hpow : ∀ (m : ℕ) (j : ZMod N), ch N ((m : ZMod N) * j) = ch N j ^ m := by
    intro m j
    rw [ch_eq, ch_eq, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul]
  have hadd : ∀ i j, ch N (i + j) = ch N i * ch N j := by
    intro i j
    rw [ch_eq, ch_eq, ch_eq]
    exact AddChar.map_add_eq_mul _ i j
  have hzero : ch N 0 = 1 := by
    rw [ch_eq]
    exact AddChar.map_zero_eq_one _
  refine ⟨fun n => ?_, hadd, hzero, fun j => ?_, hpow, fun j => ?_, fun j => ?_, fun j => ?_⟩
  · rw [ch_eq]
    exact ZMod.stdAddChar_coe n
  · rw [ch_eq, ← (ZMod.stdAddChar (N := N)).map_zero_eq_one, ZMod.injective_stdAddChar.eq_iff]
  · have h : ch N (-j) * ch N j = 1 := by
      rw [← hadd, neg_add_cancel, hzero]
    exact eq_inv_of_mul_eq_one_left h
  · rw [ch_eq, ZMod.stdAddChar_apply]
    exact Circle.norm_coe _
  · have h : ch N j ^ N = 1 := by
      rw [← hpow, ZMod.natCast_self, zero_mul, hzero]
    refine IsIntegral.of_pow (Nat.pos_of_neZero N) ?_
    rw [h]
    exact isIntegral_one

end GlobalTheory.WpFam.AddCharZMod
