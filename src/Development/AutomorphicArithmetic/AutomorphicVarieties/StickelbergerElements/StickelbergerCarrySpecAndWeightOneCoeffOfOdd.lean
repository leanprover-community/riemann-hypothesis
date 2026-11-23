module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.StickelbergerElements.SamePrimesMulPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Rat
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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

@[expose] public section

open Finset UpperTheory.V.Bern UpperTheory.V.Stk

theorem UpperTheory.V.Stk.stickelbergerCarry_spec_and_weightOne_coeff_of_odd :
    ∀ (M a : ℕ) [NeZero M], a.Coprime M → ∀ b : ZMod M,
      (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b ∧ (Odd a → Eva M 1 a b = (Eone M a b : ℚ)) := by
  intro M a _ hcop b
  have hM : (M : ℤ) ∣ (a : ℤ) * ((yCl a b).val : ℤ) - (b.val : ℤ) := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, yCl, ← mul_assoc,
      ZMod.coe_mul_inv_eq_one a hcop, one_mul, sub_self]
  have h1 : (a : ℤ) * ((yCl a b).val : ℤ) = (b.val : ℤ) + (M : ℤ) * jv M a b := by
    rw [jv, Int.mul_ediv_cancel' hM]
    ring
  refine ⟨h1, fun hodd => ?_⟩
  have hMq : (M : ℚ) ≠ 0 := by exact_mod_cast NeZero.ne M
  have h1q : (a : ℚ) * ((yCl a b).val : ℚ) = (b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ) := by
    exact_mod_cast h1
  obtain ⟨t, ht⟩ := hodd
  have hE : (Eone M a b : ℚ) = (t : ℚ) - (jv M a b : ℚ) := by
    rw [Eone]
    have : (((a : ℤ) - 1) / 2) = t := by omega
    rw [this]
    push_cast
    rfl
  rw [hE, Eva, Ev, Ev, bcoef, bcoef, Polynomial.bernoulli_one]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Nat.cast_one, sub_self,
    zpow_zero, one_mul, div_one, pow_one]
  have ha : (a : ℚ) ≠ 0 := by
    rw [ht]
    push_cast
    positivity
  have hy : ((yCl a b).val : ℚ) = ((b.val : ℚ) + (M : ℚ) * (jv M a b : ℚ)) / (a : ℚ) := by
    field_simp
    linarith [h1q]
  rw [hy]
  have hta : (a : ℚ) = 2 * t + 1 := by exact_mod_cast ht
  field_simp
  rw [hta]
  ring
