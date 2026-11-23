module

public import ReciprocityTheory.DualLattices.TensorSpan
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Nilpotent
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Valuation.Integers

@[expose] public section

noncomputable section

open Finset Matrix

namespace ReciprocityTheory.PGsh.Up.U3

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [hp : Fact p.Prime] {C : Type} [Field C] {v : Valuation C NNReal}
  {R : Type} [CommRing R] [Algebra R C]

structure IsTeich (v : Valuation C NNReal) (ω : ZMod p → C) : Prop where
  pow : ∀ a, ω a ^ p = ω a
  cong : ∀ a, v (ω a - (a.val : C)) < 1
  zero : ω 0 = 0
  one : ω 1 = 1
  mul : ∀ a b, ω (a * b) = ω a * ω b
  sep : ∀ a b, a ≠ b → v (ω a - ω b) = 1

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem int (a : ZMod p) : v (ω a) ≤ 1 := by
  by_cases ha : a = 0
  · rw [ha, hω.zero, map_zero]
    exact zero_le
  · have h := hω.sep a 0 ha
    rw [hω.zero, sub_zero] at h
    exact h.le

theorem v_eq_one {a : ZMod p} (ha : a ≠ 0) : v (ω a) = 1 := by
  have h := hω.sep a 0 ha
  rwa [hω.zero, sub_zero] at h

theorem ne_zero {a : ZMod p} (ha : a ≠ 0) : ω a ≠ 0 := by
  intro h
  have h1 := hω.v_eq_one ha
  rw [h, map_zero] at h1
  exact zero_ne_one h1

theorem pow_pred {a : ZMod p} (ha : a ≠ 0) : ω a ^ (p - 1) = 1 := by
  have hne := hω.ne_zero ha
  have h1 : ω a ^ (p - 1) * ω a = 1 * ω a := by
    rw [← pow_succ, Nat.sub_add_cancel hp.out.one_lt.le, one_mul]
    exact hω.pow a
  exact mul_right_cancel₀ hne h1

end IsTeich

def wt (ω : ZMod p → C) (a : ZMod p) : C := ω a ^ (2 * p - 3)

def sS (ω : ZMod p → C) : C := ∑ b, wt ω b

def u0 (ω : ZMod p → C) (a : ZMod p) : C := wt ω a - if a = 0 then sS ω else 0

def lam (ω : ZMod p → C) (f : ZMod p → C) : C := ∑ a, u0 ω a * f a

section wt

namespace IsTeich

variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

theorem wt_zero : wt ω 0 = 0 := by
  unfold wt
  rw [hω.zero]
  exact zero_pow (by have := hp.out.two_le; omega)

theorem wt_mul_self {a : ZMod p} (ha : a ≠ 0) : wt ω a * ω a = 1 := by
  unfold wt
  rw [← pow_succ]
  have e : 2 * p - 3 + 1 = (p - 1) * 2 := by
    have := hp.out.two_le
    omega
  rw [e, pow_mul, hω.pow_pred ha, one_pow]

theorem wt_int (a : ZMod p) : v (wt ω a) ≤ 1 := by
  unfold wt
  rw [map_pow]
  exact pow_le_one₀ (zero_le) (hω.int a)

private theorem lam_eq_sum_wt_mul_sub (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  simp [lam, u0, sS, sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_mul]

theorem lam_eq (f : ZMod p → C) : lam ω f = ∑ a, wt ω a * (f a - f 0) := by
  exact lam_eq_sum_wt_mul_sub hω f

theorem lam_omega : lam ω ω = (p : C) - 1 := by
  rw [lam_eq_sum_wt_mul_sub hω, hω.zero]
  simp only [sub_zero]
  have h1 : ∀ a, wt ω a * ω a = 1 - if a = 0 then 1 else 0 := fun a => by
    split_ifs with ha
    · rw [ha, hω.wt_zero, zero_mul, sub_self]
    · rw [hω.wt_mul_self ha, sub_zero]
  simp only [h1, Finset.sum_sub_distrib]
  simp

end IsTeich

end wt

section hopf

variable (hv : v.Integers R)
include hv

omit hv in
theorem pow_mem' (AA : HopfOrder (C := C) R (ZMod p)) {f : ZMod p → C} (hf : f ∈ AA.carrier)
    (n : ℕ) : f ^ n ∈ AA.carrier := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact AA.one_mem
  | succ n ih =>
    rw [pow_succ]
    exact AA.mul_mem _ _ ih hf


variable {ω : ZMod p → C} (hω : IsTeich v ω)
include hω

end hopf

end ReciprocityTheory.PGsh.Up.U3
