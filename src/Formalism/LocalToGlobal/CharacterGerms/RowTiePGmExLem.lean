module

public import Formalism.LocalToGlobal.CharacterGerms.Interface
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.GmExArith

open Formalism.L2.FormalSeriesBounds NumberField

variable {C : Type} [Field C] {V : VF C}

theorem mm_add {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a + b) :=
  lt_of_lt_of_le (lt_min ha hb) (V.v.map_add a b)

theorem mm_zero : V.MM (0 : C) := by
  unfold VF.MM; rw [V.v.map_zero]; exact WithTop.top_pos

theorem mm_neg {a : C} (h : V.MM a) : V.MM (-a) := by
  unfold VF.MM at *; rwa [V.v.map_neg]

theorem mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by
  rw [sub_eq_add_neg]; exact mm_add ha (mm_neg hb)

theorem mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by
  unfold VF.MM at *
  rw [V.v.map_mul]
  have hb' : (0 : WithTop ℝ) ≤ V.v b := by simpa [VF.Ge] using hb
  exact add_pos_of_pos_of_nonneg ha hb'

theorem mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by
  rw [mul_comm]; exact mm_mul_int hb ha

theorem mm_l : V.MM (V.l : C) := by
  unfold VF.MM; rw [V.v_l]; exact zero_lt_one

theorem mm_sum {ι : Type*} {s : Finset ι} {f : ι → C} (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact mm_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact mm_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem ge_natCast' (n : ℕ) : V.Ge 0 (n : C) := by
  induction n with
  | zero => rw [Nat.cast_zero]; exact VF.Ge.zero 0
  | succ n ih => rw [Nat.cast_succ]; exact ih.add VF.Ge.one

theorem ge_intCast' (m : ℤ) : V.Ge 0 (m : C) := by
  cases m with
  | ofNat n => rw [Int.ofNat_eq_natCast, Int.cast_natCast]; exact ge_natCast' n
  | negSucc n => rw [Int.cast_negSucc]; exact (ge_natCast' (n + 1)).neg

theorem geom_int {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (n : ℕ) :
    V.Ge 0 (∑ i ∈ Finset.range n, A ^ i * B ^ (n - 1 - i)) :=
  VF.Ge.sum fun i _ => (hA.pow i).mul_int (hB.pow _)

theorem mm_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) (h : V.MM (A - B)) (n : ℕ) :
    V.MM (A ^ n - B ^ n) := by
  rw [← geom_sum₂_mul]; exact mm_int_mul (geom_int hA hB n) h

end Formalism.L2.FormalSeriesBounds.GmExArith
