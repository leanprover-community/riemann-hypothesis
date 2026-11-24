module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

namespace GlobalTheory

theorem multiset_mem_list_sum' {α : Type*} (l : List (Multiset α)) (x : α) :
    x ∈ l.sum ↔ ∃ m ∈ l, x ∈ m := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.sum_cons, Multiset.mem_add, ih]

theorem multiset_le_list_sum' {α : Type*} (l : List (Multiset α)) (m : Multiset α) (h : m ∈ l) :
    m ≤ l.sum := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.1 h with rfl | h
    · exact Multiset.le_add_right _ _
    · exact (ih h).trans (Multiset.le_add_left _ _)

theorem norm_natCast_cpow_ofReal {q : ℕ} (hq : 0 < q) (s : ℝ) :
    ‖(q : ℂ) ^ ((s : ℝ) : ℂ)‖ = (q : ℝ) ^ s := by
  rw [Complex.norm_natCast_cpow_of_pos hq]
  simp

theorem rpow_exponent_inj_of_one_lt {b : ℝ} (hb : 1 < b) {x y : ℝ} (h : b ^ x = b ^ y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact absurd h (ne_of_lt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))
  · exact hxy
  · exact absurd h (ne_of_gt (Real.rpow_lt_rpow_of_exponent_lt hb hxy))

end GlobalTheory
