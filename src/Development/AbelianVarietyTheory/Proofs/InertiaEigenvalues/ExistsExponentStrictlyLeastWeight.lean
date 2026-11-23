module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.DFinsupp.WellFounded
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

@[expose] public section

open scoped BigOperators

namespace GlobalTheory


open scoped BigOperators in
theorem _root_.GlobalTheory.exists_exponent_strictly_least_weight :
    ∀ (ρ : ℕ) (S : Set (Fin ρ → ℕ)), S.Nonempty → ∃ m ∈ S, ∀ c : Fin ρ → ℕ,
      (∀ i, ∑ i' ∈ Finset.Iio i, m i' * c i' < c i) →
        ∀ a ∈ S, a ≠ m → ∑ i, m i * c i < ∑ i, a i * c i := by
  intro ρ S hS
  have hwf : WellFounded (Pi.Lex (fun i j : Fin ρ => j < i) (fun {_} (x y : ℕ) => x < y)) :=
    Pi.Lex.wellFounded _
  refine ⟨hwf.min S hS, hwf.min_mem S hS, ?_⟩
  set m := hwf.min S hS with hm
  intro c hc a ha hne
  have hnl := hwf.not_lt_min S ha
  have hd : (Finset.univ.filter fun i => a i ≠ m i).Nonempty := by
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hne
    exact ⟨i, by simp [hi]⟩
  set k := (Finset.univ.filter fun i => a i ≠ m i).max' hd with hkdef
  have hk : a k ≠ m k := (Finset.mem_filter.1 (Finset.max'_mem _ hd)).2
  have hgt : ∀ j, k < j → a j = m j := fun j hj => by
    by_contra h
    exact absurd (Finset.le_max' _ j (by simp [h])) (not_le.2 hj)
  have hlt : m k < a k := by
    rcases lt_or_gt_of_ne hk with h | h
    · exact absurd ⟨k, fun j hj => hgt j hj, h⟩ hnl
    · exact h
  have key : ∀ i, m i * c i + (if i = k then c k else 0) ≤
      a i * c i + (if i < k then m i * c i else 0) := by
    intro i
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne]
    · subst h
      simp only [if_true, lt_irrefl, if_false, add_zero]
      nlinarith
    · simp [h.ne', not_lt.2 h.le, hgt i h]
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => key i
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', ← Finset.sum_filter] at hsum
  simp only [Finset.mem_univ, if_true] at hsum
  have hI : Finset.univ.filter (fun i => i < k) = Finset.Iio k := by ext; simp
  rw [hI] at hsum
  have := hc k
  omega

end GlobalTheory
