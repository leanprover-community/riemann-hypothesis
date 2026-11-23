module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Complex.Basic
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
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace GlobalTheory.SumCompSurjective

open Finset

theorem sum_comp_surjective {G Q : Type} [AddCommGroup G] [AddCommGroup Q] [Fintype G] [Fintype Q]
    (π : G →+ Q) (hπ : Function.Surjective (⇑π : G → Q)) (g : Q → ℂ) :
    ∃ n : ℕ, 0 < n ∧ ∑ y : G, g (π y) = (n : ℂ) * ∑ q : Q, g q := by
  classical
  have hfib : ∀ q : Q, (univ.filter fun y : G => π y = q).card
      = (univ.filter fun y : G => π y = 0).card := by
    intro q
    obtain ⟨a, rfl⟩ := hπ q
    refine Finset.card_bij (fun y _ => y - a) ?_ ?_ ?_
    · intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      rw [map_sub, hy, sub_self]
    · intro y _ z _ h
      exact sub_left_injective h
    · intro z hz
      simp only [mem_filter, mem_univ, true_and] at hz
      refine ⟨z + a, ?_, by simp⟩
      simp only [mem_filter, mem_univ, true_and]
      rw [map_add (f := _), hz, zero_add]
  refine ⟨(univ.filter fun y : G => π y = 0).card, ?_, ?_⟩
  · exact Finset.card_pos.2 ⟨0, by simp⟩
  · rw [← Finset.sum_fiberwise (s := univ) (g := fun y : G => π y) (f := fun y => g (π y)),
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => g q) (fun y hy => by rw [(mem_filter.1 hy).2]),
      Finset.sum_const, hfib q, nsmul_eq_mul]

end GlobalTheory.SumCompSurjective
