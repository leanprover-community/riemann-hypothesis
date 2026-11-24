module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
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
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action

@[expose] public section

namespace GlobalTheory.ComplexValueBound

open Finset

theorem main : ∀ {ι κ M : Type} [inst : AddCommGroup M] [inst_1 : Module ℂ M] (T : κ → M →ₗ[ℂ] M) (l : ι → κ → ℂ), (∀ (i j : ι), i ≠ j → ∃ (k : κ), l i k ≠ l j k) → ∀ (s : Finset ι) (u : ι → M), (∀ (i : ι) (k : κ), (T k : M → M) (u i) = l i k • u i) → ∑ i ∈ s, u i = (0 : M) → ∀ i ∈ s, u i = (0 : M) := by
  intro ι κ M _ _ T l hl s
  classical
  induction s using Finset.induction_on with
  | empty => intro u _ _ i hi; simp at hi
  | insert a s ha ih =>
    intro u hu hsum
    rw [Finset.sum_insert ha] at hsum
    have hsa : ∑ i ∈ s, u i = -u a := by
      rw [← sub_eq_zero, sub_neg_eq_add, add_comm]; exact hsum
    have hs : ∀ j ∈ s, u j = 0 := by
      intro j hj
      have hne : a ≠ j := fun h => ha (h ▸ hj)
      obtain ⟨k, hk⟩ := hl a j hne
      have hvu : ∀ (i : ι) (k' : κ), (T k' : M → M) ((l i k - l a k) • u i)
          = l i k' • ((l i k - l a k) • u i) := by
        intro i k'
        rw [LinearMap.map_smul, hu, smul_comm]
      have hvsum : ∑ i ∈ s, (l i k - l a k) • u i = 0 := by
        have h1 : ∑ i ∈ s, (l i k - l a k) • u i
            = T k (∑ i ∈ s, u i) - l a k • ∑ i ∈ s, u i := by

          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [hu, sub_smul]
        rw [h1, hsa, map_neg, hu, smul_neg, sub_neg_eq_add, neg_add_cancel]
      have h := ih (fun i => (l i k - l a k) • u i) hvu hvsum j hj
      exact (smul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr (Ne.symm hk))
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · have h0 : ∑ i ∈ s, u i = 0 := Finset.sum_eq_zero hs
      rw [h0, add_zero] at hsum; exact hsum
    · exact hs i hi

end GlobalTheory.ComplexValueBound
