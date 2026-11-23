module

public import Mathlib.Algebra.Algebra.Defs
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

open Polynomial

namespace GlobalTheory.CompanionTheory.KillSum

theorem prod_map_add_eq {R α : Type*} [CommRing R] (P : Multiset α) (f : α → R) (w : R) :
    ∃ q, (P.map fun a => f a + w).prod = (P.map f).prod + w * q := by
  induction P using Multiset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | cons a s ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨(s.map f).prod + f a * q + w * q, ?_⟩
    simp only [Multiset.map_cons, Multiset.prod_cons, hq]
    ring

theorem add_killed {R : Type*} [CommRing R] [Algebra ℂ R] (x y : R) (P Q : Multiset ℂ)
    (hP : (P.map fun c => x - algebraMap ℂ R c).prod = 0)
    (hQ : (Q.map fun c => y - algebraMap ℂ R c).prod = 0) :
    ((Q.bind fun b => P.map fun a => a + b).map fun c => (x + y) - algebraMap ℂ R c).prod = 0 := by
  have key : ∀ b : ℂ, ∃ q, (P.map fun a => (x + y) - algebraMap ℂ R (a + b)).prod
      = (y - algebraMap ℂ R b) * q := by
    intro b
    obtain ⟨q, hq⟩ := prod_map_add_eq P (fun c => x - algebraMap ℂ R c) (y - algebraMap ℂ R b)
    refine ⟨q, ?_⟩
    rw [hP, zero_add] at hq
    rw [← hq]
    congr 1
    apply Multiset.map_congr rfl
    intro a _
    simp only [map_add (f := _)]
    ring
  choose q hq using key
  rw [Multiset.map_bind, Multiset.prod_bind]
  simp only [Multiset.map_map, Function.comp_def]
  simp only [hq]
  rw [Multiset.prod_map_mul, hQ, zero_mul]

theorem sum_killed {ι : Type} (T : Finset ι) (l : ι → Multiset ℂ) :
    ∃ l' : Multiset ℂ, Multiset.card l' = ∏ τ ∈ T, Multiset.card (l τ) ∧
  ∀ (R : Type) [CommRing R] [Algebra ℂ R] (h : ι → R), (∀ τ ∈ T, ((l τ).map fun c => h τ - algebraMap ℂ R c).prod = 0) →
    (l'.map fun c => ∑ τ ∈ T, h τ - algebraMap ℂ R c).prod = 0 := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨{0}, by simp, fun R _ _ h _ => by simp⟩
  | insert τ s hτ ih =>
    obtain ⟨l0, hc, hk⟩ := ih
    refine ⟨l0.bind fun b => (l τ).map fun a => a + b, ?_, ?_⟩
    · rw [Finset.prod_insert hτ, ← hc]
      simp [Multiset.card_bind, mul_comm]
    · intro R _ _ h hh
      rw [Finset.sum_insert hτ]
      exact add_killed _ _ _ _ (hh τ (Finset.mem_insert_self _ _))
        (hk R h fun t ht => hh t (Finset.mem_insert_of_mem ht))

end GlobalTheory.CompanionTheory.KillSum
