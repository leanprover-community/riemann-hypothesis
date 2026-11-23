module

public import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt
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
import Mathlib.Tactic.Basify
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
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm

@[expose] public section

open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem liftL_deg_reg : ∀ (q l : ℕ) (L : List (ℕ × ℕ)), 2 ≤ q → 0 < l →
    (∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2) →
    deg (liftL q l L) = deg L ∧ ∀ p ∈ liftL q l L, 0 < p.1 ∧ Reg (q ^ l) p.1 p.2 := by
  intro q l L hq hl hL
  induction L with
  | nil => simp [liftL, deg]
  | cons p L ih =>
    have hL' : ∀ p ∈ L, 0 < p.1 ∧ l ∣ p.1 ∧ Reg q p.1 p.2 := fun p' hp' => hL p' (List.mem_cons_of_mem _ hp')
    obtain ⟨ihd, ihm⟩ := ih hL'
    obtain ⟨hp0, hpd, hpr⟩ := hL p List.mem_cons_self
    obtain ⟨c, hc⟩ := hpd
    have hc0 : 0 < c := by
      rcases Nat.eq_zero_or_pos c with h | h
      · subst h; simp at hc; omega
      · exact h
    have hdiv : p.1 / l = c := by rw [hc]; exact Nat.mul_div_cancel_left c hl
    have hcons : liftL q l (p :: L) = (List.range l).map (fun i => (p.1 / l, p.2 * q ^ i)) ++ liftL q l L := by
      simp [liftL, List.flatMap_cons]
    refine ⟨?_, ?_⟩
    · rw [hcons]
      simp only [deg, List.map_append, List.sum_append, List.map_map] at ihd ⊢
      rw [ihd]
      simp [Function.comp_def, List.sum_replicate, hdiv, hc, Nat.mul_div_cancel_left c hl]
    · intro p' hp'
      rw [hcons, List.mem_append] at hp'
      rcases hp' with hp' | hp'
      · obtain ⟨i, -, rfl⟩ := List.mem_map.1 hp'
        refine ⟨by simpa [hdiv] using hc0, ?_⟩
        simp only [hdiv]
        rw [hc] at hpr
        exact (GlobalTheory.Shin.reg_step_of_dvd q l c p.2 hq hl hc0 hpr).1 i
      · exact ihm p' hp'

end GlobalTheory.Shin
