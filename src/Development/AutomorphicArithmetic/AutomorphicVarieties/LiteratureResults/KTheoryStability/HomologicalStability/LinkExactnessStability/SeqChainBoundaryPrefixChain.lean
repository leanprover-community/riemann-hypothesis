module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SubClosed
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open GlobalTheory.SeqCx Matrix

namespace GlobalTheory.SeqCx

private theorem bd_single_eq_sum_neg_one_pow_eraseIdx (V : Type) (l : List V) :
    bd V (Finsupp.single l 1) =
      ∑ i ∈ Finset.range l.length, (-1 : ℤ) ^ i • Finsupp.single (l.eraseIdx i) 1 := by
  simp [bd, Finsupp.linearCombination_single]

theorem bd_single_append (V : Type) (τ w : List V) :
    bd V (Finsupp.single (τ ++ w) 1) =
      Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1)) +
      (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V (Finsupp.single w 1)) := by
  simp only [bd_single_eq_sum_neg_one_pow_eraseIdx, Finsupp.mapDomain_finsetSum, Finset.smul_sum]
  rw [List.length_append, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single, List.eraseIdx_append_of_lt_length hi]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single,
      List.eraseIdx_append_of_length_le (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      pow_add, mul_smul]

theorem bd_mapDomain_prepend : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  intro V τ c
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [Finsupp.mapDomain_add, map_add (f := _), hf, hg, map_add (f := _), Finsupp.mapDomain_add, smul_add,
      Finsupp.sum_add_index' (by intro; simp) (by intros; simp [add_smul])]
    abel
  | single w a =>
    rw [Finsupp.mapDomain_single, Finsupp.sum_single_index (by simp)]
    have h1 : Finsupp.single (τ ++ w) a = a • Finsupp.single (τ ++ w) (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have h2 : Finsupp.single w a = a • Finsupp.single w (1 : ℤ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h1, h2, map_smul, map_smul, bd_single_append, Finsupp.mapDomain_smul, smul_add, smul_comm a]

end GlobalTheory.SeqCx

section
open GlobalTheory.SeqCx Matrix
theorem _root_.GlobalTheory.T.seqChain_boundary_prefix_chain : ∀ (V : Type) (τ : List V) (c : List V →₀ ℤ), bd V (Finsupp.mapDomain (fun w => τ ++ w) c) = (c.sum fun w a => a • Finsupp.mapDomain (fun σ => σ ++ w) (bd V (Finsupp.single τ 1))) + (-1 : ℤ) ^ τ.length • Finsupp.mapDomain (fun w => τ ++ w) (bd V c) := by
  first
  | exact @GlobalTheory.SeqCx.bd_mapDomain_prepend
  | exact @GlobalTheory.SeqCx.bd_single_append
end
