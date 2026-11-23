module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
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
import Mathlib.RingTheory.PiTensorProduct
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem cas_mul_comm_of_block : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), IsGl F → ∀ a b, s a = s b → cas s F * F a b = F a b * cas s F := by
  intro ι M _ _ _ _ s F hF a b hab
  rw [← sub_eq_zero]
  have key : ∀ c d, F c d * F d c * F a b - F a b * (F c d * F d c) =
      ((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0)) := by
    intro c d
    have e : F c d * F d c * F a b - F a b * (F c d * F d c) =
        F c d * (F d c * F a b - F a b * F d c) + (F c d * F a b - F a b * F c d) * F d c := by noncomm_ring
    rw [e, hF d c a b, hF c d a b]
    simp only [mul_sub, sub_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  have h0 : cas s F * F a b - F a b * cas s F = ∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0 := by
    simp only [cas, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    by_cases h : s c = s d
    · simp only [h, if_true]; exact key c d
    · simp only [h, if_false, zero_mul, mul_zero, sub_self]
  have h1 : (∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc; simp [hc]
    · simp
  have h4 : (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0) =
      ∑ d, if s a = s d then F a d * F d b else 0 := by
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro c _ hc; simp [Ne.symm hc]
    · simp
  have h2 : (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single b]
    · simp [hab]
    · intro d _ hd; simp [Ne.symm hd]
    · simp
  have h3 : (∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) =
      ∑ c, if s c = s a then F c b * F a c else 0 := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_eq_single a]
    · simp
    · intro d _ hd; simp [hd]
    · simp
  rw [h0]
  have split : (∑ c, ∑ d, if s c = s d then
      (((if c = a then F c d * F d b else 0) - (if b = d then F c d * F a c else 0)) +
      ((if d = a then F c b * F d c else 0) - (if b = c then F a d * F d c else 0))) else 0) =
      ((∑ c, ∑ d, if s c = s d then (if c = a then F c d * F d b else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = d then F c d * F a c else 0) else 0)) +
      ((∑ c, ∑ d, if s c = s d then (if d = a then F c b * F d c else 0) else 0) -
        (∑ c, ∑ d, if s c = s d then (if b = c then F a d * F d c else 0) else 0)) := by
    simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> simp
  rw [split, h1, h2, h3, h4]
  abel

end GlobalTheory.HoweR
