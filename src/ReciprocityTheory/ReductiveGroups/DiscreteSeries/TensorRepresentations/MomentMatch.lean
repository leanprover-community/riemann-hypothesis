module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.Polynomial.Eval.Degree

@[expose] public section

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS

theorem moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp

variable {n : ℕ}

end ReciprocityTheory.ChartRestriction.DS
