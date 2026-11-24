module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.BlockLevi

variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]

def diagPart (f : ι → ℕ) (A : Matrix ι ι k) : Matrix ι ι k :=
  Matrix.of fun r s => if f r = f s then A r s else 0

theorem mul_diagPart_apply (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) {r s : ι} (h : f s ≤ f r) :
    (A * diagPart f B) r s = (A * B) r s := by
  simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
  refine Finset.sum_congr rfl fun t _ => ?_
  split_ifs with ht
  · rfl
  · rcases lt_or_gt_of_ne ht with h1 | h1
    · rw [hA (lt_of_lt_of_le h1 h)]; simp
    · rw [hB h1]

theorem diagPart_mul_diagPart (f : ι → ℕ) {A B : Matrix ι ι k} (hA : A.BlockTriangular f)
    (hB : B.BlockTriangular f) (hAB : A * B = 1) :
    diagPart f A * diagPart f B = 1 := by
  ext r s
  by_cases h : f r = f s
  · rw [← hAB, ← mul_diagPart_apply f hA hB h.ge]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_pos (h.trans ht.symm)]
    · simp [ht]
  · have hrs : r ≠ s := fun e => h (e ▸ rfl)
    rw [Matrix.one_apply_ne hrs]
    simp only [Matrix.mul_apply, diagPart, Matrix.of_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : f t = f s
    · rw [if_neg (fun e => h (e.trans ht))]; simp
    · simp [ht]

theorem blockTriangular_inv (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by
  letI : Invertible b.val := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb

theorem exists_unip_mul_levi : ∀ (k : Type) [Field k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (b : GL (n ⊕ Fin c) k), b.val.BlockTriangular (lev p) → ∃ u ∈ N k n c p, ∃ m : GL (n ⊕ Fin c) k, (∀ r s, lev p r ≠ lev p s → m.val r s = 0) ∧ (∀ r s, lev p r = lev p s → m.val r s = b.val r s) ∧ b = u * m := by
  intro k _ n _ _ c p b hb
  have hi := blockTriangular_inv (lev p) b hb
  let m : GL (n ⊕ Fin c) k := ⟨diagPart (lev p) b.val, diagPart (lev p) (b⁻¹).val,
    diagPart_mul_diagPart _ hb hi b.mul_inv, diagPart_mul_diagPart _ hi hb b.inv_mul⟩
  refine ⟨b * m⁻¹, Subgroup.subset_closure ?_, m, ?_, ?_, by simp⟩
  · intro r s h
    have : (b * m⁻¹).val = b.val * diagPart (lev p) (b⁻¹).val := rfl
    rw [this, mul_diagPart_apply _ hb hi h, b.mul_inv]
  · intro r s h
    simp [m, diagPart, h]
  · intro r s h
    simp [m, diagPart, h]

end GlobalTheory.RootEx.BlockLevi
