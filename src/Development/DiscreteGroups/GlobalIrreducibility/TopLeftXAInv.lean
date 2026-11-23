module

public import Development.DiscreteGroups.GlobalIrreducibility.RankOneTopLeftZero
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
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.deprecated false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.Whittaker Matrix

namespace DiscreteGroups.sglob.LConvGenM

variable {k : Type} [Field k] {n : ℕ}

section RankOne

variable (j : ℕ) (hj : j < n) (hj1 : 1 ≤ j) (ξ : Fin n → k) (hξ : ξ (i0 j hj hj1) ≠ 0)
include hξ

theorem coef_eq : (ξ (i0 j hj hj1))⁻¹ * (ξ (i0 j hj hj1) - 1) = 1 - (ξ (i0 j hj hj1))⁻¹ := by
  field_simp

def xA : GL (Fin n) k :=
  ⟨1 + R1 j hj hj1 ξ, 1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ,
    by rw [add_mul, one_mul, mul_sub, mul_one, Matrix.mul_smul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel,
    by rw [sub_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, rankOne_mul_self, smul_smul, rowVector_at_index, coef_eq j hj hj1 ξ hξ,
      sub_smul, one_smul]; abel⟩

theorem topLeft_xA : TopLeft j ((xA j hj hj1 ξ hξ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 + R1 j hj hj1 ξ) i l = _
  rw [Matrix.add_apply, rankOne_top_left_zero j hj hj1 ξ i l h, add_zero]

theorem topLeft_xA_inv : TopLeft j (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) := by
  intro i l h
  show (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i l = _
  rw [Matrix.sub_apply, Matrix.smul_apply, rankOne_top_left_zero j hj hj1 ξ i l h, smul_zero, sub_zero]

theorem rowMul_xA_inv (a : Fin n) (ha : a.val < j) :
    rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) a =
      if a = i0 j hj hj1 then 1 else 0 := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  have key : ∀ i : Fin n, (if i.val < j then ξ i *
      (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i a else 0) =
      (if i = a then ξ a else 0) - (if i = i0 j hj hj1 then vrow j hj hj1 ξ a else 0) := by
    intro i
    show (if i.val < j then ξ i * (1 - (ξ (i0 j hj hj1))⁻¹ • R1 j hj hj1 ξ) i a else 0) = _
    by_cases hi : i.val < j
    · rw [if_pos hi]
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, R1, of_apply, one_apply]
      by_cases hia : i = a <;> by_cases hii : i = i0 j hj hj1
      · subst hia; subst hii; simp; field_simp
      · subst hia; simp [hii]
      · subst hii; simp [hia]; field_simp
      · simp [hia, hii]
    · rw [if_neg hi, if_neg (fun e => hi (by rw [e]; exact ha)), if_neg (fun e => hi (by rw [e]; exact hi0))]
      ring
  rw [rowMul, Finset.sum_congr rfl fun i _ => key i, Finset.sum_sub_distrib, Finset.sum_ite_eq',
    Finset.sum_ite_eq', if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  simp only [vrow, if_pos ha]
  ring

theorem dotj_xA_inv (c : Fin n → k) :
    dotj j (rowMul j ξ (((xA j hj hj1 ξ hξ)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) c = c (i0 j hj hj1) := by
  have hi0 : (i0 j hj hj1).val < j := by simp [i0]; omega
  rw [dotj, Finset.sum_congr rfl fun a _ => (?_ : _ = if a = i0 j hj hj1 then c a else 0), Finset.sum_ite_eq',
    if_pos (Finset.mem_univ _)]
  by_cases ha : a.val < j
  · rw [if_pos ha, rowMul_xA_inv j hj hj1 ξ hξ a ha]
    split_ifs <;> simp
  · rw [if_neg ha, if_neg (fun e => ha (by rw [e]; exact hi0))]

end RankOne

end DiscreteGroups.sglob.LConvGenM
