module

public import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsSympl
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

namespace PSymplDetSchur

noncomputable def clearCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if j = 0 then -A i 0 / A 0 0 else 0

theorem det_clearCol {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (clearCol A).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ ?_]
  · simp [clearCol]
  · intro i j hij
    have hij' : i < j := OrderDual.toDual_lt_toDual.mp hij
    have hne : i ≠ j := ne_of_lt hij'
    have hj : j ≠ 0 := by
      rintro rfl
      simp at hij'
    simp [clearCol, hne, hj]

theorem clearCol_mul_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (j : Fin (n + 1)) :
    (clearCol A * A) 0 j = A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, (Fin.succ_ne_zero _).symm, Fin.succ_ne_zero]

theorem clearCol_mul_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (i : Fin n)
    (j : Fin (n + 1)) :
    (clearCol A * A) i.succ j = A i.succ j - A i.succ 0 / A 0 0 * A 0 j := by
  rw [Matrix.mul_apply, Fin.sum_univ_succ]
  simp [clearCol, Fin.succ_ne_zero, Fin.succ_inj]
  ring

end PSymplDetSchur


open PSymplDetSchur in
theorem SymplDetSchur.proof : SymplDetSchur.Statement := by
  intro n A ha
  have hdet : A.det = (clearCol A * A).det := by
    rw [Matrix.det_mul, det_clearCol, one_mul]
  rw [hdet, Matrix.det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin n, (clearCol A * A) i.succ 0 = 0 := by
    intro i
    rw [clearCol_mul_succ]
    field_simp
    ring
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, clearCol_mul_zero]
  congr 1
  congr 1
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.of_apply, clearCol_mul_succ]
  ring

end GroundTheory.Heights₂.Heights
