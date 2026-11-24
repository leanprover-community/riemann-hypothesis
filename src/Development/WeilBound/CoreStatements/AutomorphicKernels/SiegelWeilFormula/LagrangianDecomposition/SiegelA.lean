module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.BlockIndexInrLast
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open Matrix

namespace PositivityTheory.SiegelWeilFormula.Ald

theorem block_index_inl_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inl (em0 h a)) = Sum.inl (Sum.inl a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inl a)

theorem block_index_inr_embedded {N n : ℕ} (h : n + 1 = N) (a : Fin n) : eB h (Sum.inr (em0 h a)) = Sum.inl (Sum.inr a) :=
  PositivityTheory.SiegelWeilFormula.Ald.eB_map h (Sum.inr a)

theorem blk_fromRows {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (P : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R)
    (A : Matrix (Fin n) (Fin n) R)
    (hP : P * Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) =
      Matrix.fromRows (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin n) R) * A) :
    blk h P 1 * Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) =
      Matrix.fromRows (1 : Matrix (Fin N) (Fin N) R) (0 : Matrix (Fin N) (Fin N) R) *
        (Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h) := by
  have hA : ∀ i j, P (Sum.inl i) (Sum.inl j) = A i j := by
    intro i j
    have := congrFun (congrFun hP (Sum.inl i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have hB : ∀ i j, P (Sum.inr i) (Sum.inl j) = 0 := by
    intro i j
    have := congrFun (congrFun hP (Sum.inr i)) j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply] using this
  have key : ∀ c : Fin N, c = PositivityTheory.SiegelWeilFormula.Ald.i0 h ∨ ∃ j, c = PositivityTheory.SiegelWeilFormula.Ald.em0 h j := by
    intro c
    by_cases hc : c = PositivityTheory.SiegelWeilFormula.Ald.i0 h
    · exact Or.inl hc
    · obtain ⟨j, rfl⟩ := (PositivityTheory.SiegelWeilFormula.Ald.ne_last_iff_mem_range h c).1 hc
      exact Or.inr ⟨j, rfl⟩
  ext u c
  rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sum_type]
  rcases u with a | a <;> rcases key a with rfl | ⟨i, rfl⟩ <;> rcases key c with rfl | ⟨j, rfl⟩ <;>
    simp [Matrix.one_apply, PositivityTheory.SiegelWeilFormula.Ald.blk_apply, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_embedded,
      PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_embedded, PositivityTheory.SiegelWeilFormula.Ald.block_index_inl_last, PositivityTheory.SiegelWeilFormula.Ald.block_index_inr_last,
      PositivityTheory.SiegelWeilFormula.Ald.index_embedded_equiv, PositivityTheory.SiegelWeilFormula.Ald.index_last_equiv, hA, hB]

theorem det_blkA {R : Type*} [CommRing R] {N n : ℕ} (h : n + 1 = N) (A : Matrix (Fin n) (Fin n) R) :
    ((Matrix.fromBlocks A 0 0 1 : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R).submatrix (eI h) (eI h)).det = A.det := by
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, mul_one]

end PositivityTheory.SiegelWeilFormula.Ald

end
