module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DblCol
public import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.RealLift.Dbl

namespace GlobalTheory.RealLift.Dbl.ColBlocks

theorem mul_transpose_doubledSpaceFrame_toCols1 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₁ =
      M.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₁, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]

theorem mul_transpose_doubledSpaceFrame_toCols2 {α β : Type} [Fintype β] {R S : ℕ} (M : Matrix α (Ix (R + S) (S + R)) ℂ) (C : Matrix β (Ix R S) ℂ) :
    (M * (dblM C)ᵀ).toCols₂ =
      M.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ := by
  ext a i
  simp only [Matrix.toCols₂, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, id,
    dblM, Fintype.sum_sum_type, Fin.sum_univ_add, dblCol, finSumFinEquiv_symm_apply_castAdd,
    finSumFinEquiv_symm_apply_natAdd, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
    add_zero, zero_add]
  ring

theorem mul_submatrix_right {α γ δ ε : Type} [Fintype γ] (A : Matrix α γ ℂ) (c : Matrix γ δ ℂ) (e : ε → δ) :
    A * c.submatrix id e = (A * c).submatrix id e := rfl

theorem jm_right_L {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      X.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Jm R S := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

theorem jm_right_R {γ : Type} {R S : ℕ} (X : Matrix γ (Ix (R + S) (S + R)) ℂ) :
    (X * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(X.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Jm R S) := by
  ext a k
  rcases k with r | s <;>
  simp [Jm, Formalism.UG.Jpq, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks, Matrix.one_apply]

end GlobalTheory.RealLift.Dbl.ColBlocks

namespace GlobalTheory.RealLift.Dbl


open GlobalTheory.RealLift.Dbl.ColBlocks in
theorem dblM_colBlocks : ∀ (α β : Type) [Fintype β] (P Q R S : ℕ) (A : Matrix α (Ix P Q) ℂ) (C : Matrix β (Ix R S) ℂ)
    (c : Matrix (Ix P Q) (Ix (R + S) (S + R)) ℂ),
    (A * c * (dblM C)ᵀ).toCols₁ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) * Cᵀ ∧
    (A * c * (dblM C)ᵀ).toCols₂ =
        A * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) * Cᵀ ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) =
      Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inl (Fin.castAdd S r)) (fun s => Sum.inr (Fin.castAdd R s))) *
        Jm R S ∧
    (Jm P Q * c * Jm (R + S) (S + R)).submatrix id
        (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) =
      -(Jm P Q * c.submatrix id (Sum.elim (fun r => Sum.inr (Fin.natAdd S r)) (fun s => Sum.inl (Fin.natAdd R s))) *
        Jm R S) := by
  intro α β _ P Q R S A C c
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [mul_transpose_doubledSpaceFrame_toCols1, mul_submatrix_right]
  · rw [mul_transpose_doubledSpaceFrame_toCols2, mul_submatrix_right]
  · rw [jm_right_L, mul_submatrix_right]
  · rw [jm_right_R, mul_submatrix_right]

end GlobalTheory.RealLift.Dbl
