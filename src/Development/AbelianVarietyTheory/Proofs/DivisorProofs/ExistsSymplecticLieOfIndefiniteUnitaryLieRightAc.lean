module

public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
public import Formalism.LocalRingCardinality.DataTheta
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap

@[expose] public section

open scoped TensorProduct Matrix
open MeasureTheory Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.RealWeil

namespace GlobalTheory.RealLift.SpLie

open Matrix

def sgnD {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnD := by
  ext a b
  rcases a with a | a <;> rcases b with b | b <;>
    simp [Jm, Formalism.UG.Jpq, sgnD, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

theorem lineSign_eq_mul {p q r s : ℕ} (a : Ix p q) (b : Ix r s) : lineSign a b = sgnD a * sgnD b := by
  rcases a with a | a <;> rcases b with b | b <;> simp [lineSign, sgnD]

theorem upq_entry {r s : ℕ} {Y : Mat r s} (hY : Y ∈ upq r s) (b k : Ix r s) :
    star (Y k b) * sgnD k + sgnD b * Y b k = 0 := by
  have h : (Yᴴ * Jm r s + Jm r s * Y) b k = 0 := by
    rw [show Yᴴ * Jm r s + Jm r s * Y = 0 from hY]; rfl
  rw [Jm_eq_diagonal] at h
  simpa [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply] using h

theorem sympl_eq_dot {l : Type} [Fintype l] [DecidableEq l] (u v : l ⊕ l → ℝ) :
    sympl u v = -(u ⬝ᵥ (Matrix.J l ℝ *ᵥ v)) := by
  simp [sympl, pPart, qPart, PiLp.inner_apply, Matrix.J, mulVec, dotProduct, Fintype.sum_sum_type,
    Matrix.one_apply, ite_mul, Finset.sum_ite_eq]
  simp only [mul_comm (v _)]
  ring

theorem sum_zero {P Q R S : ℕ} (c c' : Matrix (Ix P Q) (Ix R S) ℂ) (Y : Mat R S) (hY : Y ∈ upq R S) :
    (∑ a, ∑ b, lineSign a b * (c * Yᵀ) a b * star (c' a b)) +
      ∑ a, ∑ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) = 0 := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun a _ => ?_
  have e1 : ∀ b, lineSign a b * (c * Yᵀ) a b * star (c' a b) =
      ∑ k, sgnD a * c a k * star (c' a b) * (sgnD b * Y b k) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply]; ring
  have e2 : ∀ b, lineSign a b * c a b * star ((c' * Yᵀ) a b) =
      ∑ k, sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k)) := by
    intro b
    rw [lineSign_eq_mul, Matrix.mul_apply, star_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [transpose_apply, star_mul']; ring
  simp only [e1, e2]
  rw [Finset.sum_comm (f := fun b k => sgnD a * c a b * star (c' a k) * (sgnD b * star (Y b k))),
    ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun b _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun k _ => ?_
  linear_combination (sgnD a * c a k * star (c' a b)) * upq_entry hY b k

theorem mem_sp_of_sympl {l : Type} [Fintype l] [DecidableEq l] (Z : Matrix (l ⊕ l) (l ⊕ l) ℝ)
    (h : ∀ u v, sympl (Z *ᵥ u) v + sympl u (Z *ᵥ v) = 0) : Z ∈ LieAlgebra.Symplectic.sp l ℝ := by
  rw [LieAlgebra.Symplectic.sp, mem_skewAdjointMatricesLieSubalgebra, mem_skewAdjointMatricesSubmodule]
  show Zᵀ * Matrix.J l ℝ = Matrix.J l ℝ * -Z
  ext a b
  have h1 := h (Pi.single a 1) (Pi.single b 1)
  rw [sympl_eq_dot, sympl_eq_dot] at h1
  simp [mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply] at h1 ⊢
  linarith

end GlobalTheory.RealLift.SpLie
