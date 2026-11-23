module

public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Hadamard
public import Mathlib.Analysis.Normed.Ring.Basic

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.T0

open Matrix

theorem hadamard_gram {R : Type*} [Fintype R] [DecidableEq R] {n : ℕ} (hR : Fintype.card R = n)
    (M : R → Fin n → ℂ) (ν : R → ℝ) (s : Fin n → ℝ) (hν : ∀ r, 0 < ν r)
    (hM : ∀ r k, ‖M r k‖ * ν r ≤ s k) :
    ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2 ≤
      (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
  classical

  let e : R ≃ Fin n := Fintype.equivFinOfCardEq hR
  let A : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => M (e.symm i) k
  let N : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i k => (ν (e.symm i) : ℂ) * M (e.symm i) k
  have hG : (Matrix.of fun k l : Fin n => ∑ r, M r k * M r l) = Aᵀ * A := by
    ext k l
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, A]
    exact (Equiv.sum_comp e.symm (fun r => M r k * M r l)).symm
  have hNd : N = Matrix.diagonal (fun i => (ν (e.symm i) : ℂ)) * A := by
    ext i k
    simp [N, A, Matrix.diagonal_mul]
  have hprod : ∏ i, ν (e.symm i) = ∏ r, ν r := Equiv.prod_comp e.symm ν
  have hνpos : 0 ≤ ∏ r, ν r := Finset.prod_nonneg fun r _ => (hν r).le
  have hdetN : ‖N.det‖ = (∏ r, ν r) * ‖A.det‖ := by
    rw [hNd, Matrix.det_mul, Matrix.det_diagonal, norm_mul, norm_prod, ← hprod]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hν _)]
  have hleft : ‖(Matrix.of fun k l : Fin n => ∑ r, M r k * M r l).det‖ * ∏ r, ν r ^ 2
      = ‖N.det‖ ^ 2 := by
    rw [hG, Matrix.det_mul, Matrix.det_transpose, norm_mul, hdetN, Finset.prod_pow]
    ring
  rw [hleft]

  have hH : ‖N.det‖ ≤ ∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2) := by
    have := hadamard_det_le Nᵀ
    simpa [Matrix.det_transpose, Matrix.transpose_apply] using this
  have hcol : ∀ k, ∑ i, ‖N i k‖ ^ 2 ≤ (n : ℝ) * s k ^ 2 := by
    intro k
    have : ∀ i, ‖N i k‖ ^ 2 ≤ s k ^ 2 := by
      intro i
      have h1 : ‖N i k‖ = ‖M (e.symm i) k‖ * ν (e.symm i) := by
        simp only [N, Matrix.of_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (hν _)]
        ring
      rw [h1]
      exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (hν _).le) (hM _ _) 2
    calc ∑ i, ‖N i k‖ ^ 2 ≤ ∑ _i : Fin n, s k ^ 2 := Finset.sum_le_sum fun i _ => this i
      _ = (n : ℝ) * s k ^ 2 := by simp
  calc ‖N.det‖ ^ 2 ≤ (∏ k, Real.sqrt (∑ i, ‖N i k‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hH 2
    _ = ∏ k, ∑ i, ‖N i k‖ ^ 2 := by
        rw [← Finset.prod_pow]
        exact Finset.prod_congr rfl fun k _ =>
          Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity)
    _ ≤ ∏ k, ((n : ℝ) * s k ^ 2) :=
        Finset.prod_le_prod₀ (fun k _ => Finset.sum_nonneg fun i _ => by positivity)
          fun k _ => hcol k
    _ = (n : ℝ) ^ n * ∏ k, s k ^ 2 := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end ReciprocityTheory.ChartRestriction.G.T0
