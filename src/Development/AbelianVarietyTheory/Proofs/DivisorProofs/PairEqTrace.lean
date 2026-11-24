module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix

namespace GlobalTheory.PairingTraceExpansion

variable {K : Type} [Field K] {n d : ℕ}

theorem pair_eq_trace (X Y : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM X Y = trace (Xᵀ * Y) := by
  simp only [GlobalTheory.FlipMatch.pairM, trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem pair_expand (P M : Matrix (Fin n) (Fin d) K) :
    trace (Pᵀ * M) = ∑ i : Fin n, ∑ j : Fin d, P i j * M i j := by
  simp only [trace, diag, Matrix.mul_apply, transpose_apply]
  exact Finset.sum_comm

theorem main (A : Matrix (Fin n) (Fin n) K) (B : Matrix (Fin d) (Fin d) K)
    (b : GL (Fin n) K) (c : GL (Fin d) K) (P Q : Matrix (Fin n) (Fin d) K) :
    GlobalTheory.FlipMatch.pairM ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * Matrix.transpose (↑c⁻¹ : Matrix (Fin d) (Fin d) K))
      (-(Matrix.transpose (↑b : Matrix (Fin n) (Fin n) K) * A * Q * Matrix.transpose B * (↑c : Matrix (Fin d) (Fin d) K))) =
      -∑ i : Fin n, ∑ j : Fin d, ∑ k : Fin n, ∑ l : Fin d, P i j * A i k * B j l * Q k l := by
  have hb : (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ * (↑b : Matrix (Fin n) (Fin n) K)ᵀ = 1 := by
    rw [← transpose_mul, Units.mul_inv, transpose_one]
  have hc : (↑c : Matrix (Fin d) (Fin d) K) * (↑c⁻¹ : Matrix (Fin d) (Fin d) K) = 1 := Units.mul_inv c

  have ht : ((↑b⁻¹ : Matrix (Fin n) (Fin n) K) * P * (↑c⁻¹ : Matrix (Fin d) (Fin d) K)ᵀ)ᵀ *
      -((↑b : Matrix (Fin n) (Fin n) K)ᵀ * A * Q * Bᵀ * (↑c : Matrix (Fin d) (Fin d) K)) =
      -((↑c⁻¹ : Matrix (Fin d) (Fin d) K) * (Pᵀ * (A * Q * Bᵀ)) * (↑c : Matrix (Fin d) (Fin d) K)) := by
    simp only [transpose_mul, transpose_transpose, Matrix.mul_neg, neg_inj, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (↑b⁻¹ : Matrix (Fin n) (Fin n) K)ᵀ, hb, Matrix.one_mul]
  rw [pair_eq_trace, ht, trace_neg, trace_mul_comm, ← Matrix.mul_assoc, hc, Matrix.one_mul, pair_expand]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
  simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by ring

end GlobalTheory.PairingTraceExpansion
