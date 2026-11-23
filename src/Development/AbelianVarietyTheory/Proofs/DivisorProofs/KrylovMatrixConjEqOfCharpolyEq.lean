module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h

  simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
