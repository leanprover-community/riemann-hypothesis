module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.UniNilp
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

@[expose] public section

open Matrix Finset Real

namespace GlobalTheory

private theorem trace_sub_one_pow_eq_zero_of_trace_pow_eq (K : Type) [Field K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) (k : ℕ) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    ((A - 1) ^ k).trace = 0 := by
  have hc : Commute A (-1 : Matrix (Fin n) (Fin n) K) := (Commute.one_right A).neg_right
  have hall : ∀ m ∈ Finset.range (k + 1), (A ^ m).trace = (n : K) := by
    intro m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    · exact h m hm0 (le_trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)) hkn)
  rw [sub_eq_add_neg, hc.add_pow, Matrix.trace_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      (A ^ m * (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) * (k.choose m : Matrix (Fin n) (Fin n) K)).trace
        = (n : K) * ((1 : K) ^ m * (-1 : K) ^ (k - m) * (k.choose m : K)) := by
    intro m hm
    have e1 : (-1 : Matrix (Fin n) (Fin n) K) ^ (k - m) = ((-1 : K) ^ (k - m)) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [← neg_one_smul K (1 : Matrix (Fin n) (Fin n) K), smul_pow, one_pow]
    have e2 : ((k.choose m : ℕ) : Matrix (Fin n) (Fin n) K) = (k.choose m : K) • (1 : Matrix (Fin n) (Fin n) K) := by
      rw [Nat.cast_smul_eq_nsmul, nsmul_one]
    rw [e1, e2, Matrix.mul_smul, mul_one, Matrix.mul_smul, mul_one, smul_smul,
      Matrix.trace_smul, hall m hm, smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← add_pow]
  simp [Nat.pos_iff_ne_zero.mp hk1]

theorem unipotent_of_trace_pow_eq_size (K : Type) [Field K] [CharZero K] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ j, 1 ≤ j → j ≤ n → (A ^ j).trace = n) :
    A.charpoly = (Polynomial.X - 1) ^ n ∧ (A - 1) ^ n = 0 := by
  have htr : ∀ k, 1 ≤ k → k ≤ n → ((A - 1) ^ k).trace = 0 :=
    fun k hk1 hkn => trace_sub_one_pow_eq_zero_of_trace_pow_eq K n A h k hk1 hkn
  have hB : IsNilpotent (A - 1) :=
    ReciprocityTheory.L2DbarEstimates.Y.isNilpotent_of_trace_pow n (A - 1) htr
  have hchar : (A - 1).charpoly = Polynomial.X ^ n := by
    have := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hB).eq_zero
    simpa [sub_eq_zero] using this
  refine ⟨?_, ?_⟩
  · have e : A - 1 - Matrix.scalar (Fin n) (-1 : K) = A := by
      rw [map_neg, map_one, sub_neg_eq_add, sub_add_cancel]
    have hs := Matrix.charpoly_sub_scalar (A - 1) (-1 : K)
    rw [e, hchar] at hs
    rw [hs, Polynomial.pow_comp, Polynomial.X_comp, map_neg, map_one, ← sub_eq_add_neg]
  · have := Matrix.aeval_self_charpoly (A - 1)
    rwa [hchar, map_pow, Polynomial.aeval_X] at this

end GlobalTheory
