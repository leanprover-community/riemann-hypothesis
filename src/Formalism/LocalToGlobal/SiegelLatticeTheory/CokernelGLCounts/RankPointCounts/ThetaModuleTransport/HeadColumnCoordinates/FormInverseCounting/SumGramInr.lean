module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.ThetaC
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

noncomputable section

open Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.LocCnt0LAlg

variable {E : Type} [CommRing E] (cj : E →+* E) {r : ℕ}

theorem sum_gram_inl (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (c : Ix r → E)
    (j : Fin (r + 1)) :
    ∑ i, c i * gramC cj Z T T' i (Sum.inl j) =
      (∑ b, Z j b * c (Sum.inr b)) - (if j = Fin.last r then T * c (Sum.inl (Fin.last r)) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [gramC, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁, Matrix.of_apply,
    Matrix.transpose_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [and_true, if_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ]
    rw [mul_comm (c _) (-T), neg_mul, Finset.sum_congr rfl (fun b _ => mul_comm (c (Sum.inr b)) _)]
    ring
  · simp only [hj, and_false, if_false, mul_zero, Finset.sum_const_zero, zero_add, sub_zero]
    exact Finset.sum_congr rfl (fun b _ => mul_comm _ _)

theorem sum_gram_inr (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : E) (c : Ix r → E)
    (j : Fin (r + 1)) :
    ∑ i, c i * gramC cj Z T T' i (Sum.inr j) =
      (∑ a, cj (Z a j) * c (Sum.inl a)) - (if j = Fin.last r then T' * c (Sum.inr (Fin.last r)) else 0) := by
  rw [Fintype.sum_sum_type]
  simp only [gramC, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.of_apply]
  by_cases hj : j = Fin.last r
  · subst hj
    simp only [and_true, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [mul_comm (c _) (-T'), neg_mul, Finset.sum_congr rfl (fun a _ => mul_comm (c (Sum.inl a)) _)]
    ring
  · simp only [hj, and_false, if_false, mul_zero, Finset.sum_const_zero, add_zero, sub_zero]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)

end Formalism.L2.SG.LocalCountModules.LocCnt0LAlg
