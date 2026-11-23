module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.PerpVecPerpSt
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

@[expose] public section

namespace PI.UnitaryGroupMassFormula.FormPartialDerivatives

open ReciprocityTheory.ChartRestriction.G.TB

theorem perpVec_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (c : Fin p) :
    h (perpVec h e e' g) (e c) = 0 := by
  have hentry : ∀ a', hMat h e e' a' c = h (e' a') (e c) := fun _ => rfl
  have key : ∀ a, ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) =
      if a = c then (hMat h e e').det else 0 := by
    intro a
    have hk := congrFun (congrFun (Matrix.adjugate_mul (hMat h e e')) a) c
    rw [Matrix.mul_apply] at hk
    simp only [hentry] at hk
    rw [hk, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp

  simp only [perpVec, map_sub, map_smul, map_sum, Pi.sub_apply, Pi.smul_apply, Finset.sum_apply,
  smul_eq_mul]
  have hsum : ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c) =
      (hMat h e e').det * h g (e c) := by
    calc ∑ a, ∑ a', (hMat h e e').adjugate a a' * h g (e a) * h (e' a') (e c)
        = ∑ a, h g (e a) * ∑ a', (hMat h e e').adjugate a a' * h (e' a') (e c) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun a' _ => ?_
          ring
      _ = (hMat h e e').det * h g (e c) := by
          simp only [key, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
          ring
  rw [hsum]
  ring

theorem perpVec_of_perp (R : Type) [CommRing R] (V : Type) [AddCommGroup V] [Module R V] (p : ℕ)
    (h : V →ₗ[R] (V → R)) (e e' : Fin p → V) (g : V) (hg : ∀ a, h g (e a) = 0) :
    perpVec h e e' g = (hMat h e e').det • g := by
  simp [perpVec, hg]

end PI.UnitaryGroupMassFormula.FormPartialDerivatives
