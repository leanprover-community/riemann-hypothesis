module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.ShcAdC
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPPos
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
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.DetPaHadApply

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PolarJacobianDeterminant

theorem prod_shc_sq_eq_Jac_pow {ε : Fin n → Bool} (z : PCoord ε → ℂ) :
    ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = Jac z ^ 4 := by
  set f : Fin n → Fin n → ℝ := fun i j => shc (pev z i - pev z j) with hf
  have hsym : ∀ i j, f i j = f j i := by
    intro i j; simp only [hf]; rw [← neg_sub, PolarJacobianDeterminant.shc_neg]
  have hpt : ∀ i j, f i j = (if i < j then f i j else 1) * (if j < i then f i j else 1) := by
    intro i j
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt_of_gt h]
    · subst h; simp [hf, shc]
    · simp [h, not_lt_of_gt h]
  have hswap : ∏ i, ∏ j, (if j < i then f i j else 1) = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => ?_
    rw [hsym]
  have hJ : Jac z = ∏ i, ∏ j, (if i < j then f i j else 1) := by
    simp only [Jac, Finset.prod_filter, hf]
  have hall : ∏ i, ∏ j, f i j = Jac z ^ 2 := by
    calc ∏ i, ∏ j, f i j
          = ∏ i, ∏ j, ((if i < j then f i j else 1) * (if j < i then f i j else 1)) :=
          Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => hpt i j
      _ = (∏ i, ∏ j, (if i < j then f i j else 1)) * ∏ i, ∏ j, (if j < i then f i j else 1) := by
          simp only [Finset.prod_mul_distrib]
      _ = Jac z ^ 2 := by rw [hswap, ← hJ, sq]
  have : ∏ i, ∏ j, shc (pev z i - pev z j) ^ 2 = (∏ i, ∏ j, f i j) ^ 2 := by
    simp only [hf, Finset.prod_pow]
  rw [this, hall, ← pow_mul]

theorem fderiv_shcAdC {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    fderiv ℝ (shcAdC y) 0 = LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y) := by
  have : shcAdC y = ⇑(LinearMap.toContinuousLinearMap (PolarJacobianDeterminant.shcAdCL y)) := by
    funext w; rfl
  rw [this]
  exact ContinuousLinearMap.fderiv _

end PolarJacobianDeterminant

theorem detP {ε : Fin n → Bool} (y : PCoord ε → ℂ) :
    LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) = Jac y := by
  have h4 := (detPb y).symm.trans ((detPa y).trans (PolarJacobianDeterminant.prod_shc_sq_eq_Jac_pow y))
  have hpos : 0 < LinearMap.det ((fderiv ℝ (shcAdC y) 0 : (PCoord ε → ℂ) →L[ℝ] (PCoord ε → ℂ)) :
      (PCoord ε → ℂ) →ₗ[ℝ] (PCoord ε → ℂ)) := by
    rw [PolarJacobianDeterminant.fderiv_shcAdC, LinearMap.coe_toContinuousLinearMap]
    exact PolarJacobianDeterminant.det_shcAdCL_pos y
  have hJ : 0 ≤ Jac y := Finset.prod_nonneg fun a _ => Finset.prod_nonneg fun b _ =>
    (PolarJacobianDeterminant.shc_pos _).le
  exact (pow_left_inj₀ hpos.le hJ (by norm_num)).mp h4

end ReciprocityTheory.ChartRestriction.DS
