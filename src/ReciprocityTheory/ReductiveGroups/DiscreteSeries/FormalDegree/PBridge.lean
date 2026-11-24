module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.AdKMeasurePreserving
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.TraceMulSelfEqSumEigenvaluesSq

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS

open ReciprocityTheory.ChartRestriction.DS.S7

variable {n : ℕ}

theorem toMK_inv_eq_conjTranspose {ε : Fin n → Bool} (k : KG ε) : toMK k⁻¹ = (toMK k)ᴴ := by
  have h : toMK k⁻¹ = star (toMK k) :=
    Units.inv_eq_of_mul_eq_one_right (Unitary.mul_star_self_of_mem (show toMK k ∈ Kset ε from k.2).1)
  rw [h, Matrix.star_eq_conjTranspose]

theorem conj_pmat_eq_adK {ε : Fin n → Bool} (k : KG ε) (z : PCoord ε → ℂ) :
    toMK k⁻¹ * pmat z * toMK k = pmat (adK k⁻¹ z) := by
  rw [pmat_adK, toMK_inv_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

theorem rhoP_real_smul {ε : Fin n → Bool} (t : ℝ) (z : PCoord ε → ℂ) : rhoP ((t : ℂ) • z) = |t| * rhoP z := by
  have hS : ∑ ab, ‖((t : ℂ) • z) ab‖ ^ 2 = t ^ 2 * ∑ ab, ‖z ab‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ab _ => ?_
    simp [Pi.smul_apply, smul_eq_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  unfold rhoP
  rw [hs_pmat, hs_pmat, hS, show 2 * (t ^ 2 * ∑ ab, ‖z ab‖ ^ 2) = t ^ 2 * (2 * ∑ ab, ‖z ab‖ ^ 2) by ring,
    Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq_eq_abs]
  ring

end ReciprocityTheory.ChartRestriction.DS
