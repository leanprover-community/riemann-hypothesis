module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic

@[expose] public section

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

theorem sum_coord_smul_coordVec {n : ℕ} (w : V n) : ∑ b, w b • coordVec b = w := by
  ext i
  simp [coordVec, Pi.single_apply]

theorem dOne_comp_holo {n : ℕ} {φ : V n → V n} {c : V n → ℂ} {v : V n}
    (hc : DifferentiableAt ℝ c (φ v)) (hφ : DifferentiableAt ℂ φ v) :
    dOne (fun w => c (φ w)) v = pull (fderiv ℂ φ v) (dOne c (φ v)) := by
  have key (a : Fin n) : del (fun w => c (φ w)) v (coordVec a) =
      ∑ b, fderiv ℂ φ v (coordVec a) b * del c (φ v) (coordVec b) := by
    rw [del_comp_holo hc hφ]
    conv_lhs => rw [← sum_coord_smul_coordVec (fderiv ℂ φ v (coordVec a))]

    simp [map_sum, map_smul, smul_eq_mul]

  simp only [dOne, map_sum, map_smul, (pull_dz _ _).1, Finset.smul_sum, smul_smul, key, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [mul_comm]

end GlobalTheory.CxForm.DelForm
