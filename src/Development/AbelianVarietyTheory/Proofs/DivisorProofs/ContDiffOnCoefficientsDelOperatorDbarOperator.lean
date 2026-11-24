module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
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
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false

namespace GlobalTheory.CxForm.SmoothCoef

theorem contDiffOn_del_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => del f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [del_apply]
  exact ((h.clm_apply contDiffOn_const).sub ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_dbar_dir {n : ℕ} {s : Set (V n)} {f : V n → ℂ} (hs : IsOpen s) (hf : ContDiffOn ℝ ∞ f s) (e : V n) :
    ContDiffOn ℝ ∞ (fun v => dbar f v e) s := by
  have h : ContDiffOn ℝ ∞ (fun v => fderiv ℝ f v) s := hf.fderiv_of_isOpen hs (by simp)
  simp only [dbar_apply]
  exact ((h.clm_apply contDiffOn_const).add ((h.clm_apply contDiffOn_const).const_smul _)).const_smul _

theorem contDiffOn_coef : ∀ (n : ℕ) (s : Set (V n)) (F : V n → Alt n), IsOpen s →
    (∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (F v) S) s) →
    ∀ S, ContDiffOn ℝ ∞ (fun v => (bas n).repr (delAt F v) S) s ∧
      ContDiffOn ℝ ∞ (fun v => (bas n).repr (dbarAt F v) S) s := by
  intro n s F hs hF U
  constructor

  · simp only [delAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_del_dir hs (hF S) _).mul contDiffOn_const

  · simp only [dbarAt, coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul, Finset.sum_apply',
    Finsupp.smul_apply, smul_eq_mul]
    exact ContDiffOn.sum fun a _ => ContDiffOn.sum fun S _ => (contDiffOn_dbar_dir hs (hF S) _).mul contDiffOn_const

end GlobalTheory.CxForm.SmoothCoef
