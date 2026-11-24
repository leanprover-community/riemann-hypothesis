module

public import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollifierL2LocTendsto
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.B

open MeasureTheory Filter Topology Set Metric
open scoped Convolution ContDiff ENNReal Pointwise

theorem fderiv_moll_apply (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] (K : Kernel E μ) {u : E → ℂ} (hu : LocallyIntegrable u μ)
    (x a : E) :
    fderiv ℝ (moll K u) x a = ∫ y, (fderiv ℝ K.toFun (x - y) a) • u y ∂μ := by
  have hcs : HasCompactSupport K.toFun :=
    HasCompactSupport.intro (isCompact_closedBall (0 : E) K.r) fun y hy => by
      by_contra h
      exact hy (ball_subset_closedBall (K.support_subset h))
  have hd := hcs.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (K.smooth.of_le (by simp)) hu x
  have hmoll : moll K u = K.toFun ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] u := rfl
  rw [hmoll, hd.fderiv]
  have hex := (hcs.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL E) (K.smooth.continuous_fderiv (by simp)) hu x
  rw [convolution_def, ContinuousLinearMap.integral_apply hex]
  rw [← integral_sub_left_eq_self _ μ x]
  congr 1
  ext y
  rw [sub_sub_cancel]
  rfl

theorem moll_weakComm (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] : WeakCommSt E μ := by
  intro m c v g w hw K
  funext x
  have hd : ∀ k, fderiv ℝ (moll K (g k)) x (v k) =
      ∫ y, (fderiv ℝ K.toFun (x - y) (v k)) • g k y ∂μ :=
    fun k => fderiv_moll_apply E μ K (hw.1 k) x (v k)
  set φ : E → ℂ := fun y => ((K.toFun (x - y) : ℝ) : ℂ) with hφdef
  have hφs : ContDiff ℝ ∞ φ :=
    Complex.ofRealCLM.contDiff.comp (K.smooth.comp (contDiff_const.sub contDiff_id))
  have hφc : HasCompactSupport φ :=
    HasCompactSupport.intro (isCompact_closedBall x K.r) fun y hy => by
      simp only [hφdef, Complex.ofReal_eq_zero]
      by_contra h
      apply hy
      have h' := K.support_subset h
      rw [mem_ball_zero_iff] at h'
      rw [mem_closedBall, dist_eq_norm, ← norm_neg, neg_sub]
      exact h'.le
  have hw3 := hw.2.2 φ hφs hφc
  have hdφ : ∀ y a, fderiv ℝ φ y a = -((fderiv ℝ K.toFun (x - y) a : ℝ) : ℂ) := by
    intro y a
    have h1 : HasFDerivAt (fun y : E => x - y) (-ContinuousLinearMap.id ℝ E) y :=
      (hasFDerivAt_id y).const_sub x
    have h2 := ((K.smooth.differentiable (by simp)) (x - y)).hasFDerivAt.comp y h1
    have h3 := Complex.ofRealCLM.hasFDerivAt.comp y h2
    rw [(show HasFDerivAt φ _ y from h3).fderiv]
    simp
  have hm : moll K w x = ∫ y, w y * φ y ∂μ := by
    show ∫ t, K.toFun t • w (x - t) ∂μ = _
    rw [← integral_sub_left_eq_self (fun t => K.toFun t • w (x - t)) μ x]
    congr 1
    ext y
    simp only [hφdef, sub_sub_cancel, Complex.real_smul]
    ring
  simp only [Dop, hd]
  rw [hm, hw3, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_neg, ← integral_neg]
  congr 2
  ext y
  rw [hdφ, Complex.real_smul]
  ring

end ReciprocityTheory.L2DbarEstimates.B
