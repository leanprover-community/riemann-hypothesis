module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Separation.CompletelyRegular
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open NumberField MeasureTheory
open scoped RealInnerProductSpace FourierTransform

namespace GlobalTheory.HeckePoisson.Dilation

open GlobalTheory.HeckeTheta

variable {I : Type} [Fintype I]

def dilPi (y : I → ℝ) : (I → ℂ) →ₗ[ℝ] (I → ℂ) :=
  LinearMap.pi fun i => (Real.exp (y i / 2) • (LinearMap.id : ℂ →ₗ[ℝ] ℂ)).comp (LinearMap.proj i)

def dilE (y : I → ℝ) : EuclideanSpace ℂ I →ₗ[ℝ] EuclideanSpace ℂ I :=
  ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm : (I → ℂ) →ₗ[ℝ] EuclideanSpace ℂ I) ∘ₗ dilPi y ∘ₗ
    ((WithLp.linearEquiv 2 ℝ (I → ℂ)).symm.symm : EuclideanSpace ℂ I →ₗ[ℝ] (I → ℂ))

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_apply_eq_toLp_dil (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE y w = WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)) := by
  ext i
  simp [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, _root_.GlobalTheory.HeckeTheta.dil]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma dilE_neg_apply_dilE_apply (y : I → ℝ) (w : EuclideanSpace ℂ I) :
    _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y w) = w := by
  ext i
  simp only [dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, WithLp.ofLp_toLp, Pi.neg_apply, ← mul_assoc,
    ← Complex.ofReal_mul, ← Real.exp_add, neg_div, neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma det_dilE_eq_exp_sum (y : I → ℝ) : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) = Real.exp (∑ i, y i) := by
  rw [_root_.GlobalTheory.HeckePoisson.Dilation.dilE, LinearMap.det_conj, _root_.GlobalTheory.HeckePoisson.Dilation.dilPi, LinearMap.det_pi, Real.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex, ← Real.exp_nat_mul]
  congr 1
  push_cast
  ring

open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
private lemma inner_dilE_dilE_neg (y : I → ℝ) (v l : EuclideanSpace ℂ I) :
    ⟪_root_.GlobalTheory.HeckePoisson.Dilation.dilE y v, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫ = ⟪v, l⟫ := by
  simp [-Complex.ofReal_exp, dilE_apply_eq_toLp_dil, _root_.GlobalTheory.HeckeTheta.dil, real_inner_eq_re_inner, PiLp.inner_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Real.exp (y i / 2) * Real.exp (-y i / 2) = 1 := by
    rw [← Real.exp_add, show y i / 2 + -y i / 2 = 0 by ring, Real.exp_zero]
  linear_combination ((l.ofLp i).re * (v.ofLp i).re + (l.ofLp i).im * (v.ofLp i).im) * h


open NumberField MeasureTheory in
open scoped RealInnerProductSpace FourierTransform in
variable {I : Type} [Fintype I] in
theorem _root_.GlobalTheory.HeckePoisson.Dilation.fourier_comp_dil (I : Type) [Fintype I] (f : EuclideanSpace ℂ I → ℂ) (y : I → ℝ)
    (l : EuclideanSpace ℂ I) :
    𝓕 (fun w : EuclideanSpace ℂ I => f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil y (WithLp.ofLp w)))) l =
      (Real.exp (-∑ i, y i) : ℂ) * 𝓕 f (WithLp.toLp 2 (_root_.GlobalTheory.HeckeTheta.dil (-y) (WithLp.ofLp l))) := by
  let e : EuclideanSpace ℂ I ≃ₗ[ℝ] EuclideanSpace ℂ I :=
    LinearEquiv.ofLinear (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) (_root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y))
      (LinearMap.ext fun w => by simpa using dilE_neg_apply_dilE_apply (-y) w)
      (LinearMap.ext fun w => dilE_neg_apply_dilE_apply y w)
  have hemb : MeasurableEmbedding (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) :=
    e.toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
  have hdet : LinearMap.det (_root_.GlobalTheory.HeckePoisson.Dilation.dilE y) ≠ 0 := by
    rw [det_dilE_eq_exp_sum]
    exact (Real.exp_pos _).ne'
  have key := hemb.integral_map (μ := volume)
    (fun u => 𝐞 (-⟪u, _root_.GlobalTheory.HeckePoisson.Dilation.dilE (-y) l⟫) • f u)
  rw [Measure.map_linearMap_addHaar_eq_smul_addHaar _ hdet, integral_smul_measure] at key
  simp only [inner_dilE_dilE_neg] at key
  simp only [dilE_apply_eq_toLp_dil] at key
  rw [Real.fourier_eq, Real.fourier_eq, ← key, det_dilE_eq_exp_sum, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_pos (inv_pos.mpr (Real.exp_pos _)), ← Real.exp_neg, Complex.real_smul]

end GlobalTheory.HeckePoisson.Dilation
