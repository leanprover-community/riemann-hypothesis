module

import Development.AutomorphicSpectrum.Proofs.MembershipProofs.DenseHasCompactSupport
import Mathlib.Analysis.Distribution.SchwartzSpace.CompactSupport
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.Order.CompletePartialOrder
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas
import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.UniformSpace.Uniformizable
public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Geometry.Manifold.ContMDiff.Basic

@[expose] public section

noncomputable section

open Filter Topology MeasureTheory

namespace PositivityTheory.RL.Delta

open Complex
open scoped Real ContDiff

theorem hadamard_lemma : ∀ (n : ℕ) (f : (Fin n → ℝ) → ℂ), ContDiff ℝ ∞ f → f 0 = 0 → ∃ g : Fin n → (Fin n → ℝ) → ℂ, (∀ i, ContDiff ℝ ∞ (g i)) ∧ ∀ x, f x = ∑ i, (x i : ℂ) * g i x :=
  GlobalTheory.CompanionTheory.DiracComb.hadamard_lemma

theorem dense_hasCompactSupport : ∀ (n : ℕ), Dense {f : SchwartzMap (Fin n → ℝ) ℂ | HasCompactSupport (f : (Fin n → ℝ) → ℂ)} :=
  fun _ => SchwartzMap.dense_hasCompactSupport

theorem exists_quot : ∃ q : ℝ → ℂ, ContDiffOn ℝ ∞ q (Metric.ball 0 1) ∧
    ∀ t ∈ Metric.ball (0 : ℝ) 1, (t : ℂ) = (cexp (2 * π * I * t) - 1) * q t :=
  GlobalTheory.CompanionTheory.DiracComb.exists_quot

theorem exists_div (n : ℕ) (f : SchwartzMap (Fin n → ℝ) ℂ)
    (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) :
    ∃ g : Fin n → SchwartzMap (Fin n → ℝ) ℂ, (∀ i, HasCompactSupport (g i : (Fin n → ℝ) → ℂ)) ∧
      ∀ x, f x = ∑ i, (cexp (2 * π * I * x i) - 1) * g i x :=
  GlobalTheory.CompanionTheory.DiracComb.exists_div n f hf h0

theorem zero_of_ball (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ), (∀ x, g x = cexp (2 * π * I * x i) * f x) → T g = T f)
    (f : SchwartzMap (Fin n → ℝ) ℂ) (hf : tsupport (f : (Fin n → ℝ) → ℂ) ⊆ Metric.ball 0 1) (h0 : f 0 = 0) : T f = 0 := by
    obtain ⟨g, hg, hg'⟩ := exists_div n f hf h0
    have hsm : ∀ i, ContDiff ℝ ∞ (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) := by
      intro i
      refine ContDiff.mul ?_ ((g i).smooth ⊤)
      exact (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ (fun _ => ℝ) i))).cexp
    have hcs : ∀ i, HasCompactSupport (fun x : Fin n → ℝ => cexp (2 * π * I * x i) * g i x) :=
      fun i => (hg i).mul_left
    have e : f = ∑ i, ((hcs i).toSchwartzMap (hsm i) - g i) := by
      ext x
      rw [hg' x, _root_.sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show _ = cexp (2 * π * I * x i) * g i x - g i x
      ring

    rw [e, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_sub, hχ i (g i) _ (fun x => rfl), sub_self]

theorem eq_delta (n : ℕ) (T : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ)
    (hχ : ∀ (t : ℝ) (i : Fin n) (f g : SchwartzMap (Fin n → ℝ) ℂ),
      (∀ x, g x = cexp (2 * π * I * (t * x i : ℝ)) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap (Fin n → ℝ) ℂ, T f = a * f 0 := by
  have hA : ∀ f : SchwartzMap (Fin n → ℝ) ℂ, HasCompactSupport (f : (Fin n → ℝ) → ℂ) → f 0 = 0 → T f = 0 := by
    intro f hf h0
    obtain ⟨R, hR, hs⟩ := hf.isCompact.isBounded.subset_ball_lt 0 0
    let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) := ContinuousLinearEquiv.smulLeft (Units.mk0 R hR.ne')
    have he : ∀ x, e x = R • x := fun _ => rfl
    have he' : ∀ x, e.symm x = R⁻¹ • x := fun x => e.injective (by rw [e.apply_symm_apply, he, smul_inv_smul₀ hR.ne'])
    have := zero_of_ball n (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm)
      (fun i f g h => hχ R⁻¹ i _ _ fun x => by
        show g (e.symm x) = _ * f (e.symm x)
        rw [h, he']; simp) (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ?_ (by
        show f (e 0) = 0
        rw [map_zero, h0])
    · rw [← this]
      exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.apply_symm_apply x).symm)
    · have hsub : Function.support (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e f) ⊆ e ⁻¹' tsupport f :=
        fun x hx => subset_tsupport _ hx
      refine (closure_minimal hsub ((isClosed_tsupport _).preimage e.continuous)).trans fun x hx => ?_
      have := hs hx
      rw [mem_ball_zero_iff, he, norm_smul, Real.norm_eq_abs, abs_of_pos hR] at this
      rw [mem_ball_zero_iff]
      exact (mul_lt_iff_lt_one_right hR).1 this
  let b : ContDiffBump (0 : Fin n → ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩
  have h₁ : HasCompactSupport (Complex.ofRealCLM ∘ (b : (Fin n → ℝ) → ℝ)) :=
    b.hasCompactSupport.comp_left rfl
  let ψ : SchwartzMap (Fin n → ℝ) ℂ :=
    h₁.toSchwartzMap (Complex.ofRealCLM.contDiff.comp b.contDiff)
  have hψ : ∀ x, ψ x = (b x : ℂ) := fun x => rfl
  have hψ0 : ψ 0 = 1 := by
    rw [hψ, b.one_of_mem_closedBall (Metric.mem_closedBall_self b.rIn_pos.le)]; simp
  refine ⟨T ψ, fun f => ?_⟩
  let S : SchwartzMap (Fin n → ℝ) ℂ →L[ℂ] ℂ :=
    BoundedContinuousFunction.evalCLM ℂ 0 ∘L SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ _
  have hcl : IsClosed {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f} :=
    isClosed_eq T.continuous (continuous_const.mul S.continuous)
  refine closure_minimal (t := {f : SchwartzMap (Fin n → ℝ) ℂ | T f = T ψ * S f}) ?_ hcl (dense_hasCompactSupport n f)
  intro f hf
  have := hA (f - f 0 • ψ) (HasCompactSupport.sub hf (HasCompactSupport.smul_left (f := fun _ => f 0) h₁)) (by
    show f 0 - f 0 • ψ 0 = 0
    rw [hψ0]; simp)
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul, mul_comm] at this
  exact this

theorem eq_delta' {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (T : SchwartzMap V ℂ →L[ℂ] ℂ)
    (hχ : ∀ (l : V →ₗ[ℝ] ℝ) (f g : SchwartzMap V ℂ), (∀ x, g x = cexp (2 * π * I * l x) * f x) → T g = T f) :
    ∃ a : ℂ, ∀ f : SchwartzMap V ℂ, T f = a * f 0 := by
  let e : V ≃L[ℝ] (Fin (Module.finrank ℝ V) → ℝ) := (Module.finBasis ℝ V).equivFun.toContinuousLinearEquiv
  obtain ⟨a, ha⟩ := eq_delta _ (T ∘L SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e) fun t i f g h =>
    hχ (t • (LinearMap.proj i ∘ₗ e.toLinearEquiv.toLinearMap)) _ _ fun x => h (e x)
  refine ⟨a, fun f => ?_⟩
  have := ha (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e.symm f)
  refine Eq.trans ?_ (this.trans ?_)
  · exact congrArg T (SchwartzMap.ext fun x => congrArg f (e.symm_apply_apply x).symm)
  · show a * f (e.symm 0) = _
    rw [map_zero]

end PositivityTheory.RL.Delta

end
