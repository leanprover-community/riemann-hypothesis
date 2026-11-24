module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NotInjOnOfFderivEqZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
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
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

@[expose] public section

open scoped Topology
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.InjHol

theorem analyticAt_of_differentiableOn_euclidean {n : ℕ} {W : Set (V n)} {g : V n → V n} {a : V n}
    (hW : IsOpen W) (ha : a ∈ W) (hg : DifferentiableOn ℂ g W) : AnalyticAt ℂ g a := by
  let e : V n ≃L[ℂ] (Fin n → ℂ) := EuclideanSpace.equiv (Fin n) ℂ
  have hU : IsOpen (e.symm ⁻¹' W) := hW.preimage e.symm.continuous
  have hf : DifferentiableOn ℂ (fun x => e (g (e.symm x))) (e.symm ⁻¹' W) :=
    e.differentiable.comp_differentiableOn
      (hg.comp e.symm.differentiable.differentiableOn (fun _ hx => hx))
  have ha' : e a ∈ e.symm ⁻¹' W := by simpa using ha
  have han : AnalyticAt ℂ (fun x => e (g (e.symm x))) (e a) := analyticAt_pi_iff.mpr fun i =>
    ReciprocityTheory.AnForm.Osgood.osgood n _ (fun x => e (g (e.symm x)) i) hU
      (differentiableOn_pi.mp hf i) _ ha'
  have h2 : AnalyticAt ℂ (fun y => e.symm (e (g (e.symm (e y))))) a :=
    ((e.symm : (Fin n → ℂ) →L[ℂ] V n).analyticAt _).comp
      (han.comp ((e : V n →L[ℂ] (Fin n → ℂ)).analyticAt a))
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using h2

theorem exists_local_inverse_of_injOn :
    ∀ (n : ℕ) (W : Set (V n)) (g : V n → V n) (a : V n), IsOpen W → a ∈ W →
      DifferentiableOn ℂ g W → Set.InjOn g W →
      ∃ h : V n → V n, ∀ᶠ u in 𝓝 (g a), h u ∈ W ∧ g (h u) = u ∧ DifferentiableAt ℂ h u := by
  intro n W g a hW ha hg hinj
  have han := analyticAt_of_differentiableOn_euclidean hW ha hg
  have hi : Function.Injective (fderiv ℂ g a) :=
    localStatement n _ _ (by simp) (by simp) g a han ⟨W, hW.mem_nhds ha, hinj⟩
  have hs : Function.Surjective (fderiv ℂ g a) := LinearMap.injective_iff_surjective.mp
    (show Function.Injective (fderiv ℂ g a : V n →ₗ[ℂ] V n) from hi)
  let f' : V n ≃L[ℂ] V n := ContinuousLinearEquiv.ofBijective (fderiv ℂ g a)
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  have hf' : HasFDerivAt g (f' : V n →L[ℂ] V n) a := han.differentiableAt.hasFDerivAt
  have hc : ContDiffAt ℂ 1 g a := han.contDiffAt
  have hn : (1 : WithTop ℕ∞) ≠ 0 := one_ne_zero
  have hG := hc.to_localInverse hf' hn
  have hGv := hc.localInverse_apply_image hf' hn
  refine ⟨hc.localInverse hf' hn, ?_⟩
  have hT : Filter.Tendsto (hc.localInverse hf' hn) (𝓝 (g a)) (𝓝 a) := by
    have := hG.continuousAt.tendsto
    rwa [hGv] at this
  have hr : ∀ᶠ u in 𝓝 (g a), g (hc.localInverse hf' hn u) = u :=
    (hc.hasStrictFDerivAt' hf' hn).eventually_right_inverse
  filter_upwards [hT.eventually (hW.mem_nhds ha), hr, hG.eventually (by simp)] with u h1 h2 h3
  exact ⟨h1, h2, h3.differentiableAt hn⟩

end GlobalTheory.InjHol
