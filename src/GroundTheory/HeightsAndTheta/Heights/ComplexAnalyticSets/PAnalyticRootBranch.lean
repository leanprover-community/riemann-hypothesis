module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticRootBranch
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRiemannExtensionAnalytic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.ImplicitContDiff
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.Deriv.Polynomial

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Filter Topology

noncomputable section

theorem AnalyticRootBranch.proof : AnalyticRootBranch.Statement := by
  intro d N a t₀ τ₀ ha hsep hroot
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j t₀) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (t₀, τ₀) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (t₀, τ₀)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ 1 F (t₀, τ₀) := hFa.contDiffAt

  have hpe : ∀ s, p.eval s = F (t₀, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ₀) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (t₀, s))
        (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ₀ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ₀
        ((hasFDerivAt_const t₀ τ₀).prodMk (hasFDerivAt_id τ₀))
    have h2 : (fun s : ℂ => F (t₀, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ₀).hasFDerivAt

  have hder : p.derivative.eval τ₀ ≠ 0 := by
    have h := hsep.eval₂_derivative_ne_zero (RingHom.id ℂ) (x := τ₀)
      (by rw [Polynomial.eval₂_id, hpe]; exact hroot)
    rwa [Polynomial.eval₂_id] at h
  have hinv : (fderiv ℂ F (t₀, τ₀) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
  have hψt : ψ t₀ = τ₀ := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hψcd : ContDiffAt ℂ 1 ψ t₀ := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  obtain ⟨O, hOsub, hOo, ht₀O⟩ := eventually_nhds_iff.mp
    ((hcd.eventually_apply_implicitFunction one_ne_zero hinv).and (hψcd.eventually (by simp)))
  refine ⟨O, ψ, hOo, ht₀O, ?_, hψt, fun t ht => (hOsub t ht).1.trans hroot⟩
  refine RiemannExtensionAnalytic.analyticOnNhd_of_differentiableOn hOo fun t ht => ?_
  exact ((hOsub t ht).2.differentiableAt one_ne_zero).differentiableWithinAt

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
