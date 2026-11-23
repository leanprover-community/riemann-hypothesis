module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StAnalyticSimpleRootBranch
public import Mathlib.Analysis.Calculus.ImplicitContDiff
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
open scoped ContDiff

noncomputable section

theorem AnalyticSimpleRootBranch.proof : AnalyticSimpleRootBranch.Statement := by
  intro d N a y τ ha hroot hder
  set p : Polynomial ℂ := Polynomial.X ^ N + ∑ j, Polynomial.C (a j y) * Polynomial.X ^ (j : ℕ) with hp
  set F : (Fin d → ℂ) × ℂ → ℂ := fun v => v.2 ^ N + ∑ j, a j v.1 * v.2 ^ (j : ℕ) with hF
  have hFa : AnalyticAt ℂ F (y, τ) := by
    refine (analyticAt_snd.pow N).add (Finset.analyticAt_fun_sum _ fun j _ => ?_)
    exact ((ha j).comp (analyticAt_fst (p := (y, τ)))).mul (analyticAt_snd.pow _)
  have hcd : ContDiffAt ℂ ω F (y, τ) := hFa.contDiffAt
  have hpe : ∀ s, p.eval s = F (y, s) := by
    intro s
    simp [hp, hF, Polynomial.eval_finsetSum]

  have hpart : fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ =
      (1 : ℂ →L[ℂ] ℂ).smulRight (p.derivative.eval τ) := by
    have h1 : HasFDerivAt (fun s : ℂ => F (y, s))
        (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ) τ :=
      (hFa.differentiableAt.hasFDerivAt).comp τ ((hasFDerivAt_const y τ).prodMk (hasFDerivAt_id τ))
    have h2 : (fun s : ℂ => F (y, s)) = fun s => p.eval s := funext fun s => (hpe s).symm
    rw [h2] at h1
    exact h1.unique (p.hasDerivAt τ).hasFDerivAt
  have hinv : (fderiv ℂ F (y, τ) ∘L ContinuousLinearMap.inr ℂ (Fin d → ℂ) ℂ).IsInvertible := by
    rw [hpart]
    refine ⟨ContinuousLinearEquiv.unitsEquivAut ℂ (Units.mk0 _ hder), ?_⟩
    ext; simp
  have hω : (ω : WithTop ℕ∞) ≠ 0 := by simp
  set ψ := hcd.implicitFunction hω hinv with hψdef
  have hψy : ψ y = τ := hcd.implicitFunction_apply_self hω hinv
  have hψa : AnalyticAt ℂ ψ y := (hcd.contDiffAt_implicitFunction hω hinv).analyticAt
  have hF0 : F (y, τ) = 0 := hroot
  obtain ⟨U₁, B, hU₁o, hyU₁, hBo, hτB, hsub⟩ :=
    mem_nhds_prod_iff'.mp (hcd.eventually_apply_eq_iff_implicitFunction hω hinv)
  set W : Set (Fin d → ℂ) := U₁ ∩ {x | AnalyticAt ℂ ψ x} with hW
  have hWo : IsOpen W := hU₁o.inter (isOpen_analyticAt ℂ ψ)
  have hWc : ContinuousOn ψ W := fun x hx => hx.2.continuousAt.continuousWithinAt
  refine ⟨W ∩ ψ ⁻¹' B, B, ψ, hWc.isOpen_inter_preimage hWo hBo, ⟨⟨hyU₁, hψa⟩, by simpa [hψy] using hτB⟩,
    hBo, hτB, fun x hx => hx.1.2, hψy, fun y' hy' => ⟨hy'.2, fun s hs => ?_⟩⟩
  have h := hsub (Set.mk_mem_prod hy'.1.1 hs)
  simp only [Set.mem_ofPred_eq] at h
  change F (y', s) = 0 ↔ s = ψ y'
  rw [← hF0, h]
  exact eq_comm

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
