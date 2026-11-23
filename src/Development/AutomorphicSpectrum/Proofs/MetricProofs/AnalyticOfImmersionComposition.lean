module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Composition
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

namespace GlobalTheory.CompanionTheory.Metric.Rigid

theorem analyticAt_of_comp_immersion {e : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] (F : (Fin e → ℂ) → Fin e → ℂ) (ψ : (Fin e → ℂ) → V)
    (H : (Fin e → ℂ) → V) (y₀ : Fin e → ℂ) (hψ : AnalyticAt ℂ ψ (F y₀))
    (hker : (fderiv ℂ ψ (F y₀)).ker = ⊥) (hH : AnalyticAt ℂ H y₀) (hF : ContinuousAt F y₀)
    (hEq : ∀ᶠ y in nhds y₀, ψ (F y) = H y) : AnalyticAt ℂ F y₀ := by
  classical
  obtain ⟨P₀, hP₀⟩ := ((fderiv ℂ ψ (F y₀) : (Fin e → ℂ) →L[ℂ] V) :
    (Fin e → ℂ) →ₗ[ℂ] V).exists_leftInverse_of_injective hker
  let P : V →L[ℂ] (Fin e → ℂ) := LinearMap.toContinuousLinearMap P₀
  have hPL : P.comp (fderiv ℂ ψ (F y₀)) = ContinuousLinearMap.id ℂ _ := by
    ext1 v
    exact LinearMap.congr_fun hP₀ v
  have hψd : HasFDerivAt ψ (fderiv ℂ ψ (F y₀)) (F y₀) := hψ.differentiableAt.hasFDerivAt
  have hgd : HasFDerivAt (fun x => P (ψ x))
      ((ContinuousLinearEquiv.refl ℂ (Fin e → ℂ) : (Fin e → ℂ) →L[ℂ] (Fin e → ℂ))) (F y₀) := by
    have h1 := P.hasFDerivAt.comp (F y₀) hψd
    rw [hPL] at h1
    simpa using h1
  have hga : AnalyticAt ℂ (fun x => P (ψ x)) (F y₀) := (P.analyticAt _).comp hψ
  have hgc : ContDiffAt ℂ (⊤ : WithTop ℕ∞) (fun x => P (ψ x)) (F y₀) := hga.contDiffAt
  have hn : (⊤ : WithTop ℕ∞) ≠ 0 := by simp
  have hφa := (hgc.to_localInverse hgd hn).analyticAt
  have hleft := (hgc.hasStrictFDerivAt' hgd hn).eventually_left_inverse
  have hH0 : ψ (F y₀) = H y₀ := hEq.self_of_nhds
  have hev : (fun y => hgc.localInverse hgd hn (P (H y))) =ᶠ[nhds y₀] F := by
    filter_upwards [hF.tendsto.eventually hleft, hEq] with y h1 h2
    rw [← h2]
    exact h1
  have hcomp : AnalyticAt ℂ (fun y => hgc.localInverse hgd hn (P (H y))) y₀ := by
    have h0 : AnalyticAt ℂ (hgc.localInverse hgd hn) (P (H y₀)) := by
      rw [← hH0]
      exact hφa
    have hPH : AnalyticAt ℂ (fun y => P (H y)) y₀ := (P.analyticAt (H y₀)).comp hH
    exact h0.comp_of_eq hPH rfl
  exact hcomp.congr hev

end GlobalTheory.CompanionTheory.Metric.Rigid
