module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainExtension.PointAssembly.ZnNonneg
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspCoefficientFlow
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FlowCoefficientBounds

@[expose] public section

namespace PIW.FdPA

open ReciprocityTheory.ChartRestriction.G.FD NumberField Complex MeasureTheory

noncomputable section

theorem fourierJacobi_differentiable {E : Type} [Field E] [NumberField E] [IsCMField E] : FjDiff E := by
  intro r X la P ξ ν hP hξ
  exact CuspCoefficientFlow.fj_diffOn (X := X) la P hP hξ ν

theorem fourierJacobi_bounded {E : Type} [Field E] [NumberField E] [IsCMField E] : FjBdd E := by
  intro r X la P ξ ν hP hξ
  obtain ⟨-, C, hC⟩ := hP
  exact ⟨C, fun x hx => FlowCoefficientBounds.fj_bound (X := X) la P C hC hξ ν hx⟩

theorem fourierJacobi_boundaryEq {E : Type} [Field E] [NumberField E] [IsCMField E] : FjBEq E := by
  intro r X la P ξ ν hP hξ x hx b hb
  classical
  have hflow : ∀ s : X.Ψ → ℝ, X.flow ξ (fun τ => (s τ : ℂ)) (rmul x b) =
      rmul (X.flow ξ (fun τ => (s τ : ℂ)) x) b := by
    intro s
    funext τ
    show X.flowMat ξ τ (s τ : ℂ) * (mat x τ * mat b τ) = X.flowMat ξ τ (s τ : ℂ) * mat x τ * mat b τ
    rw [Matrix.mul_assoc]
  have hP' : ∀ s : X.Ψ → ℝ,
      P (X.flow ξ (fun τ => (s τ : ℂ)) (rmul x b)) * cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ) =
        bchar la b * (P (X.flow ξ (fun τ => (s τ : ℂ)) x) *
          cexp (-(4 * Real.pi * I) * ∑ τ, (ν τ : ℂ) * s τ)) := by
    intro s
    rw [hflow, hP.2.1 _ (FlowCoefficientBounds.flow_real X hξ hx s la).1 b hb, mul_assoc]
  unfold Data.fj
  split_ifs with h1 h2
  · simp_rw [hP']
    rw [integral_const_mul]
    ring
  · simp
  · simp

end

end PIW.FdPA
