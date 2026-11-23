module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FubiniStudyMetricSmooth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.HeightComparisonBetweenModels
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
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ExistsIntSmulIsAdicIntegralInTensorBasis

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

theorem _root_.GlobalTheory.T.height_comparison_between_models : Top.Given → PtsIntegrableStatement →
    ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem)
      (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω]
      (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)]
      (D : ComponentData II Ψ K J Ω W) (Hd : HodgeData D) (M M' : XModel D)
      (S : LogLogRegularisationSetting M D.Xo (muLine Hd))
      (S₁ : LogLogRegularisationSetting M' D.Xo (muLine Hd)) (B : ℕ),
      IsFullIntersectionSystem II → S.IsTied → S₁.IsTied →
      ArLimExists Hd S B ∧ arLim Hd S B = arLim Hd S₁ B := by
  intro hG _ K _ J _ II Ψ _ Ω _ _ W _ _ D Hd M M' S S₁ B hII hS hS₁
  have hIn : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  have hNb : IsSmoothHerm (fsHerm J (muTwDeg Hd B)) := PB.StepW.fsHerm_isSmoothHerm K J _
  have h₁ := tendsto_arLimFun hIn.metricLocal S hS B hII _ hNb rfl
  have h₂ := tendsto_arLimFun hIn.metricLocal S₁ hS₁ B hII _ hNb rfl
  exact ⟨⟨_, h₁⟩, by rw [arLim, arLim, h₁.limUnder_eq, h₂.limUnder_eq]⟩
