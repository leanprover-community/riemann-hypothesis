module

public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.WeightOccurrence.OccSome
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HeBranching
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory Matrix Finset Formalism.REAL Formalism.MainNotions.S PI.DSInfCharCap GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods
open scoped InnerProductSpace ComplexConjugate

namespace PositivityTheory.RgHe.A

def SchurEigenProjectionExists : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' mu _ e H H' _ _ _ _ _ _ π σ ν =>
  GlobalTheory.CompanionTheory.PairingAnalysis.HeWord ε lam ε' mu → ∀ κ : ℝ, PositivityTheory.RgHe.SchurK ε' σ ν κ → ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν ∧
    ∃ (i : H' →L[ℂ] H) (η : H), (∀ x, ‖i x‖ = ‖x‖) ∧
      (∀ h : UJ ε', ∀ x, i (σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) x) = π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) (i x)) ∧
      η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π ∧ ⟪η, i w⟫_ℂ ≠ 0 ∧
      ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, i w⟫_ℂ * ⟪i w, a⟫_ℂ)

def MomentP : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' _ B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ (P : H →L[ℂ] H') (w : H') (κ : ℝ), GlobalTheory.CompanionTheory.PairingAnalysis.Intertw ε' e π σ P → ‖w‖ = 1 →
    ‖ContinuousLinearMap.adjoint P w‖ = 1 → 0 < κ →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν →
    (∀ x : UJ ε', ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um (h⁻¹ * x)) w⟫_ℂ ∂ν =
      κ * conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um x) w⟫_ℂ) →
    (∃ η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π, ⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ ≠ 0 ∧
      ∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
        κ * (⟪η, ContinuousLinearMap.adjoint P w⟫_ℂ * ⟪ContinuousLinearMap.adjoint P w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 →
      ∫⁻ g : UJ ε, ENNReal.ofReal (GlobalTheory.CompanionTheory.PairingAnalysis.colSq (GlobalTheory.CompanionTheory.PairingAnalysis.um g⁻¹) (GlobalTheory.CompanionTheory.PairingAnalysis.zi e) *
          ‖⟪ContinuousLinearMap.adjoint P w, π (GlobalTheory.CompanionTheory.PairingAnalysis.um g) v⟫_ℂ‖ ^ 2) ∂(muG ε) ≤
        ENNReal.ofReal ((8 * ((n : ℝ) + 1) * B) ^ (8 * (n + 1))) *
          ∫⁻ g : UJ ε, ENNReal.ofReal (‖⟪ContinuousLinearMap.adjoint P w, π (GlobalTheory.CompanionTheory.PairingAnalysis.um g) v⟫_ℂ‖ ^ 2) ∂(muG ε)

def BigProjP : Prop := GlobalTheory.CompanionTheory.PairingAnalysis.ForPairs fun {n} ε lam ε' mu B e H H' _ _ _ _ _ _ π σ ν =>
  ∀ κ : ℝ, PositivityTheory.RgHe.SchurK ε' σ ν κ → ∀ w ∈ lowKSub ε' mu σ, ‖w‖ = 1 →
    Integrable (fun h : UJ ε' => ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ) ν → ∀ (i : H' →L[ℂ] H) (η : H), (∀ x, ‖i x‖ = ‖x‖) →
    (∀ h : UJ ε', ∀ x, i (σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) x) = π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) (i x)) →
    η ∈ PI.PhMeasCore.smoothVecs (Jm ε) π → ⟪η, i w⟫_ℂ ≠ 0 →
    (∀ a : H, ∫ h : UJ ε', conj ⟪w, σ (GlobalTheory.CompanionTheory.PairingAnalysis.um h) w⟫_ℂ * ⟪η, π (GlobalTheory.CompanionTheory.PairingAnalysis.emb e (GlobalTheory.CompanionTheory.PairingAnalysis.um h)) a⟫_ℂ ∂ν =
      κ * (⟪η, i w⟫_ℂ * ⟪i w, a⟫_ℂ)) →
    ∀ v ∈ lowKSub ε lam π, ‖v‖ = 1 → ∃ g₀ : UJ ε, hs (GlobalTheory.CompanionTheory.PairingAnalysis.um g₀) ≤ (8 * ((n : ℝ) + 1) * B) ^ (20 * (n + 1)) ∧
      Real.exp (-(100 * ((n : ℝ) + 1) ^ 3 * Real.log (8 * (n + 1) * B))) ≤
        ‖ContinuousLinearMap.adjoint i (π (GlobalTheory.CompanionTheory.PairingAnalysis.um g₀) v)‖

end PositivityTheory.RgHe.A
