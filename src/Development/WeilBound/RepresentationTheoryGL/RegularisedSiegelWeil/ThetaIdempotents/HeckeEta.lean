module

public import Development.AbelianVarietyTheory.Definitions.Foundations.EventuallyEqOfIsPreconnected
public import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
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
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf

@[expose] public section

noncomputable section

open scoped Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel

namespace PositivityTheory.Rg.Rsw

def HeckeEta : Prop := ∀ (D : D7) (k : ℕ), ∃ χ : (AE D)ˣ →* Circle, IsHeckeChar D χ ∧ ResEta D χ k

def RightId : Prop :=
  ∀ (U : Set ℂ) (h g : ℂ → ℂ) (c σ : ℝ), IsOpen U → IsRightDomain U → DifferentiableOn ℂ h U →
    DifferentiableOn ℂ g {z : ℂ | c < z.re} → (∀ z : ℂ, σ < z.re → h z = g z) → ∀ z ∈ U, c < z.re → h z = g z

def PoleReal : Prop :=
  ∀ (h : ℂ → ℂ) (d : Polynomial ℂ) (s₀ ε : ℝ), 0 < ε → d ≠ 0 → DifferentiableOn ℂ h (Metric.closedBall (s₀ : ℂ) ε) →
    (∀ z ∈ Metric.sphere (s₀ : ℂ) ε, DifferentiableAt ℂ h z) →
    (∀ z ∈ Metric.closedBall (s₀ : ℂ) ε, z ≠ s₀ → d.eval z ≠ 0) →
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖((σ - s₀ : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))‖ ≤ B) →
      (∀ k : ℕ, 2 ≤ k → ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (k - 1) * (h z / d.eval z) = 0) ∧
      Tendsto (fun σ : ℝ => ((σ - s₀ : ℝ) : ℂ) * (h σ / d.eval (σ : ℂ))) (𝓝[>] s₀)
        (𝓝 ((2 * Real.pi * Complex.I)⁻¹ * ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (1 - 1) * (h z / d.eval z)))) ∧
    ((∃ B : ℝ, ∀ᶠ σ : ℝ in 𝓝[>] s₀, ‖h σ / d.eval (σ : ℂ)‖ ≤ B) →
      ∀ k : ℕ, 1 ≤ k → ∮ z in C((s₀ : ℂ), ε), (z - s₀) ^ (k - 1) * (h z / d.eval z) = 0)

end PositivityTheory.Rg.Rsw

end
