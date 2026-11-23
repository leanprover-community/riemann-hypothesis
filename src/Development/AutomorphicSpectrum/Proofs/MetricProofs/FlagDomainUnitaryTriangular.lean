module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ContinuousNormMulOneAddAbsLogPow
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Sheaves.Init
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.SmulOneLeAndLeSmulOneIffEigenvalues

@[expose] public section

open Complex Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_extension_polydisc_of_log_growth :
    ∀ (n : ℕ) (S : Finset (Fin n)) (φ : (Fin n → ℂ) → ℂ) (ρ C : ℝ) (N : ℕ), 0 < ρ →
      DifferentiableOn ℂ φ {z ∈ ball (0 : Fin n → ℂ) ρ | ∀ i ∈ S, z i ≠ 0} →
      (∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) →
        ‖φ z‖ ≤ C * (1 + ∑ i ∈ S, |Real.log ‖z i‖|) ^ N) →
      ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ (ball 0 ρ) ∧
        ∀ z ∈ ball (0 : Fin n → ℂ) ρ, (∀ i ∈ S, z i ≠ 0) → ψ z = φ z := by
  intro n S φ ρ C N _ hφ hb
  have hg : HasLogGrowth S id (ball (0 : Fin n → ℂ) ρ) φ := fun K hK _ =>
    ⟨C, N, fun z hz hB => hb z (hK hz) (notMem_coordDivisor.1 hB)⟩
  obtain ⟨ψ, hψ, he⟩ := HasLogGrowth.exists_differentiableOn_extension isOpen_ball
    (hφ.mono fun z hz => ⟨hz.1, notMem_coordDivisor.1 hz.2⟩) hg
  exact ⟨ψ, hψ, fun z hz h0 => he ⟨hz, notMem_coordDivisor.2 h0⟩⟩

end GlobalTheory.CompanionTheory.Ar.Flat
