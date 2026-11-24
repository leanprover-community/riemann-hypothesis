module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJATCModConstCut
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

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC

noncomputable section

def DTExists : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∃ h ∈ UWset k r z, ∃ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ ∧
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ ∧
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂

def DTStab : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ),
    2 ≤ k → inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → IsSection k r z z' μsec →
    ∀ ζ₁ ζ₂ : ℂ, Tz k r z * Tz k r z' < Complex.normSq ζ₁ → Tz k r z * Tz k r z' < Complex.normSq ζ₂ →
    ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z',
      h *ᵥ SSn.nu0 k r z z' μsec ζ₁ = SSn.nu0 k r z z' μsec ζ₂ →
      h' *ᵥ SSn.nu0' k r z z' μsec ζ₁ = SSn.nu0' k r z z' μsec ζ₂ →
      h * SSn.io0 k r z z' μsec ζ₁ * h'⁻¹ = SSn.io0 k r z z' μsec ζ₂ →
      ∀ p ∈ NF.Stab k r z z' μsec ζ₂, (h⁻¹ * p.1 * h, h'⁻¹ * p.2 * h') ∈ NF.Stab k r z z' μsec ζ₁

theorem datumTransit_of_cut (hE : DTExists) (hS : DTStab) : DatumTransit := by
  intro k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  obtain ⟨h, hh, h', hh', e1, e2, e3⟩ := hE k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂
  exact ⟨h, hh, h', hh', e1, e2, e3, hS k r z z' μsec hk hz hz' hT hT' hsec ζ₁ ζ₂ h₁ h₂ h hh h' hh' e1 e2 e3⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep.Core.TC.MC
