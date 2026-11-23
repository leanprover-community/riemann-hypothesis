module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.MeasureTheory.Group.Measure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingOfProjectionSupport
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

@[expose] public section

open MeasureTheory

theorem _root_.GlobalTheory.T.vanishing_of_projection_support : ∀ {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [LocallyCompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [μ.IsAddHaarMeasure] (P : X →+ X), Continuous P →
    (∀ x, P (P x) = P x) → ∀ (Φ Ψ : X → ℂ), Continuous Φ → Continuous Ψ → ∀ K : Set X, IsCompact K →
    (∀ x, Φ x ≠ 0 → P x ∈ K) → ∀ y : X, (∀ z, P z = z → Φ (y + z) = 0) →
    (∀ O : Set X, IsOpen O → y ∈ O → ∃ h : X → ENNReal, Measurable h ∧ (∀ x, h x ≤ 1) ∧
      (∀ x z, P z = z → h (x + z) = h x) ∧ (∀ x, h x ≠ 0 → x + (P y - P x) ∈ O) ∧
      (∃ O' : Set X, IsOpen O' ∧ y ∈ O' ∧ ∀ x ∈ O', Ψ x ≠ 0 → 1 / 2 ≤ h x) ∧
      ∫⁻ x, h x * ‖Ψ x‖ₑ ^ 2 ∂μ = ∫⁻ x, h x * ‖Φ x‖ₑ ^ 2 ∂μ) → Ψ y = 0 := by
  first | exact @GlobalTheory.FiberPointwise.vanish_at_point | exact GlobalTheory.FiberPointwise.vanish_at_point | (intros; apply GlobalTheory.FiberPointwise.vanish_at_point <;> assumption)
