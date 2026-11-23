module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocallyBoundedOffCoordinateHyperplanes
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

open Metric Filter Topology Set

theorem _root_.GlobalTheory.T.locally_bounded_off_coordinate_hyperplanes : (∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r → DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) → (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) → ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧ ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t) → ∀ (n a : ℕ) (ρ : ℝ) (Φ : (Fin n → ℂ) → ℂ) (m : Fin n → ℕ), 0 < ρ → DifferentiableOn ℂ Φ {z | z ∈ Metric.ball (0 : Fin n → ℂ) ρ ∧ ∀ k : Fin n, (k : ℕ) < a → z k ≠ 0} → (∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Complex.exp (2 * Real.pi * Complex.I * Φ z)‖ * ∏ k, ‖z k‖ ^ m k ≤ 1) → ∀ z₀ ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∃ V ∈ nhds z₀, ∃ M : ℝ, ∀ z ∈ V, z ∈ Metric.ball (0 : Fin n → ℂ) ρ → (∀ k : Fin n, (k : ℕ) < a → z k ≠ 0) → ‖Φ z‖ ≤ M := by
  first | exact @GlobalTheory.HyperplaneLocBound.locally_bounded | exact GlobalTheory.HyperplaneLocBound.locally_bounded | (intros; apply GlobalTheory.HyperplaneLocBound.locally_bounded <;> assumption)
