module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsogenyFibresEvenThetaSigmaStarSquareQuotient
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

theorem _root_.GlobalTheory.T.isogeny_fibres_even_theta_sigmaStarSquareQuotient : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ (β t₀ : ℂ) (k : ℕ), (∀ ω ∈ Λ, β * ω ∈ Λ) → β + starRingEnd ℂ β = 1 → β * starRingEnd ℂ β = ((2 * k : ℕ) : ℂ) → 2 * t₀ ∈ Λ → β * t₀ ∉ Λ → (1 - β) * t₀ ∉ Λ → ∃ (Q : Fin k → ℂ) (Q' : Fin (2 * k) → ℂ), (∀ i, Q i ∉ Λ ∧ InRationalLattice Λ (Q i)) ∧ (∀ j, Q' j ∉ Λ ∧ InRationalLattice Λ (Q' j)) ∧ (∀ z, GL3Theta.th0 Λ t₀ (β * z) = ∏ i, sqTh Λ (Q i) z) ∧ (∀ z, sqTh Λ (β * t₀) (β * z) = ∏ j, sqTh Λ (Q' j) z) ∧ (∀ i j, wpF Λ (Q i) ≠ wpF Λ (Q' j)) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ t₀) ∧ (∃ j, wpF Λ (Q' j) = wpF Λ (β * t₀)) ∧ wpF Λ t₀ ≠ wpF Λ (β * t₀) := by
  first | exact @GlobalTheory.EvenTheta.Fibres.isogeny_fibres | exact GlobalTheory.EvenTheta.Fibres.isogeny_fibres | (intros; apply GlobalTheory.EvenTheta.Fibres.isogeny_fibres <;> assumption)
