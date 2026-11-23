module

public import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Geometry.Manifold.StructureGroupoid

@[expose] public section

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

theorem _root_.GlobalTheory.T.qExpansionCoeffsInSubring_ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N → (∀ c ∈ R, QAll (· ∈ R) N fun _ => c) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ + g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ - g τ) ∧ (∀ f g, QAll (· ∈ R) N f → QAll (· ∈ R) N g → QAll (· ∈ R) N fun τ => f τ * g τ) ∧ (∀ f (k : ℕ), QAll (· ∈ R) N f → QAll (· ∈ R) N fun τ => f τ ^ k) ∧ (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ), (∀ k ∈ s, QAll (· ∈ R) N (f k)) → (QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧ QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  first | exact @GlobalTheory.QFam.QAllSubring.ring_closed | exact GlobalTheory.QFam.QAllSubring.ring_closed | (intros; apply GlobalTheory.QFam.QAllSubring.ring_closed <;> assumption)
