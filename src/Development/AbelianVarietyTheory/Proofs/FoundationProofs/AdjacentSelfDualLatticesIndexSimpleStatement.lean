module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimple
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

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.adjacent_selfDual_lattices_index_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → idx A B = Nat.card (R ⧸ P) ∧ idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  first | exact @GlobalTheory.FinWeil.adjacent_selfDual_simple | exact GlobalTheory.FinWeil.adjacent_selfDual_simple | (intros; apply GlobalTheory.FinWeil.adjacent_selfDual_simple <;> assumption)
