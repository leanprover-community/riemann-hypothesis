module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Classical GlobalTheory.FinWeil
open scoped BigOperators

theorem _root_.GlobalTheory.T.sumOp_transversal_fixes_linear_and_of_le : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ B → (∀ v, Fixes W A v → ∀ (ι : Type) [Fintype ι] (f : ι → X), (∀ i, f i ∈ B) → (∀ b ∈ B, ∃! i, b - f i ∈ A) → sumOp W A B v = ∑ i, W (f i) v ∧ idx A B = Fintype.card ι) ∧ (idx A B ≠ 0 → (∃ (n : ℕ) (f : Fin n → X), (∀ i, f i ∈ B) ∧ ∀ b ∈ B, ∃! i, b - f i ∈ A) ∧ (∀ v, Fixes W A v → Fixes W B (sumOp W A B v)) ∧ ∀ (c : ℂ) v, sumOp W A B (c • v) = c • sumOp W A B v) ∧ (B ≤ A → idx A B = 1 ∧ ∀ v, Fixes W A v → sumOp W A B v = v) := by
  first | exact @GlobalTheory.FinWeil.sumOp_transversal | exact GlobalTheory.FinWeil.sumOp_transversal | (intros; apply GlobalTheory.FinWeil.sumOp_transversal <;> assumption)
