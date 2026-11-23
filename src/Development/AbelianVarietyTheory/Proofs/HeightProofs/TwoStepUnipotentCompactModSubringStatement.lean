module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.TwoStepUnipotentCompactModSubring
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

open NumberField IsDedekindDomain MeasureTheory

theorem _root_.GlobalTheory.T.twoStepUnipotent_compact_mod_subring : ∀ (S : Type) [Ring S] [TopologicalSpace S] [IsTopologicalRing S] (st : S →+ S) (S₀ : Subring S) (e₁ e₃ h : S) (K : Set S), Continuous st → (∀ x y, st (x * y) = st y * st x) → (∀ x, st (st x) = x) → (∀ x ∈ S₀, st x ∈ S₀) → e₁ ∈ S₀ → h ∈ S₀ → e₁ * e₁ = e₁ → st e₁ = e₃ → e₁ * e₃ = 0 → e₃ * e₁ = 0 → h + h = 1 → (∀ x, h * x = x * h) → IsCompact K → (∀ x, ∃ y ∈ S₀, x - y ∈ K) → ∃ K' : Set Sˣ, IsCompact K' ∧ (∀ g ∈ K', (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0)) ∧ ∀ g : Sˣ, (st (g : S) * (g : S) = 1 ∧ ((g : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((g : S) - 1) * (1 - e₃) = 0) → ∃ γ : Sˣ, (st (γ : S) * (γ : S) = 1 ∧ ((γ : S) - 1) * e₁ = 0 ∧ (1 - e₁) * ((γ : S) - 1) * (1 - e₃) = 0) ∧ (γ : S) ∈ S₀ ∧ ((γ⁻¹ : Sˣ) : S) ∈ S₀ ∧ γ * g ∈ K' := by
  first | exact @GlobalTheory.TwoStepUnipotent.compact_mod_subring | exact GlobalTheory.TwoStepUnipotent.compact_mod_subring | (intros; apply GlobalTheory.TwoStepUnipotent.compact_mod_subring <;> assumption)
