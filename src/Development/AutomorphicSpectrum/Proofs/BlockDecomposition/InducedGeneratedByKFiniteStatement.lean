module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Basic
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InducedGeneratedByKFinite
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


theorem _root_.GlobalTheory.T.induced_generated_by_K_finite : ∀ {Γ J : Type} [Group Γ] [AddCommGroup J] [Module ℂ J] (Q K K₁ : Subgroup Γ) (π : Representation ℂ Q J) (M : Submodule ℂ (Γ → J)) (Gf : Γ → J), K₁ ≤ K → K₁.relIndex K ≠ 0 → (∀ κ ∈ K, ∀ b ∈ K₁, κ * b * κ⁻¹ ∈ K₁) → (∀ g : Γ, ∃ q : Q, ∃ κ ∈ K, g = (q : Γ) * κ) → (∀ φ ∈ M, ∀ x : Γ, (fun g => φ (g * x)) ∈ M) → (∀ φ ∈ M, ∀ (q : Q) (g : Γ), φ ((q : Γ) * g) = π q (φ g)) → (∀ (q : Q) (g : Γ), Gf ((q : Γ) * g) = π q (Gf g)) → (∀ (g : Γ), ∀ b ∈ K₁, Gf (g * b) = Gf g) → (∀ κ ∈ K, ∃ φ ∈ M, (∀ (q : Q), ∀ b ∈ K₁, φ ((q : Γ) * b) = π q (Gf κ)) ∧ ∀ g : Γ, (¬ ∃ q : Q, ∃ b ∈ K₁, g = (q : Γ) * b) → φ g = 0) → Gf ∈ M := by
  first | exact @GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | exact GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps | (intros; apply GlobalTheory.CompanionTheory.CosetSum.mem_of_translated_bumps <;> assumption)
