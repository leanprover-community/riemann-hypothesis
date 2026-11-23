module

public import Development.AbelianVarietyTheory.Definitions.Divisors.IsEulerContraction
public import Development.WeilBound.CoreStatements.PublishedTheorems.NadelVanishingPairs.NadelVanishingLemmas.CartierProjectionProperties
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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

@[expose] public section

open GlobalTheory GlobalTheory.LogDR

theorem _root_.GlobalTheory.T.cartier_projection_properties : ∀ (K : Type) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] (n : ℕ) (x : Fin n → Kˣ), IsCoord x → ∃ (h Q : abelian₂ K →+ abelian₂ K) (π : K →+ K), (∀ η, η - Q η = extD K (h η) + h (extD K η)) ∧ (∀ c I, Q (c • logWedge x I) = π c • logWedge x I) ∧ (∀ c, ∃ g : K, π c = g ^ p) ∧ (∀ g : K, π (g ^ p) = g ^ p) ∧ (∀ η, Q (extD K η) = 0) ∧ ∀ T : ℕ → AddSubgroup (abelian₂ K), (∀ q, ∀ η ∈ T q, extD K η ∈ T (q + 1)) → (∀ i θ, IsEulerContraction x i θ → (∀ q, ∀ η ∈ T (q + 1), θ η ∈ T q) ∧ ∀ η ∈ T 0, θ η = 0) → (∀ q, ∀ η ∈ T (q + 1), h η ∈ T q) ∧ (∀ η ∈ T 0, h η = 0) ∧ ∀ q, ∀ η ∈ T q, Q η ∈ T q := by
  first | exact @_root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic | exact _root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic | (intros; apply _root_.GlobalTheory.CartierHomotopy.cartier_projector_homotopic <;> assumption)
