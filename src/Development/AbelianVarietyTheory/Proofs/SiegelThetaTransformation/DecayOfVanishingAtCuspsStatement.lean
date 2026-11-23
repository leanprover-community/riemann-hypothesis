module

public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DecayOfVanishingAtCusps
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

theorem _root_.GlobalTheory.T.decay_of_vanishing_at_cusps' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ → ∀ (N R : ℕ) (δ s : ℝ), 0 < N → 0 < R → 0 < δ → 0 ≤ s → ∃ C : ℝ, ∀ (f : CM Ψ N N → ℂ) (B : ℝ), DifferentiableOn ℂ (fun Z : CF Ψ N N => f Z) {Z | (Z : CM Ψ N N) ∈ Hn Ψ N} → (∀ y : Matrix (Fin N) (Fin N) E, IntM y → ccT y = y → ∀ Z ∈ Hn Ψ N, f (fun τ => Z τ + ((R : E) • y).map τ.1) = f Z) → (∀ Z ∈ HnGe Ψ N (δ / 4), ‖f Z‖ ≤ B) → (∀ v : Fin N → E, v ≠ 0 → ∀ Z ∈ Hn Ψ N, Tendsto (fun t : ℝ => f (pushZ Ψ Z v t)) atTop (𝓝 0)) → ∀ Z ∈ HnGe Ψ N δ, ‖f Z‖ * detIm Z ^ s ≤ C * B := by
  first | exact @GlobalTheory.SW.decay_of_vanishing_at_cusps | exact GlobalTheory.SW.decay_of_vanishing_at_cusps | (intros; apply GlobalTheory.SW.decay_of_vanishing_at_cusps <;> assumption)
