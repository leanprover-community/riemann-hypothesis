module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.SepticCharacterInjective
public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TxCosetCriterion
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

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

theorem _root_.GlobalTheory.T.tx_coset_norm_one_and_ne_zero : ∀ (C : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CompleteSpace C] [IsAlgClosed C] (N : NumD C) (q : QuadraticMap ℤ N.X ℝ), N.Int q → ∀ n g : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n g → ∀ j : ℕ, 1 ≤ j → (∀ p : N.QT ((n ^ j) ^ 2), ‖N.tx (n ^ j) p‖ ≤ 1 ∧ (‖N.tx (n ^ j) p‖ = 1 → ∃ z, p.1.1.toAdd = n ^ j • z)) ∧ (∀ p : N.QT ((n ^ j) ^ 2), p.1.1 = 1 → ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ ‖N.tx (n ^ j) (p * h)‖ = 1) ∧ ∀ p : N.QT ((n ^ j) ^ 2), ∃ h : N.QT ((n ^ j) ^ 2), h.1.1 = 1 ∧ h.1.2 ^ n ^ (j + 1) = 1 ∧ N.tx (n ^ j) (p * h) ≠ 0 := by
  first | exact @GlobalTheory.tx_coset_criterion | exact GlobalTheory.tx_coset_criterion | (intros; apply GlobalTheory.tx_coset_criterion <;> assumption)
