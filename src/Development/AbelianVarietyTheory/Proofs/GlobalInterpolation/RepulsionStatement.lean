module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Repulsion
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

theorem _root_.GlobalTheory.T.one_sub_re_ge_of_exceptional_zero_repulsion : ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ₁ χ : DirichletCharacter ℂ q) (β L : ℝ) (ρ : ℂ), χ₁ ≠ 1 → χ₁ ^ 2 = 1 → β < 1 → 1 / 2 ≤ β → LFunction χ₁ β = 0 → LFunction χ ρ = 0 → 1 / 2 ≤ ρ.re → ρ.re < 1 → (χ ≠ χ₁ ∨ ρ ≠ β ∨ 2 ≤ ord χ₁ β) → Real.log (q * (|ρ.im| + 2)) ≤ L → c * Real.log (c / ((1 - β) * L)) / L ≤ 1 - ρ.re := by
  first | exact @GlobalTheory.Lin.Repulsion.repulsion | exact GlobalTheory.Lin.Repulsion.repulsion | (intros; apply GlobalTheory.Lin.Repulsion.repulsion <;> assumption)
