module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Tactic.ToDual
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NumericalConditionsTheoremTLargePrime
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
import Mathlib.RingTheory.PowerSeries.Basic

@[expose] public section

open scoped PowerSeries Pointwise

theorem _root_.GlobalTheory.T.numerical_conditions_theorem_T_large_prime : ∀ (l H N η r : ℕ), 2 ≤ N → 1 ≤ η → η < H → 4 * r ≤ N ^ 2 → 40 * (H * N ^ 2 + N ^ 3) < l → 2 * (H + η + 2 * (N - 1) * r + 1) + 2 < l ∧ 10 * H + 2 ≤ l ∧ 14 * H + (N + 2) * η < l ∧ 8 * H + 1 < l ∧ 4 * η * r + 4 < l ∧ (r + 2) * η < l + 1 := by
  first | exact @GlobalTheory.numerical_bounds_of_forty_mul_lt | exact GlobalTheory.numerical_bounds_of_forty_mul_lt | (intros; apply GlobalTheory.numerical_bounds_of_forty_mul_lt <;> assumption)
