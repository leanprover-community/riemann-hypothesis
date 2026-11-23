module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannSumOfOneSidedIncrements
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

open Filter Topology

theorem _root_.GlobalTheory.T.tendsto_sub_of_one_sided_increment_bound_derivative : ∀ (s : Polynomial ℝ) (ℓ : ℚ → ℕ → ℝ), (∀ t t' : ℚ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ℓ t m - ℓ t' m ≤ ((t' : ℝ) - t) * s.derivative.eval (t : ℝ) + ε) → Tendsto (fun m => ℓ 0 m - ℓ 1 m) atTop (𝓝 (s.eval 1 - s.eval 0)) := by
  first | exact @GlobalTheory.riemann_sum_of_one_sided_increments | exact GlobalTheory.riemann_sum_of_one_sided_increments | (intros; apply GlobalTheory.riemann_sum_of_one_sided_increments <;> assumption)
