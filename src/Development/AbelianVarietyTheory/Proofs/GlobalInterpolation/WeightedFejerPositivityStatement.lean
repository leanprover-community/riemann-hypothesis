module

public import Mathlib.Analysis.Complex.Trigonometric
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeightedFejerPositivity
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
import Mathlib.NumberTheory.DirichletCharacter.Basic

@[expose] public section

open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology

theorem _root_.GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound : ∀ (J : ℕ) (θ : ℝ), (∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (w ^ j).re) ∧ (J : ℝ) / 4 - 3 / 4 ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) * (Complex.exp (θ * I) ^ j).re := by
  first | exact @GlobalTheory.weighted_fejer_positivity | exact GlobalTheory.weighted_fejer_positivity | (intros; apply GlobalTheory.weighted_fejer_positivity <;> assumption)
