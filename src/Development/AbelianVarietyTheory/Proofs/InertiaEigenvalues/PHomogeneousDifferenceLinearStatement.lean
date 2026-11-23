module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PHomogeneousDifferenceLinear
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
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss

@[expose] public section

open GlobalTheory.PMon.Gauss
open scoped Formalism.Per

theorem _root_.GlobalTheory.T.exists_int_sub_mul_eq_int_mul_of_homogeneous : ∀ (p h s m : ℕ), 2 ≤ p → s < h → 1 ≤ m → ∀ A B : ℝ → ℝ, ConcaveOn ℝ (Set.Ioc 0 1) A → ConcaveOn ℝ (Set.Ioc 0 1) B → ContinuousOn A (Set.Ioc 0 1) → ContinuousOn B (Set.Ioc 0 1) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), A t = A r + k * (t - r)) → (∀ r ∈ Set.Ioo (0 : ℝ) 1, ∃ (k : ℤ) (δ : ℝ), 0 < δ ∧ r + δ ≤ 1 ∧ ∀ t ∈ Set.Icc r (r + δ), B t = B r + k * (t - r)) → (∀ r ∈ Set.Ioc (0 : ℝ) 1, (p : ℝ) ^ h * B (r / (p : ℝ) ^ h) = B r + s * r) → (∀ r ∈ Set.Ioc (0 : ℝ) (1 / p), A (p * r) - m * B (p * r) = p * (A r - m * B r)) → ∃ n : ℤ, ∀ r ∈ Set.Ioc (0 : ℝ) 1, A r - m * B r = n * r := by
  first | exact @GlobalTheory.PHomCalc.p_homogeneous_difference_linear | exact GlobalTheory.PHomCalc.p_homogeneous_difference_linear | (intros; apply GlobalTheory.PHomCalc.p_homogeneous_difference_linear <;> assumption)
