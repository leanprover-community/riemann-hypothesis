module

public import Formalism.LocalRingCardinality.DataParams₂
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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

open Formalism.BasicNotions Formalism.MainNotions

theorem _root_.GlobalTheory.T.scale_polynomial_quantities_comparison : ∀ eps c κ : ℝ, 0 < eps → 0 < κ → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → s.x ^ c ≤ Real.exp (s.x ^ (s.eps / 8)) ∧ s.x ^ c ≤ s.X' ^ κ ∧ s.x ^ c * s.X' ≤ s.b ^ κ ∧ s.b' * s.x ^ c ≤ s.b ∧ s.b ^ (1 - κ) * s.x ^ c ≤ s.b' ∧ (∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ s.x ^ (3 : ℝ) → s.b ^ (1 - κ) * s.x ^ c ≤ s.w'' n ∧ s.w'' n ≤ s.b' ∧ s.X'' n = s.x * n * s.X') ∧ Real.exp (c * s.x ^ (s.eps / 5) * Real.log s.x ^ 2) * s.x ^ c ≤ s.X' ^ κ := by
  first | exact @GlobalTheory.scale_poly_comparison | exact GlobalTheory.scale_poly_comparison | (intros; apply GlobalTheory.scale_poly_comparison <;> assumption)
