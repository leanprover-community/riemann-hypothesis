module

public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.Complex.Basic
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.AnalyticGroupLawBoundedCommutator
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

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.analytic_group_law_bounded_commutator : ∀ {B V W : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] (b₀ : B) (G : B × V × V → W) (R : ℝ), 0 < R → DifferentiableOn ℂ G (ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R) → (∀ p ∈ ball b₀ R ×ˢ ball (0 : V) R ×ˢ ball (0 : V) R, ‖G p‖ ≤ 1) → (∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, G (b, s, 0) = 0 ∧ G (b, 0, s) = 0) → ∀ b ∈ ball b₀ R, ∀ s ∈ ball (0 : V) R, ∀ t ∈ ball (0 : V) R, ‖G (b, s, t)‖ ≤ ‖s‖ * ‖t‖ / R ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | exact GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes | (intros; apply GlobalTheory.CompanionTheory.Metric.norm_le_of_vanishing_on_axes <;> assumption)
