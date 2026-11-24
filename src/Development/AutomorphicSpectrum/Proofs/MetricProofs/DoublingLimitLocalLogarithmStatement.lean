module

public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IterDifferentiableOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.DoublingLimitLocalLogarithm
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

open Set Filter Topology Metric

theorem _root_.GlobalTheory.T.doubling_limit_local_logarithm : ∀ {B V : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b₀ : B) (h : B × V → V) (ρ C : ℝ), 0 < ρ → 0 ≤ C → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖h (b, s)‖ ≤ 3 / 5 * ‖s‖) → (∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖(2 : ℂ) • h (b, s) - s‖ ≤ C * ‖s‖ ^ 2) → ∃ L : B × V → V, TendstoUniformlyOn (fun (k : ℕ) (p : B × V) => (2 : ℂ) ^ k • GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.iter h k p) L atTop (ball b₀ ρ ×ˢ ball (0 : V) ρ) ∧ ∀ b ∈ ball b₀ ρ, ∀ s ∈ ball (0 : V) ρ, ‖L (b, s) - s‖ ≤ 4 * C * ‖s‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | exact GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.LocalLog.koenigs_limit <;> assumption)
