module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrable
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

open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M

theorem _root_.GlobalTheory.T.tail_log_bound_local_integrable : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ), (∀ i, IsPotential A (Φ i)) → (∀ x ∈ Yo, 1 ≤ r x) → (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)), S ⊆ (A.chart j).target → IsCompact S → ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧ ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤ CE * Real.log R₀ ^ (e + 1) / R₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | exact GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart <;> assumption)
