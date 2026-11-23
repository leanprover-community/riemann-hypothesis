module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ChartMeasApplyOfSubset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlueMeasUnivNeTopOfCompact
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal

theorem _root_.GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] {n : ℕ} {ι : Type} (e : ι → OpenPartialHomeomorph M (V n)), (∀ y, ∃ i, y ∈ (e i).source) → (∀ i j, DifferentiableOn ℂ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)) → ∀ (r : ι → V n → ℝ), (∀ i, ContinuousOn (r i) (e i).target) → (∀ i j y, y ∈ (e i).source → y ∈ (e j).source → r i (e i y) = ‖GlobalTheory.ChartGlue.transDet (e i) (e j) y‖ ^ 2 * r j (e j y)) → GlobalTheory.ChartGlue.glueMeas e (fun i y => ENNReal.ofReal (r i (e i y))) univ ≠ ∞ := by
  exact @GlobalTheory.glueMeas_univ_ne_top_of_compact
