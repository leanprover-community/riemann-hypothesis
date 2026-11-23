module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffCompactAverageOfClosedPartials
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

open MeasureTheory
open scoped ContDiff


theorem _root_.GlobalTheory.T.contDiff_compactAverage_of_closed_partials : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  first | exact @GlobalTheory.AvgSmooth.main | exact GlobalTheory.AvgSmooth.main | (intros; apply GlobalTheory.AvgSmooth.main <;> assumption)
