module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslationIsometrySchwartzOperator
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

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem _root_.GlobalTheory.T.translation_isometry_schwartz_operator : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    (μ : MeasureTheory.Measure V) [μ.IsAddHaarMeasure] (T : SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ),
    (∀ (a : V) (f f' g g' : SchwartzMap V ℂ), (∀ x, f' x = f (x + a)) → (∀ x, g' x = g (x + a)) →
      ∫ x, T f' x * starRingEnd ℂ (T g' x) ∂μ = ∫ x, T f x * starRingEnd ℂ (T g x) ∂μ) →
    ∀ (χ ψ h : SchwartzMap V ℂ), HasCompactSupport (χ : V → ℂ) → ∀ M : ℕ, ∃ C : ℝ,
      ∀ (v : V) (k ψv : SchwartzMap V ℂ), (∀ x, k x = χ (x - v) * h x) → (∀ x, ψv x = ψ (x - v)) →
        ‖∫ x, T k x * starRingEnd ℂ (T ψv x) ∂μ‖ ≤ C * ((1 + ‖v‖) ^ M)⁻¹ := by
  first | exact @GlobalTheory.TransDecay.decay | exact GlobalTheory.TransDecay.decay | (intros; apply GlobalTheory.TransDecay.decay <;> assumption)
