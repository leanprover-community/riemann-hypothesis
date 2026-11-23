module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralFoldViaLintegralFormula
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

theorem _root_.GlobalTheory.T.integral_fold_via_lintegral_formula : ∀ {α Y Z : Type} [MeasurableSpace α] [MeasurableSpace Y] [MeasurableSpace Z] (μ : Measure α) (Fs : Set α) (ν : Measure Y) (m : Measure Z) (S : Set Z), m S < ⊤ → ∀ (Φ : Y → Z → α), Measurable (Function.uncurry Φ) → ∀ (c : ℝ), 0 ≤ c → ∀ (P : (α → ENNReal) → Prop), (∀ F : α → ENNReal, Measurable F → P F → ∫⁻ x in Fs, F x ∂μ = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s in S, F (Φ y s) ∂m ∂ν) → ∀ (G : α → ℂ), Measurable G → (∀ φ : ℂ → ENNReal, φ 0 = 0 → P (fun x => φ (G x))) → ∫⁻ y, ∫⁻ s in S, ‖G (Φ y s)‖ₑ ∂m ∂ν < ⊤ → IntegrableOn G Fs μ ∧ ∫ x in Fs, G x ∂μ = (c : ℂ) * ∫ y, ∫ s in S, G (Φ y s) ∂m ∂ν := by
  first | exact @GlobalTheory.FoldIntegral.fold | exact GlobalTheory.FoldIntegral.fold | (intros; apply GlobalTheory.FoldIntegral.fold <;> assumption)
