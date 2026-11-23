module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralKernelLiftsFubiniSigmaFinite
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate ENNReal

theorem _root_.GlobalTheory.T.integral_kernel_lifts_fubini_sigmaFinite : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by
  first | exact @GlobalTheory.AbsFubini.abstract_fubini_two_lifts | exact GlobalTheory.AbsFubini.abstract_fubini_two_lifts | (intros; apply GlobalTheory.AbsFubini.abstract_fubini_two_lifts <;> assumption)
