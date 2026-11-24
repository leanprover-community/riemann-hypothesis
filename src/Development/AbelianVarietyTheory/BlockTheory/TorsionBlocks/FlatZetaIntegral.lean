module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Set

namespace GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral

variable {X : Type} [MeasurableSpace X]

noncomputable def flatIntegrand (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) (x : X) : ℂ :=
  f x * ((a x : ℝ) : ℂ) ^ (s - s₀)

noncomputable def flatZeta (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s : ℂ) : ℂ :=
  ∫ x, flatIntegrand f a s₀ s x ∂μ

def ConvergesAbsLocUnifOn (μ : Measure X) (F : ℂ → X → ℂ) (D : Set ℂ) : Prop :=
  (∀ s ∈ D, Integrable (F s) μ) ∧
    ∀ s ∈ D, ∃ U ∈ nhdsWithin s D, ∃ g : X → ℝ, Integrable g μ ∧
      ∀ s' ∈ U, ∀ x, ‖F s' x‖ ≤ g x

def FlatZetaHolomorphic : Prop :=
  ∀ (X : Type) [MeasurableSpace X] (μ : Measure X) (f : X → ℂ) (a : X → ℝ) (s₀ s₁ : ℂ),
    Measurable a → (∀ x, 0 < a x) → (∀ x, a x ≤ 1) →
    Integrable (flatIntegrand f a s₀ s₁) μ →
      ConvergesAbsLocUnifOn μ (flatIntegrand f a s₀) {s | s₁.re ≤ s.re} ∧
      DifferentiableOn ℂ (flatZeta μ f a s₀) {s | s₁.re < s.re} ∧
      ContinuousOn (flatZeta μ f a s₀) {s | s₁.re ≤ s.re}


omit [MeasurableSpace X] in
theorem flatIntegrand_self (f : X → ℂ) (a : X → ℝ) (s₀ : ℂ) : flatIntegrand f a s₀ s₀ = f := by
  funext x
  simp [flatIntegrand]


omit [MeasurableSpace X] in
theorem norm_flatIntegrand (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by
  rw [flatIntegrand, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.sub_re]

end GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
