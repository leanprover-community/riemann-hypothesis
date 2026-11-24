module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveNormalisationLength
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def PuncturedCurveDiscInverse.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
    ∃ ε > 0, ∀ (φ : ℂ → Fin n → ℂ) (σ₀ : ℂ) (δ : ℝ), 0 < δ →
      DifferentiableOn ℂ φ (Metric.ball σ₀ δ) → Set.InjOn φ (Metric.ball σ₀ δ) →
      Set.MapsTo φ (Metric.ball σ₀ δ) (zeroSet I) → φ σ₀ ∈ Metric.ball q ε → φ σ₀ ≠ q →
      ∃ U : Set (Fin n → ℂ), IsOpen U ∧ φ σ₀ ∈ U ∧ ∃ ψ : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ ψ U ∧
        ∀ z ∈ zeroSet I ∩ U, ∃ σ ∈ Metric.ball σ₀ δ, φ σ = z ∧ ψ z = σ

end

end GroundTheory.Heights₂.Heights
