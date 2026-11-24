module

public import Mathlib.MeasureTheory.Group.Measure
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Examples

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal NNReal

noncomputable section

def SemidirectHaar.Statement (G T : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [Group T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T] : Prop :=
  ∀ (P H : Subgroup G), IsClosed (P : Set G) → IsClosed (H : Set G) → H ≤ P →
    ∀ (τ : T →* G) (β : P → T) (δ : T → ℝ≥0), Continuous τ → Continuous β → Continuous δ →
    (∀ t, τ t ∈ P) → (∀ t, ∀ x ∈ H, τ t * x * (τ t)⁻¹ ∈ H) → (∀ t, τ t ∈ H → t = 1) →
    (∀ p : P, (p : G) * (τ (β p))⁻¹ ∈ H) →
    ∀ (μ : Measure P) [μ.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
      (ρ : Measure T) [ρ.IsHaarMeasure],
    (∀ (t : T) (f : G → ℝ≥0∞), Measurable f →
      ∫⁻ x, f (τ t * x * (τ t)⁻¹) ∂ν = δ t * ∫⁻ x, f x ∂ν) →
    ∃ c : ℝ≥0, c ≠ 0 ∧ ∀ φ : G → ℝ≥0∞, Measurable φ →
      ∫⁻ p, φ p ∂μ = c * ∫⁻ t, δ t * ∫⁻ x : H, φ (x * τ t) ∂ν ∂ρ

section Inhabitants

open GaussianPlane

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
