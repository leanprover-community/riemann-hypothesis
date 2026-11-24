module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.SecondCountableTopologyArchUnitary
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

@[expose] public section

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open MeasureTheory
open scoped ENNReal

noncomputable section

def UnfoldAlongSubgroup.Statement (G Y : Type*) [Group G] [MeasurableSpace G] [MeasurableSpace Y] :
    Prop :=
  ∀ (μ : Measure G) (H : Subgroup G) [MeasurableMul H] (ν : Measure H) [ν.IsMulLeftInvariant]
    [SFinite ν] (ρ : Measure Y) [SFinite ρ] (s : Y → G),
    Measurable (fun p : H × Y => (p.1 : G) * s p.2) →
    (∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ y, ∫⁻ x, f (x * s y) ∂ν ∂ρ) →
    ∀ (Γ : Subgroup G) [Countable Γ], Γ ≤ H →
    ∀ (FD : Set G) (FD₀ : Set H), IsFundamentalDomain Γ FD μ →
      IsFundamentalDomain (Γ.subgroupOf H) FD₀ ν →
    ∀ f : G → ℝ≥0∞, Measurable f → (∀ x : H, ∀ g, f (x * g) = f g) →
      ∫⁻ g in FD, f g ∂μ = ν FD₀ * ∫⁻ y, f (s y) ∂ρ

section Inhabitants

theorem measurableSingletonClass_cyclicTwo : MeasurableSingletonClass C2 :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

attribute [local instance] measurableSingletonClass_cyclicTwo

end Inhabitants

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
