module

public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
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

namespace ReciprocityTheory.L2DbarEstimates.I

open MeasureTheory Filter Topology
open scoped ENNReal

def HoloClosedNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (F : ℕ → M → ℂ) (f : M → ℂ),
    SmoothR n X.z ps → (∀ k, Holo n X.z (F k)) → Measurable f →
    Tendsto (fun k => wint n X.z (fun x => F k x - f x) ps) atTop (𝓝 0) →
    ∃ G : M → ℂ, Holo n X.z G ∧ f =ᵐ[vol n X.z] G

def EvalNeed (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : Prop :=
  ∀ (X : EtaleStein n M) (ps : M → ℝ) (x0 : M), SmoothR n X.z ps →
    ∃ C : ℝ, ∀ F : M → ℂ, Holo n X.z F →
      ENNReal.ofReal (‖F x0‖ ^ 2) ≤ ENNReal.ofReal C * wint n X.z F ps

end ReciprocityTheory.L2DbarEstimates.I
