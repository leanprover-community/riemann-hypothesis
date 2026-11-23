module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StRegRadialWeight
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory
open scoped ContDiff

noncomputable section

def RadialPrimitive.Statement : Prop :=
  ∀ (e : ℕ) (a : ℝ → ℝ) (t₀ T : ℝ),
    ContDiff ℝ ∞ a → 0 < t₀ → (∀ t ∈ Set.Icc 0 t₀, a t = a 0) → (∀ t, T ≤ t → a t = 0) →
    (∫ τ in (0 : ℝ)..T, a τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 →
      ∃ Q : ℝ → ℝ, ContDiff ℝ ∞ Q ∧ (∃ R : ℝ, ∀ t, R ≤ t → Q t = 0) ∧
        deriv Q 0 = a 0 ∧ deriv (deriv Q) 0 = 0 ∧
        ∀ t, 0 < t →
          deriv Q t * t ^ (e + 1) = a t * t ^ (e + 1) - radialTransform (e + 1) a t ∧
            deriv (deriv Q) t * t ^ (e + 2) = ((e + 1 : ℕ) : ℝ) * radialTransform (e + 1) a t

end

end GroundTheory.Heights₂.Heights
