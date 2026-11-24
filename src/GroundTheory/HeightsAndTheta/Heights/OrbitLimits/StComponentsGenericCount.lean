module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
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

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets

def ComponentsGenericCount.Statement : Prop :=
  ∀ (n d : ℕ) (F : Finset (Ideal (MvPolynomial (Fin n) ℂ))) (A : Matrix (Fin d) (Fin n) ℂ),
    (∀ J ∈ F, J.IsPrime ∧ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d : ℕ) ∧ IsFiniteProjection J A) →
    (∀ J ∈ F, ∀ J' ∈ F, J ≤ J' → J = J') →
      (∀ y : Fin d → ℂ,
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard ≤ ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞)) ∧
      ∃ Δ : MvPolynomial (Fin d) ℂ, Δ ≠ 0 ∧ ∀ y : Fin d → ℂ, eval y Δ ≠ 0 →
        {x | (∃ J ∈ F, x ∈ zeroSet J) ∧ A *ᵥ x = y}.encard = ((∑ J ∈ F, projDegree J A : ℕ) : ℕ∞) ∧
        ∀ x, (∃ J ∈ F, x ∈ zeroSet J) → A *ᵥ x = y →
          ∃ (U : Set (Fin d → ℂ)) (g : (Fin d → ℂ) → Fin n → ℂ), IsOpen U ∧ y ∈ U ∧
            DifferentiableOn ℂ g U ∧ g y = x ∧ ∀ y' ∈ U, A *ᵥ g y' = y' ∧ ∃ J ∈ F, g y' ∈ zeroSet J

end GroundTheory.Heights₂.Heights
