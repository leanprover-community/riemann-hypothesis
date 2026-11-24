module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
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

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

def CutOffDominated.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (P : MvPolynomial (Fin d) ℂ) (χ : ℕ → (Fin n → ℂ) → ℝ) (f : (Fin n → ℂ) → ℝ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d → IsFiniteProjection J A → P ≠ 0 →
    (∀ k, Measurable (χ k)) → (∀ k x, χ k x ∈ Set.Icc (0 : ℝ) 1) →
    (∀ x ∈ zeroSet J, eval (A *ᵥ x) P ≠ 0 → Tendsto (fun k => χ k x) atTop (𝓝 1)) →
    ContinuousOn f (zeroSet J) → (∀ i, SmoothNear (zeroSet J) (ψ i)) →
    Integrable (chartAbsDens J A f ψ) →
      Tendsto (fun k => chartInt J A (fun x => χ k x * f x) ψ) atTop (𝓝 (chartInt J A f ψ))

end

end GroundTheory.Heights₂.Heights
