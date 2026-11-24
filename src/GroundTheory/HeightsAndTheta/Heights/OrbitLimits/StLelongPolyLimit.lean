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

noncomputable section

namespace GroundTheory.Heights₂.Heights.Targets

open MvPolynomial Filter Topology Matrix
open GroundTheory.Heights₂.Heights (varInt SmoothNear localMult)

def LelongPolyLimit.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : MvPolynomial (Fin n) ℂ) (f k : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → p ∉ J →
    SmoothNear (ComplexSets.zeroSet J) f → HasCompactSupport f →
    (∀ j, SmoothNear (ComplexSets.zeroSet J) (φ j)) →
    SmoothNear (ComplexSets.zeroSet J) k → (∀ x ∈ ComplexSets.zeroSet J, 0 < k x) →
      Tendsto (fun ε : ℝ =>
          varInt J (d + 1) f (vecCons (fun x => Real.log (‖eval x p‖ ^ 2 + ε * k x ^ 2) / 2) φ))
        (𝓝[>] 0)
        (𝓝 (∑ᶠ (W : Ideal (MvPolynomial (Fin n) ℂ)) (_ : W ∈ (J ⊔ Ideal.span {p}).minimalPrimes),
          (localMult (J ⊔ Ideal.span {p}) W : ℝ) * varInt W d f φ))

end GroundTheory.Heights₂.Heights.Targets
