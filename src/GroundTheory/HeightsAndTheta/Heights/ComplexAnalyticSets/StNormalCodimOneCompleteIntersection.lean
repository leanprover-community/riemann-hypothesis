module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.KrullDimension.Basic
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

open MvPolynomial

noncomputable section

def NormalCodimOneCompleteIntersection.Statement : Prop :=
  ∀ (σ : Type) [Fintype σ] (P Q : Ideal (MvPolynomial σ ℂ)) (e : ℕ), P.IsPrime → Q.IsPrime → P ≤ Q →
    IsIntegrallyClosed (MvPolynomial σ ℂ ⧸ P) →
    ringKrullDim (MvPolynomial σ ℂ ⧸ P) = (e + 1 : ℕ) → ringKrullDim (MvPolynomial σ ℂ ⧸ Q) = (e : ℕ) →
      ∃ (c : ℕ) (f : Fin c → MvPolynomial σ ℂ) (h : MvPolynomial σ ℂ),
        c + (e + 1) = Fintype.card σ ∧ (∀ j, f j ∈ P) ∧ h ∉ Q ∧
          ∀ p ∈ P, ∃ k : ℕ, h ^ k * p ∈ Ideal.span (Set.range f)

end

end GroundTheory.Heights₂.Heights
