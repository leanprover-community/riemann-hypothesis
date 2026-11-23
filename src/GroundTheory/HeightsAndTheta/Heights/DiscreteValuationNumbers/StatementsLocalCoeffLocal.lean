module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree
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

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

universe u

section Lemmas

def LocCycleSpanMul.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x y : A), x ≠ 0 → y ≠ 0 →
    ∀ W : Ideal A, locCycle (Ideal.span {x * y}) W =
      locCycle (Ideal.span {x}) W + locCycle (Ideal.span {y}) W

def LocCyclePos.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] (J W : Ideal R), W ∈ J.minimalPrimes →
    0 < locCycle J W

def MinimalPrimesSpanSingleton.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] (x : A), x ≠ 0 →
    ∀ W : Ideal A, W ∈ (Ideal.span {x}).minimalPrimes ↔ W.IsPrime ∧ W.height = 1 ∧ x ∈ W

def LocalDomainDimTwo.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    (∃ Q : Ideal A, Q.IsPrime ∧ ⊥ < Q ∧ Q < IsLocalRing.maximalIdeal A) →
    ringKrullDim A = 2 ∧ (IsLocalRing.maximalIdeal A).height = 2 ∧
      ∀ Q : Ideal A, Q.IsPrime → ⊥ < Q → Q < IsLocalRing.maximalIdeal A → Q.height = 1

def DimTwoSumReading.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    ringKrullDim A = 2 → ∀ a b : A, a ≠ 0 →
    (∀ p : Ideal A, p.IsPrime → p.height = 1 → a ∈ p → b ∉ p) →
    ∃ n : ℕ, ∑ᶠ W : Ideal A, locCycle (Ideal.span {a}) W *
        locCycle (W ⊔ Ideal.span {b}) (IsLocalRing.maximalIdeal A) = n ∧
      ∑ᶠ (p : PrimeSpectrum A) (_ : p.asIdeal.height = 1 ∧ a ∈ p.asIdeal), ordLoc p a * ordMod p b = n

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
