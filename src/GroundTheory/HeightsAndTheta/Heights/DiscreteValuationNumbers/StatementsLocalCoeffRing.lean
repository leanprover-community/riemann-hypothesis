module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.LocCycle
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

noncomputable section

universe u

section Defs

variable {R : Type*} [CommRing R]

abbrev localQuot (P U : Ideal R) [U.IsPrime] : Type _ :=
  Localization.AtPrime U ⧸ P.map (algebraMap R (Localization.AtPrime U))

def localQuotMap (P U : Ideal R) [U.IsPrime] : R →+* localQuot P U :=
  (Ideal.Quotient.mk _).comp (algebraMap R (Localization.AtPrime U))

end Defs

section Lemmas

def LocalQuotRing.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P.IsPrime → P ≤ U →
    IsDomain (localQuot P U) ∧ IsLocalRing (localQuot P U) ∧
      (∀ y : localQuot P U, IsUnit y ↔ y ∉ U.map (localQuotMap P U)) ∧
      ∀ x : R, localQuotMap P U x = 0 ↔ x ∈ P

def LocalQuotPrimes.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    (∀ W : Ideal R, W.IsPrime → P ≤ W → W ≤ U →
      (W.map (localQuotMap P U)).IsPrime ∧ (W.map (localQuotMap P U)).comap (localQuotMap P U) = W) ∧
    ∀ p : Ideal (localQuot P U), p.IsPrime →
      P ≤ p.comap (localQuotMap P U) ∧ p.comap (localQuotMap P U) ≤ U ∧
        (p.comap (localQuotMap P U)).map (localQuotMap P U) = p

def LocCycleLocalQuot.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (J W : Ideal R), P ≤ J → W.IsPrime → P ≤ W →
    W ≤ U → locCycle J W = locCycle (J.map (localQuotMap P U)) (W.map (localQuotMap P U))

def LocalQuotColon.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime] (f g : R),
    ((P ⊔ Ideal.span {f}).colon {g}).map (localQuotMap P U) =
      (Ideal.span {localQuotMap P U f}).colon {localQuotMap P U g}

def LocalQuotFinsum.Statement : Prop :=
  ∀ (R : Type u) [CommRing R] (P U : Ideal R) [U.IsPrime], P ≤ U →
    ∀ (F : Ideal R → ℤ) (F' : Ideal (localQuot P U) → ℤ),
      (∀ G, F G ≠ 0 → G.IsPrime ∧ P ≤ G ∧ G ≤ U) → (∀ p, F' p ≠ 0 → p.IsPrime) →
      (∀ G : Ideal R, G.IsPrime → P ≤ G → G ≤ U → F G = F' (G.map (localQuotMap P U))) →
      ∑ᶠ G, F G = ∑ᶠ p, F' p

def LocalCoeffLocal.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A],
    (∀ Q₁ Q₂ : Ideal A, Q₁.IsPrime → Q₂.IsPrime → ⊥ < Q₁ → Q₁ < Q₂ → Q₂ < IsLocalRing.maximalIdeal A →
      False) →
    ∀ f g s u v : A, f ≠ 0 → g ≠ 0 → s ≠ 0 → IsUnit u → u * f = v * g →
    (∀ W : Ideal A, locCycle (Ideal.span {s}) W ≠ 0 →
      locCycle (Ideal.span {f}) W = locCycle (Ideal.span {g}) W) →
    ∑ᶠ G, (locCycle (Ideal.span {f}) G - locCycle (Ideal.span {g}) G) *
        locCycle (G ⊔ Ideal.span {s}) (IsLocalRing.maximalIdeal A) =
      ∑ᶠ W, locCycle (Ideal.span {s}) W *
        locCycle (W ⊔ (Ideal.span {f}).colon {g}) (IsLocalRing.maximalIdeal A)

end Lemmas

section Examples

end Examples

end

end GroundTheory.Heights₂.Heights.NumbersDVR
