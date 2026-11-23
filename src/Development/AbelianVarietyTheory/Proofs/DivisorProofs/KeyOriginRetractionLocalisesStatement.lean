module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeyOriginRetractionLocalises
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

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.keyOrigin_retraction_localises : ∀ (T O A₁ EA₁ : Type) [CommRing T] [CommRing O] [IsLocalRing O] [Algebra T O] [Algebra (Polynomial T) O]
    [CommRing A₁] [IsLocalRing A₁] (i₁ : A₁ →+* T), IsLocalHom i₁ → IsLocalHom (algebraMap T O) →
    ∀ [CommRing EA₁] [Algebra (Polynomial A₁) EA₁] [Algebra A₁ EA₁]
      (QA₁ : Ideal EA₁) [QA₁.IsPrime] (jA₁ : Localization.AtPrime QA₁ →+* O) (ρ' : EA₁ →+* A₁),
    algebraMap (Polynomial T) O Polynomial.X ∈ maximalIdeal O →
    ρ'.comp (algebraMap A₁ EA₁) = RingHom.id A₁ →
    ρ' (algebraMap (Polynomial A₁) EA₁ Polynomial.X) = 0 →
    (∀ x : EA₁, algebraMap T O (i₁ (ρ' x)) - jA₁ (algebraMap EA₁ (Localization.AtPrime QA₁) x) ∈
      Ideal.span {algebraMap (Polynomial T) O Polynomial.X}) →
    (∀ x : EA₁, ρ' x = 0 → ∃ s ∉ QA₁, s * x ∈ Ideal.span {algebraMap (Polynomial A₁) EA₁ Polynomial.X}) →
    ∃ ρ₁ : Localization.AtPrime QA₁ →+* A₁,
      GlobalTheory.KeyOriginEnlarge.Retracts T O A₁ i₁ EA₁ QA₁ jA₁ ρ₁ ∧
      ρ₁.comp (algebraMap EA₁ (Localization.AtPrime QA₁)) = ρ' := by
  first | (exact @GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (exact GlobalTheory.KeyOriginEnlargeLoc.retract_localises) | (intros; apply GlobalTheory.KeyOriginEnlargeLoc.retract_localises  <;> assumption)
