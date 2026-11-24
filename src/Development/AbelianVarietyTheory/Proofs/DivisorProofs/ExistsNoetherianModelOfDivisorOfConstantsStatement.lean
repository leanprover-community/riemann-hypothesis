module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNoetherianModelOfDivisorOfConstants
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

open IsLocalRing Polynomial

theorem _root_.GlobalTheory.T.exists_noetherian_model_of_divisor_of_constants : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra T E]
      [IsScalarTower T (Polynomial T) E] [Algebra.Etale (Polynomial T) E]
      (Q : Ideal E) [Q.IsPrime],
      Q.comap (algebraMap (Polynomial T) E) = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (j : Localization.AtPrime Q →+* O),
      j.comp (algebraMap (Polynomial T) (Localization.AtPrime Q)) = algebraMap (Polynomial T) O →
    ∀ (b₁ c₁ : Localization.AtPrime Q) (s : T), s ≠ 0 →
      b₁ * c₁ = algebraMap T (Localization.AtPrime Q) s →
    ∃ (A : Type) (_ : CommRing A) (_ : IsDomain A) (_ : IsLocalRing A) (_ : IsNoetherianRing A)
      (_ : IsIntegrallyClosed A) (_ : Algebra.EssFiniteType ℤ A) (i : A →+* T),
      Function.Injective i ∧ IsLocalHom i ∧
      ∃ (EA : Type) (_ : CommRing EA) (_ : Algebra (Polynomial A) EA) (_ : Algebra A EA)
        (_ : IsScalarTower A (Polynomial A) EA) (_ : Algebra.Etale (Polynomial A) EA)
        (QA : Ideal EA) (_ : QA.IsPrime),
        QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A ∧
      ∃ (jA : Localization.AtPrime QA →+* O),
        jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
          (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) ∧
      ∃ (bA cA : Localization.AtPrime QA) (sA : A), sA ≠ 0 ∧ i sA = s ∧
        bA * cA = algebraMap A (Localization.AtPrime QA) sA ∧ jA bA = j b₁ := by
  first | (exact @GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (exact GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq) | (intros; apply GlobalTheory.VertUnitsNoeth.exists_noetherian_model_of_mul_eq  <;> assumption)
