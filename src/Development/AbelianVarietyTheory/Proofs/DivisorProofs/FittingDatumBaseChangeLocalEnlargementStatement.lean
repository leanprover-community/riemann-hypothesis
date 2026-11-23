module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FittingDatumBaseChangeLocalEnlargement
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

theorem _root_.GlobalTheory.T.fittingDatum_baseChange_localEnlargement : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∀ (A₁ : Type) [CommRing A₁] [IsDomain A₁] [IsLocalRing A₁] (f : A →+* A₁) (i₁ : A₁ →+* T),
    Function.Injective i₁ → IsLocalHom i₁ → i₁.comp f = i →
    ∃ (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A₁) EA') (_ : Algebra A₁ EA')
      (_ : IsScalarTower A₁ (Polynomial A₁) EA') (_ : Algebra.Etale (Polynomial A₁) EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A₁ i₁ EA' QA' jA' ψA' DA' actA' ∧
      (∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA'))
        (h : DA →+* DA'), ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) =
          (algebraMap (GlobalTheory.LocAcyc.GenFib A₁ (Localization.AtPrime QA')) DA').comp β) ∧
      ∃ γ : EA →+* EA',
        γ.comp (algebraMap (Polynomial A) EA) = (algebraMap (Polynomial A₁) EA').comp (Polynomial.mapRingHom f) ∧
        jA'.comp ((algebraMap EA' (Localization.AtPrime QA')).comp γ) = jA.comp (algebraMap EA (Localization.AtPrime QA)) ∧
        QA' = (maximalIdeal O).comap (jA'.comp (algebraMap EA' (Localization.AtPrime QA'))) ∧
        (∀ (Z : Type) [CommRing Z] (u : Polynomial A₁ →+* Z) (v : EA →+* Z),
          u.comp (Polynomial.mapRingHom f) = v.comp (algebraMap (Polynomial A) EA) →
          ∃ w : EA' →+* Z, w.comp (algebraMap (Polynomial A₁) EA') = u ∧ w.comp γ = v) ∧
        (∀ (Z : Type) [CommRing Z] (w₁ w₂ : EA' →+* Z),
          w₁.comp (algebraMap (Polynomial A₁) EA') = w₂.comp (algebraMap (Polynomial A₁) EA') →
          w₁.comp γ = w₂.comp γ → w₁ = w₂) := by
  first | (exact @GlobalTheory.EnlargeBaseChange.fits_baseChange) | (exact GlobalTheory.EnlargeBaseChange.fits_baseChange) | (intros; apply GlobalTheory.EnlargeBaseChange.fits_baseChange  <;> assumption)
