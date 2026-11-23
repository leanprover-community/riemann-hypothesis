module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteOverBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclicTorsorEtale
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleAtPrimeOfRegularOfIsIntegrallyClosedInStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInClosureLocalizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularHeightOneLocalization
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Mathlib.Algebra.AffineMonoid.UniqueSums
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
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Polynomial.IsIntegral
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime],
    IsDomain (Localization.AtPrime QA) ∧ IsIntegrallyClosed (Localization.AtPrime QA) ∧
      IsNoetherianRing (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  refine ⟨hd, hn, inferInstance, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_comap_height_le_one : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA htors hyp P _ hP
  obtain ⟨hdom, hic, hnoeth, hinj⟩ :=
    atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective A EA QA
  haveI := GlobalTheory.T.cyclic_torsor_etale _ DA q actA htors
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htors.1
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  haveI := GlobalTheory.T.closure_finite_over_base A (Localization.AtPrime QA) hinj DA
  exact GlobalTheory.T.etale_atPrime_of_regular_of_isIntegrallyClosedIn (Localization.AtPrime QA)
    (GlobalTheory.KeyOriginNoeth.closure A (Localization.AtPrime QA) DA)
    (GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective A (Localization.AtPrime QA) hinj DA) P (GlobalTheory.T.regular_height_one_localization A EA QA P hP)
    (fun P' _ _ hh => hyp P' hh)

end GlobalTheory.KeyOriginEnlarge
