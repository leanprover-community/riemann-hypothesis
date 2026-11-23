module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorPointOverStrictHenselisationNoetherianNorm
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

theorem _root_.GlobalTheory.T.torsor_point_over_strictHenselisation_noetherianNormal : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Algebra.EssFiniteType ℤ A]
      (i : A →+* T), Function.Injective i → IsLocalHom i → IsUnit (q : A) →
    ∀ (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime],
      QA.comap (algebraMap (Polynomial A) EA) = GlobalTheory.KeyOriginCut.originIdeal A →
    ∀ (jA : Localization.AtPrime QA →+* O),
      jA.comp (algebraMap (Polynomial A) (Localization.AtPrime QA)) =
        (algebraMap (Polynomial T) O).comp (Polynomial.mapRingHom i) →
    ∀ (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O),
      ψA.comp (algebraMap (Localization.AtPrime QA) (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA))) =
        (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)).comp jA →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
      GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    ∃ σ : DA →+* GlobalTheory.LocAcyc.GenFib T O, σ.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = ψA := by
  first | (exact @GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (exact GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType) | (intros; apply GlobalTheory.KeyOriginNoeth.torsor_point_of_essFiniteType  <;> assumption)
