module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointClosureFiniteEtaleStrictHenselianStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureFiniteEtaleOriginKeyLemmaEssFinitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StrictHenselisationEnlargeGoodAtOriginStatement
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
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open IsLocalRing Polynomial

namespace GlobalTheory.KeyOriginNoeth

theorem torsor_point_of_essFiniteType : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
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
  intro T O _ _ _ _ _ _ _ _ hT P _ φ hφ hsh hP q hq0 hqT A _ _ _ _ _ _ i hi hil hqA EA _ _ _ _ _ QA _ hQA jA hjA
    ψA hψA DA _ _ actA htor
  obtain ⟨A', _, _, _, _, _, _, EA', _, _, _, _, _, QA', _, hQ', hq', ρ', hρ1, hρ2, jA', ψA', hψ', DA', _, _,
    actA', htor', hgood', β, h, hβ1, hβ2⟩ :=
    GlobalTheory.T.strictHenselisation_enlarge_good_at_origin T O hT P φ hφ hsh hP q hq0 hqT A i hi hil hqA EA QA hQA jA hjA ψA hψA DA actA htor
  have hce := GlobalTheory.T.integralClosure_finiteEtale_originKeyLemma_essFiniteType A' EA' QA' hQ' ρ' hρ1 hρ2 q hq0 hq' DA' actA' htor' hgood'
  haveI : HenselianLocalRing O := hsh.1
  haveI : IsSepClosed (ResidueField O) := hsh.2.1
  obtain ⟨σ', hσ'⟩ := GlobalTheory.T.exists_point_closureFiniteEtale_strictHenselian A' (Localization.AtPrime QA') O (GlobalTheory.LocAcyc.GenFib T O) jA'
    (algebraMap O (GlobalTheory.LocAcyc.GenFib T O)) ψA' hψ' DA' htor'.1 hce
  refine ⟨σ'.comp h, ?_⟩
  rw [RingHom.comp_assoc, hβ2, ← RingHom.comp_assoc, hσ', hβ1]

end GlobalTheory.KeyOriginNoeth
