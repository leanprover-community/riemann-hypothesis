module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFrameChart
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

theorem GlobalTheory.HodgeFrameGen.traitPullback_identification : ∀ {S' : Scheme.{0}} {G : Over S'} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ →
    ∀ {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left},
    IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α →
    ∀ {W : Type} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsIntegrallyClosed W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
    ∀ (χ' : Sp W ⟶ S'), spMap gam ≫ y = jK W ≫ χ' →
    ∃ (ρ' : ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)).left ⟶
        ((Over.pullback (spMap φ)).obj G₁).left) (ψ' : ((Over.pullback (spMap φ)).obj G₁).left ⟶ G.left),
      IsGrpPullback ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁))
        ((Over.pullback (spMap φ)).obj G₁) (jK W) ρ' ∧
      IsGrpPullback ((Over.pullback (spMap φ)).obj G₁) G χ' ψ' ∧
      ρ' ≫ ψ' = pullback.fst _ _ ≫ α ∧
      ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) := by
  intro S' G _ _ hG R _ _ G₁ _ _ hG₁ y α hα W _ _ _ _ φ gam hgam χ' hχ
  have hsq : spMap gam ≫ jK R = jK W ≫ spMap φ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact hgam r
  let A := (Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)
  let G₁W := (Over.pullback (spMap φ)).obj G₁
  have hA : IsGrpPullback A ((Over.pullback (jK R)).obj G₁) (spMap gam) (pullback.fst _ _) :=
    isGrpPullback_pullback _ _
  have hAG₁ : IsGrpPullback A G₁ (jK W ≫ spMap φ)
      ((pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R))) :=
    (hA.comp (isGrpPullback_pullback G₁ (jK R))).congr hsq rfl
  have hw : (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) ≫ G₁.hom = (A.hom ≫ jK W) ≫ spMap φ := by
    rw [hAG₁.1.w]; simp [Category.assoc]
  let ρ' : A.left ⟶ G₁W.left := pullback.lift (pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R)) (A.hom ≫ jK W) hw
  have hρfst : ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) :=
    pullback.lift_fst _ _ _
  have hρ : IsGrpPullback A G₁W (jK W) ρ' :=
    (isGrpPullback_pullback G₁ (spMap φ)).cancel (hAG₁.congr rfl hρfst.symm) (pullback.lift_snd _ _ _)
  have hG₁W : IsSemiAbelian G₁W := IsSemiAbelian.pullback (spMap φ) G₁ hG₁
  obtain ⟨ψ', hψ, hc⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map W y ((Over.pullback (jK R)).obj G₁) G α hG hα
    G₁W hG₁W χ' (spMap gam) hχ A ρ' (pullback.fst _ _) hρ hA
  exact ⟨ρ', ψ', hρ, hψ, hc, hρfst⟩
