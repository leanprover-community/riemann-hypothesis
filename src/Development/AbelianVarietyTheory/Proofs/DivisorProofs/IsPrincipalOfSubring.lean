module

public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.SiegelFamilyZetaUnit
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerSymmetricAmpleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialDescendsFlatSurjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KGroupTrivialSpreadsFromDvrGenericPointStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionAlongBaseChangeOfPullbackStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelConditionIffE8BundleKGroupTrivialStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoetherianSubringPrimeContractionOrDvrStatement
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.OneArc
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KTrivOfKTrivNonemptyOpenNormalCharZero
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelFamilyZetaUnit GlobalTheory.SiegelTypings
open GlobalTheory.PrincSubring

noncomputable section
namespace GlobalTheory.PrincSubring

theorem isPrincipal_of_subring : ∀ (h : ℕ) (R : Type) [CommRing R] (R₁ : Subring R) [IsNoetherianRing R₁] (A : Over (Sp R)) [GrpObj A] (P : LB (A ⊗ A).left) (A₁ : Over (Sp R₁)) [GrpObj A₁] (P₁ : LB (A₁ ⊗ A₁).left) (φ : A.left ⟶ A₁.left) (φ₂ : (A ⊗ A).left ⟶ (A₁ ⊗ A₁).left), IsSymmetricPair h A₁ P₁ → Out.RelAmple A₁ (diagPull A₁ P₁) → IsGrpPullback A A₁ (spMap R₁.subtype) φ → IsSquare φ φ₂ → LBIso P (P₁.pull φ₂) → IsPrincipal A P → IsPrincipal A₁ P₁ := by
  intro h R _ R₁ _ A _ P A₁ _ P₁ φ φ₂ hS hamp hpb hsq hiso hpr
  haveI : IsAbelianScheme A₁ := hS.1
  haveI : IsCommMonObj A₁ := IsAbelianScheme.comm
  obtain ⟨hG, hL, hLa, hrig, hsym⟩ := GlobalTheory.T.eighth_power_symmetric_ample h A₁ P₁ hS hamp
  have hf : KerAlong A₁ P₁ (spMap R₁.subtype) := GlobalTheory.T.kernel_condition_along_baseChange_of_pullback _ A P A₁ P₁ φ φ₂ hS.2.2.1 hpb hsq hiso hpr.2
  have hfT := (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp _).1 hf
  have hK : Out.KTriv (Out.powObj A₁ 8) (powLB A₁ P₁) := by
    refine GlobalTheory.KTrivSpread.kTriv_of_primes GlobalTheory.abelianSchemeLaws_all.1.globalFns R₁ _ hG _ hL hLa fun p => ?_
    rcases GlobalTheory.T.noetherian_subring_prime_contraction_or_dvr R R₁ p with hp | ⟨Q, k, _, i, j, V, _, _, _, ρ, e, h1, h2, hp⟩
    · exact ⟨R, inferInstance, R₁.subtype, hp, hfT⟩
    · refine ⟨V, inferInstance, ρ, hp, ?_⟩
      refine GlobalTheory.T.kGroup_trivial_spreads_from_dvr_generic_point _ _ hG hL hLa hrig hsym V (spMap ρ) ?_
      have t1 := hfT.comp (spMap (algebraMap R Q.asIdeal.ResidueField))
      have e1 : spMap (algebraMap R Q.asIdeal.ResidueField) ≫ spMap R₁.subtype = spMap j ≫ spMap i := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h1]
      rw [e1] at t1
      have t2 := (GlobalTheory.T.kGroup_trivial_descends_flat_surjective _ _ (spMap i) (spMap j) hL t1).comp (spMap e)
      have e2 : spMap e ≫ spMap i = spMap (algebraMap V (FractionRing V)) ≫ spMap ρ := by
        rw [← Geo.Tor.spMap_comp, ← Geo.Tor.spMap_comp, h2]
      rwa [e2] at t2
  have hT : GlobalTheory.KTrivSpread.TrivAlong (Out.powObj A₁ 8) (powLB A₁ P₁) (𝟙 _) :=
    fun T a ha x hx => GlobalTheory.UU.kTriv_iff_forall.1 hK T x hx
  exact ⟨hamp, fun T x hx => (GlobalTheory.T.kernel_condition_iff_e8Bundle_kGroup_trivial h A₁ P₁ hS hamp (𝟙 _)).2 hT T T.hom (Category.comp_id _) x hx⟩

end GlobalTheory.PrincSubring
