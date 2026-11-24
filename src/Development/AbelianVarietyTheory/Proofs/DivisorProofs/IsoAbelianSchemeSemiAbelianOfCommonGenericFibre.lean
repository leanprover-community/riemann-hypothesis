module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjectiveModel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommonBaseChangePolarizedAbelianSchemeOfGe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianHomExtensionHolds
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Definitions.Divisors.SharpOverIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open GlobalTheory
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc

theorem iso_of_common_generic_fibre : ∀ (O : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsIntegrallyClosed O] (A G : Over (Sp O)) [GrpObj A] [GrpObj G] [IsCommMonObj G], IsAbelianScheme A → IsSemiAbelian G → ∀ (K : Type) [Field K] [Algebra O K] [IsFractionRing O K] (B : Over (Sp K)) [GrpObj B] (a : B.left ⟶ A.left) (g : B.left ⟶ G.left), IsGrpPullback B A (spMap (algebraMap O K)) a → IsGrpPullback B G (spMap (algebraMap O K)) g → ∃ i : A ≅ G, IsMonHom i.hom ∧ a ≫ i.hom.left = g ∧ (∀ (L : LB A.left) (L' : LB G.left), L.IsLB → L'.IsLB → LBIso (L.pull a) (L'.pull g) → LBIso L (L'.pull i.hom.left)) ∧ ∀ (e : A ⟶ A) (f : G ⟶ G) (eB : B ⟶ B), eB.left ≫ a = a ≫ e.left → eB.left ≫ g = g ≫ f.left → e ≫ i.hom = i.hom ≫ f := by
  intro O _ _ _ _ _ A G _ _ _ hA hG K _ _ _ B _ a g ha hg
  have hS := GlobalTheory.Published.SemiAbelianHomExtension.isNormalScheme_spec O
  have hj := GlobalTheory.IsGenericPointHom.fractionField O K
  have hA' := GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA
  obtain ⟨E, ⟨hE, hEa⟩, -⟩ :=
    GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso_of_extensions hS hj hA' hG ha hg
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian A hA'
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  refine ⟨E, hE, hEa, ?_, ?_⟩
  · intro L L' hL hL' h
    refine GlobalTheory.Poinc.Extend.lbIso_of_generic A hA ha.1 hL (pull_isLB hL' _) ?_
    exact LBIso.trans (pull_isLB hL _) (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) h
      (GlobalTheory.GenSpread.lbIso_pull_pull hL' a hEa.symm)
  · intro e f eB he hf
    refine GlobalTheory.ExtUnique.over_hom_ext_of_isPullback ha.1 ?_
    rw [Over.comp_left, Over.comp_left, ← Category.assoc a e.left, ← he, Category.assoc, hEa,
      reassoc_of% hEa]
    exact hf

end GlobalTheory.UPoinc

end
