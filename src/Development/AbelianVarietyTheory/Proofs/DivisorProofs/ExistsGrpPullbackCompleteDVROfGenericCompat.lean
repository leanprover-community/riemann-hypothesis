module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpPullbackMapSemiAbelianNormalDomain
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
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

theorem GlobalTheory.UPoinc.exists_grpPullback_of_generic_compat : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ (G₁ : Over (Sp V)) [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ → ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (ξ : Sp V ⟶ S) (GK : Over (Sp (FractionRing V))) [GrpObj GK] (φ : GK.left ⟶ G₁.left) (γ : GK.left ⟶ G.left), IsGrpPullback GK G₁ (jK V) φ → IsGrpPullback GK G (jK V ≫ ξ) γ → ∃ β : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ β ∧ φ ≫ β = γ ∧ ∀ (f₁ : G₁ ⟶ G₁) (f : G ⟶ G) (fK : GK ⟶ GK), fK.left ≫ φ = φ ≫ f₁.left → fK.left ≫ γ = γ ≫ f.left → f₁.left ≫ β = β ≫ f.left := by
  intro V _ _ _ hV G₁ _ _ hG₁ S G _ _ hG ξ GK _ φ γ hφ hγ
  haveI : IsDiscreteValuationRing V := hV.1
  haveI : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  have hid : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := isGrpPullback_of_iso (Iso.refl G)
  obtain ⟨β, hβ, e⟩ := GlobalTheory.SemiAbDesc.exists_grpPullback_map V (𝟙 S) G G (𝟙 G.left) hG hid G₁ hG₁ ξ
    (jK V ≫ ξ) (Category.comp_id _) GK φ γ hφ hγ
  rw [Category.comp_id] at e
  refine ⟨β, hβ, e, fun f₁ f fK h₁ h₂ => ?_⟩
  have hj : GlobalTheory.IsGenericPointHom (S := Sp V) (ReciprocityTheory.ChartRestriction.G.Out.jK V) := .fractionField V (FractionRing V)
  obtain ⟨_, _⟩ := hj.quasiCompact_and_dominant
  obtain ⟨_, -⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G₁ hG₁
  obtain ⟨-, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  have : IsSchemeTheoreticallyDominant φ := .of_isPullback hφ.1.flip
  refine GlobalTheory.ExtUnique.hom_ext_of_dominant G.hom ?_ φ ?_
  · rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w, Category.assoc, Over.w, hβ.1.w]
  · rw [← Category.assoc, ← h₁, Category.assoc, e, h₂, ← Category.assoc, e]
