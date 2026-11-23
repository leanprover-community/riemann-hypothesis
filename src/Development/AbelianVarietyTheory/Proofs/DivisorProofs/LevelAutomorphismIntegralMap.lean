module

public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullbackFactor
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.LevelCarrying
import Development.AbelianVarietyTheory.Definitions.Divisors.CommGroupMulMulEqMulInvMulMulMul
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsCoprimeOfNatCast
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRightActFunPull
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnitaryWeightExponentVectorSignatureWeightMuZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GapGeSubKapBase
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Formalism.LocalToGlobal.ProjectiveLattices.ErealAddIInf
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EqvAct

theorem exists_isGrpPullback_extend : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (X' V : Scheme.{0}) [AlgebraicGeometry.IsNoetherian X'], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → ∀ (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ] (σ : V ⟶ V) (σ' : X' ⟶ X'), σ ≫ ℓ = ℓ ≫ σ' → ∀ (G' : Over X') [GrpObj G'], ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G' → ∀ (A : Over V) [GrpObj A] (κ : A.left ⟶ G'.left), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A G' ℓ κ → ∀ ν : A.left ⟶ A.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback A A σ ν → ∃ M : G'.left ⟶ G'.left, ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G' σ' M ∧ κ ≫ M = ν ≫ κ := by
  intro hext X' V _ hS ℓ _ _ σ σ' hσ G' _ hG A _ κ hκ ν hν
  have hGσ : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian ((Over.pullback σ').obj G') := IsSemiAbelian.pullback _ _ hG
  have h1 : IsGrpPullback A G' (ℓ ≫ σ') (ν ≫ κ) := (hν.comp hκ).congr hσ rfl
  have h2 := ReciprocityTheory.ChartRestriction.G.Chart.isGrpPullback_factor σ' ℓ h1
  have : IsMonHom (Iso.refl A).hom := inferInstanceAs (IsMonHom (𝟙 A))
  obtain ⟨e, ⟨he, he'⟩, -⟩ := hext.existsUnique_iso_of_isGrpPullback hS hG hGσ hκ h2 (Iso.refl A)
  haveI := he
  refine ⟨e.hom.left ≫ pullback.fst _ _, ?_, ?_⟩
  · exact ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G' σ')).congr (Category.id_comp _) rfl
  · rw [← Category.assoc, ← he']
    exact pullback.lift_fst _ _ _

theorem eq_of_comp_eq_of_isGrpPullback {X' V : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X']
    (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X') (ℓ : V ⟶ X') [IsOpenImmersion ℓ] [IsDominant ℓ]
    (G' : Over X') [GrpObj G'] (hG : ReciprocityTheory.ChartRestriction.G.Semi.IsSemiAbelian G') (A : Over V) [GrpObj A]
    (κ : A.left ⟶ G'.left) (hκ : IsGrpPullback A G' ℓ κ) (f g : G'.left ⟶ G'.left)
    (h : f ≫ G'.hom = g ≫ G'.hom) (hfg : κ ≫ f = κ ≫ g) : f = g := by
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS ℓ
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G' hG
  have : IsSchemeTheoreticallyDominant κ := .of_isPullback hκ.1.flip
  exact GlobalTheory.ExtUnique.hom_ext_of_dominant G'.hom h κ hfg

end GlobalTheory.EqvAct
