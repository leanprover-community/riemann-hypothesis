module

public import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCubicalStructureDescendedLineBundleStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricOfGaloisPullbackUniformisationBundleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedGenericFibreDescendsGaloisStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLineBundleDescendsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalBundleOfSymmetricSemiAbelian
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.GaloisPackageDescent

theorem exists_cp : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), FinExt ρ → IsGal ρ → ∀ (D : DegData R (maximalIdeal R)) (D' : DegData R' (maximalIdeal R')) (hD : IsPullDeg ρ D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R'))) (G' : Over (Sp R')) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R') D' A' G'), ∀ (a : GalAct ρ hD U') (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (β : G'.left ⟶ G.left), IsSemiAbelian G → IsGrpPullback G' G (spMap ρ) β → (∀ σ, a.act σ ≫ β = β) → ∃ P : GlobalTheory.UU.CP G, LBIso U'.LG.L (P.L.L.pull β) := by
  intro R _ _ _ hR R' _ _ _ ρ hF hG D D' hD A' G' _ _ hS' U' a G _ _ β hS hβ hinv
  obtain ⟨L, hL, hLi⟩ := GlobalTheory.T.uniformisation_lineBundle_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  obtain ⟨rig, hrig⟩ := ReciprocityTheory.ChartRestriction.G.DVR.exists_gen_of_isLB_local (V := R) (L.pull (eSec G))
    (ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB L hL _ _)
  obtain ⟨c⟩ := GlobalTheory.T.exists_cubicalStructure_descendedLineBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  have hsym := GlobalTheory.T.isSymmetric_of_galoisPullback_uniformisationBundle R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv L hL hLi rig hrig
  obtain ⟨A, gen, κ, hgen, -, -⟩ := GlobalTheory.T.polarised_generic_fibre_descends_galois R hR R' ρ hF hG D D' hD A' G' hS' U' a G β hS hβ hinv
  have : IsNoetherianRing R := hR.1.1
  obtain ⟨hLaws, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨P, hP, -⟩ := GlobalTheory.UU.exists_cp_of_isSymmetric hLaws R A G hS gen hgen ⟨L, rig, hL, hrig⟩ c hsym
  refine ⟨P, ?_⟩
  rw [hP]
  exact hLi

end GlobalTheory.GaloisPackageDescent
