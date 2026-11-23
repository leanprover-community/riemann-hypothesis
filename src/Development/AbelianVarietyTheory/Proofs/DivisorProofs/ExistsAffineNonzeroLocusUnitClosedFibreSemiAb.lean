module

public import Mathlib.RingTheory.RegularLocalRing.Defs
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsHasProjectiveDimensionLEOfResidueField
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsPrincipalMapAwayOfHasProjectiveDimensionLE
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfIsDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNonzeroLocusEqOfIsAffineOpen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.AlgebraicGeometry.QuasiAffine
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
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbAffineUnit

theorem exists_affine_nonzeroLocus_unit : ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G → IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∃ (M₀ : LB G.left) (s₀ : M₀.Sec), M₀.IsLB ∧ IsAffineOpen (nonzeroLocus s₀) ∧ ∃ y₀ ∈ nonzeroLocus s₀, G.hom y₀ = closedPoint R := by
  intro R _ _ _ G _ hG _
  have := hG.smooth
  have := hG.separated
  have := hG.quasiCompact
  have hR : IsRegularRing R := GlobalTheory.isRegularRing_of_isRegularLocalRing R
  have : IsIntegral G.left := GlobalTheory.isIntegral_left_of_isSemiAbelian G
  have : IsLocallyNoetherian G.left := LocallyOfFiniteType.isLocallyNoetherian G.hom
  have : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  have : G.left.IsSeparated := ⟨by rw [← terminal.comp_from G.hom]; infer_instance⟩
  have hst : ∀ x : G.left, UniqueFactorizationMonoid (G.left.presheaf.stalk x) := fun x =>
    have := ExtendRig.isRegularRing_stalk isRegularRing_of_smooth R G.hom x
    uniqueFactorizationMonoid_of_isRegularRing_of_isLocalRing exists_hasProjectiveDimensionLE_of_isRegularLocalRing
      isPrincipal_map_away_of_hasProjectiveDimensionLE _
  have he : (η[G]).left ≫ G.hom = 𝟙 _ := Over.w (η[G])
  set y₀ : G.left := (η[G]).left (closedPoint R) with hy₀
  have hy : G.hom y₀ = closedPoint R := by
    have h2 := Scheme.Hom.comp_apply (η[G]).left G.hom (closedPoint R : (𝟙_ (Over (Sp R))).left)
    rw [he] at h2
    exact h2.symm
  obtain ⟨W, hW, hyW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y₀) trivial
  obtain ⟨L, s, hL, hs⟩ := GlobalTheory.SS.exists_nonzeroLocus_eq_of_isAffineOpen G.left hst W hW ⟨_, hyW⟩
  exact ⟨L, s, hL, hs ▸ hW, y₀, hs ▸ hyW, hy⟩

end GlobalTheory.SemiAbAffineUnit
