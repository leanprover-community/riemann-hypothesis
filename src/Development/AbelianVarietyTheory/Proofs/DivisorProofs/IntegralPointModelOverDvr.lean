module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.MatchingNotVacuous
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible
public import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.Valuation.LocalSubring
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt
import ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint
import Mathlib.Tactic.Linter.Style
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame
import Mathlib.CategoryTheory.Monoidal.Opposite.Mon

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison, Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison", "h": "module\n\npublic import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalSystemBasesNonempty\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.Valuation.LocalSubring\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FnAlgClosedOfFixedPoints\nimport Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag\nimport Development.AbelianVarietyTheory.Definitions.Degenerations.MorAlgSt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap\nimport Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AuxiliaryInertOddPrime\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HomExtNormalSt\nimport ReciprocityTheory.AnalyticForms.RegularLocalRings.JacChartA\n\n"}
section -- clump:auto
@[expose] public section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TriplesAlong

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end GlobalTheory.TriplesAlong

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart\npublic import Formalism.LocalToGlobal.ProjectiveLattices.IsChartIff\npublic import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.MatchingNotVacuous\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.IsLatBasisHtLatIffSpanEq\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFrameExtensionExists\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartFlagBaseHolds\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralPointPullbackComparison\npublic import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModuliFiniteSurjectiveOverGenericFamily\nimport Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFlagModelBaseChangeIntegralFramedPoint\npublic import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SemiAbelianDvrExtensionsIsoCompatible\npublic import Formalism.LocalToGlobal.ProjectiveLattices.SatLeaves\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset\nimport Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero\nimport Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec\nimport Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFlagFrame\npublic import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProof\nimport Mathlib.CategoryTheory.Monoidal.Opposite.Mon\n\n"}
section -- clump:auto
@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

noncomputable section

namespace GlobalTheory.ModelFrameCompare

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isCombAtG_push {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} {v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left)} {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t'.G.left} (h : IsCombAtG t' x v a w) :
    IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a (w ≫ mm.φ) := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  refine ⟨fun i => B (u i), fun i => ?_, ?_⟩
  · rw [hB, hu, Category.assoc]
  · have e : B (List.ofFn u).prod = (List.ofFn fun i => B (u i)).prod := by
      rw [map_list_prod, List.map_ofFn]
      rfl
    rw [← e, hB, hw]

theorem isCombAtG_reflect {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f : S₁ ⟶ S₀} (mm : SABMap t' t f)
    {R : Type} [CommRing R] (x : Sp R ⟶ S₁) {n : ℕ} (v : Fin n → (Sp (DualNumber R) ⟶ t'.G.left))
    (hv : ∀ i, v i ≫ t'.G.hom = spMap (algebraMap R (DualNumber R)) ≫ x) {a : Fin n → R}
    {w : Sp (DualNumber R) ⟶ t.G.left} (h : IsCombAtG t (x ≫ f) (fun i => v i ≫ mm.φ) a w) :
    ∃ w' : Sp (DualNumber R) ⟶ t'.G.left, w' ≫ mm.φ = w ∧ IsCombAtG t' x v a w' := by
  obtain ⟨B, hB⟩ := GlobalTheory.Exist.FlagBaseChange.exists_pointEquiv mm.cart
    (spMap (algebraMap R (DualNumber R)) ≫ x) (spMap (algebraMap R (DualNumber R)) ≫ x ≫ f) (Category.assoc _ _ _)
  obtain ⟨u, hu, hw⟩ := h
  have hBs : ∀ z, (B.symm z).left ≫ mm.φ = z.left := fun z => by rw [← hB, B.apply_symm_apply]
  refine ⟨(B.symm (List.ofFn u).prod).left, by rw [hBs, hw], fun i => B.symm (u i), fun i => ?_, ?_⟩
  · refine mm.cart.1.hom_ext ?_ ?_
    · rw [hBs, hu, Category.assoc]
    · rw [Over.w (B.symm (u i)), Category.assoc, hv, ← Category.assoc, GlobalTheory.Exist.FlagBaseChange.epsMul_over]
      rfl
  · rw [map_list_prod, List.map_ofFn]
    rfl

theorem exists_sabMap_congr {S₀ S₁ : Scheme.{0}} {t' : SAB H S₁} {t : SAB H S₀} {f f' : S₁ ⟶ S₀} (mm : SABMap t' t f)
    (h : f = f') : ∃ mm' : SABMap t' t f', mm'.φ = mm.φ := by
  subst h
  exact ⟨mm, rfl⟩

end GlobalTheory.ModelFrameCompare

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralPointModelOverDvr =====
