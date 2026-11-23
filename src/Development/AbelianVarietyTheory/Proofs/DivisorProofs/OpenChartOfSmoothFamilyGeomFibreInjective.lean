module

public import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveFamilyChartAffineOfChartFiniteTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionOfMonoLiftSmallArtinExtensionsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyChartOfAffineParametersStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyOpenChartAffineFiniteTypeStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleFamilyParamInjectiveOfGeomFiberInjectiStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothInjectiveFamilyLiftsSmallArtinianStatement
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

@[expose] public section

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartCrit

theorem openChart : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (U : Over (Sp R)) (M : LB (A ⊗ U).left), SmoothOfRelativeDimension g U.hom → Fam A M → FibInj A M → IsChart A M := by
  intro R _ _ A _ g hA hAg U M hU hM hF
  have hUf : LocallyOfFiniteType U.hom := by
    haveI := hU
    haveI : Smooth U.hom := SmoothOfRelativeDimension.smooth g _
    infer_instance
  have hI : Inj A M := GlobalTheory.T.lineBundleFamilyParamInjective_of_geomFiberInjective R A hA U M hUf hM hF
  refine ⟨hM, hI, ?_⟩
  intro T N hN
  refine GlobalTheory.T.lineBundleFamilyChart_of_affine_parameters (Sp R) A hA U M hM hI ?_ T N hN
  intro T _ N hN
  refine GlobalTheory.T.additiveFamily_chart_affine_of_chart_finiteType R A hA U M hM ?_ T N hN
  intro T _ hT N hN
  exact GlobalTheory.T.lineBundleFamily_openChart_affine_finiteType R A hA U M hUf hM hI (fun f _ _ _ h => GlobalTheory.T.isOpenImmersion_of_mono_lift_smallArtinExtensions f h) T hT N hN
    (GlobalTheory.T.smoothInjectiveFamily_lifts_small_artinian R A g hA hAg U M hU hM hI T N hN)

end GlobalTheory.ChartCrit
