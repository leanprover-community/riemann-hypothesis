module

public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BernsteinUnitaryProductIrreducible
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithAtProperty
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CompatibleSystemHypothesesOfLocalInputs
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.CompatibleSystemWeightOneSaturated
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MemberHodgeHypOfLocalInputsRationalWeights
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsBaseLatticeOfPrime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsWeilBlockNeAtMember
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsBuiltEPrmAIffStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicativeClosurePrimeMem
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNelStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaLiftHypothesesOfNonvanishing
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.Tactic.NormNum.Prime
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ConditionOfMemberHypotheses

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Fc.StageOneU

theorem member_bundles_large_unramified_exponents_alt : _root_.GlobalTheory.Fc.S0.UnitaryGroupThirdPlaceHypotheses → S0.RowRat →
    ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (cDep : ℝ) (A : GroupRetwisting.AtP), EvLgG A →
      StandardLattice.SiegelMassRatioCM ∧
      MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)).s ∧
      ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry)).s)
        (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.Mem.LiteralAutomorphy.extensionWithAtProperty hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) A) SExt.none (geoCl anyGeometry))) := by
  intro P hR hL cDep A hEv
  have sw := P.siegelWeilUnitaryConvergent2
  have hA := _root_.GlobalTheory.T.compatibleSystem_member_hypotheses P.globalArtinReciprocity P.cMCurveGoodOutsidePrimeSt P.weberRayFieldSt
    P.harishChandraModules P.cuspRapidDecay P.casselmanWallach P.harishChandraFinite
    P.discreteSeriesClassification P.discreteSeriesCoverExists
    P.formalDegreeCompactDual sw
  have hPM : _root_.GlobalTheory.Mem.LiteralAutomorphy.MemberHypotheses := ⟨P.harishChandraAnalyticity, P.discreteSeriesClassification, P.cuspRapidDecay,
    P.harishChandraFinite, P.cuspTraceClass, P.dixmierMalliavinFactorisation, P.flathFactorisation,
    P.zelevinskyPolynomialRing, P.geometricLemma, P.greenCuspidal⟩
  have hH := _root_.GlobalTheory.T.compatibleSystem_member_rationalWeights hPM P.harishChandraModules P.discreteSeriesCover P.casselmanWallach
    P.weilSiegelFormulaUnitary P.siegelWeilUnitarySchrodinger P.siegelEisensteinContinuation
    P.siegelEisensteinSimplePole P.unramifiedDoublingGL P.bernsteinZelevinskyFiniteness
    P.schurOrthogonalitySquareIntegrable hR
  have hW := _root_.GlobalTheory.T.compatibleSystem_weightOne_saturated hA hH
  have hM := _root_.GlobalTheory.T.member_multiplicatively_closed_alt P.harishChandraAnalyticity P.discreteSeriesClassification
    P.cuspRapidDecay P.harishChandraFinite P.cuspTraceClass P.dixmierMalliavinFactorisation
    P.flathFactorisation P.zelevinskyPolynomialRing P.geometricLemma
    P.greenCuspidal hL (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)
  obtain ⟨hE, -, -, hL', hN⟩ := _root_.GlobalTheory.T.hyps_e_third_layer_ser_n_of_geometric_galois P.litN P.toHypothesesX
  have hMember :=
    (_root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt hA hE hH hW hL hN cDep hM).1
  exact ⟨hA.a18,
    _root_.GlobalTheory.T.memberE_extensionWithAtProperty_of_evLgG hL _ _ _ A hEv hMember,
    _root_.GlobalTheory.T.compatibleSystem_weilBlock_ne_alt hA hH hPM hL _ _ A (fun _ _ _ _ _ _ _ _ _ _ _ _ _ x => ⟨x.1.1⟩)
      (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)⟩
end GlobalTheory.Fc.StageOneU
end

alias GlobalTheory.T.large_unramified_exponent_bundles_exist_alt :=
  GlobalTheory.Fc.StageOneU.member_bundles_large_unramified_exponents_alt
end
