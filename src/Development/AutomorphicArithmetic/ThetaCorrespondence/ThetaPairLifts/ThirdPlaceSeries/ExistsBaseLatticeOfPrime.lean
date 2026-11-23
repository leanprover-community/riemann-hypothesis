module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.UpLReStage
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PositionMv
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotGeoClFalse
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.EventuallyAllScaleContextsAndOfBoth
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultQ
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HypN
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExtensionWithOrigin
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwistedBundle
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HypA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendsFineAdelicDatumLargerFieldOfPublishedStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.WeightSetResidueCharacteristic
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AllStagesAtMemberOfSpecializations
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.AutomorphyOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExBLIsLinkedPrmRStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FiniteLevelAndSecond
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Has3NeoOfSteps
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MemberEClosing
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.OrgOfKeptStatement
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SlotMvPrmRNelStatement
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
import Mathlib.Tactic.NormNum.Prime

@[expose] public section



section
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr GlobalTheory.Mem.SRe

namespace GlobalTheory.Mem.Top.Bl
theorem exists_baseLattice_of_pair_alt (hA : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt) (hE : _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis) (hH : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses) (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (hN : _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL) (N Ng : _root_.GlobalTheory.Mem.Top.Bl.NormChoiceExtension hL)
    (toB : ∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (_root_.GlobalTheory.HeightCounting.Up.extensionWithLaw hL K B f T w Z Wt p0 t nch n xd c))
    (toN : ∀ K B f T w Z Wt p0 t nch n xd c, Ng K B f T w Z Wt p0 t nch n xd c →
      Nonempty (N K B f T w Z Wt p0 t nch n xd c) ∧ GoodO (w.D Z) nch xd)
    (has3 : StepW Start (Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s))
    (lv : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (lvg : LevelThreeCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s)
    (intersection_update_fsHerm_neg_one : PositionMv (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
    (second : Pass KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) fun K B f T =>
      ∃ w : ColW B f T, Start K B f T w ∧ Has3 (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension Ng SExt.none (geoCl anyGeometry)).s K B f T w)
    (hMQ : _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) :
    MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)).s)
        (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry))) := by
  have exp := _root_.GlobalTheory.T.automorphy_of_hypotheses_alt_alt hE.e1 hE.e2 hE.e3 hE.e4 hE.e5 hE.e6 hE.e7 hE.e8 hE.e9 hE.e10 hE.e11 hE.e12 hE.e13 hA.a6 hE.e14 hA.a22
    hE.e15 hE.e16 hE.e17 hE.e18 hE.e19 hE.e20 hE.e21 hE.e22 hE.e23 hE.e24 hE.e25 hN.pr hN.ser hL hN.parMem N
    SExt.none (geoCl anyGeometry) toB
  refine ⟨?_, ?_⟩
  · exact _root_.GlobalTheory.Mem.Top.Closing.memberE_closing_alt_alt hA.a1 hA.a2 hA.a3 hA.a11 hA.a10 hA.a6 hA.a12 hA.a13 hA.a14 hA.a16 hA.a17 hA.a18 hA.a8 hA.a6 hA.a7
      hA.a5 hA.a19 hA.a20 hA.a21 hL N Ng has3 lv lvg exp second toN
  · exact _root_.GlobalTheory.T.geometric_parameter_uniform_alt hH.h1.q12 hH.cover hA.a5 hA.a7 hA.a8 hA.a9 hA.a10 hA.a6 hA.a22 hA.a23 hA.a1 hL N (geoCl anyGeometry)
      (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension N SExt.none (geoCl anyGeometry)) rfl toB intersection_update_fsHerm_neg_one hMQ
theorem exists_baseLattice_of_prime_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ,
    _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧
      GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s)
        (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  intro hA hE hH hW hL hN cDep hMQ
  have holdsW : WeightCaseCondition := _root_.GlobalTheory.T.w_of_weight_residue_char hH.h1 hH.h3 hH.multW
  have datE : DatExt := GlobalTheory.T.fineAdelicDatum_extends_to_larger_field_of_hypotheses hH.cover hA.a5 hA.a6 hA.a7 hA.a8 hA.a9 hA.a10
  obtain ⟨sA, sMt, sRat, sCusp, -, -, -, sC, -, stages⟩ :=
    _root_.GlobalTheory.T.all_stages_at_member_of_specializations_alt
      hA.a7 hA.a5 hA.a8 hA.a9 hA.a12 hH hN.pr hN.ser hL hN.arch hN.pt
  obtain ⟨settings, series, points, finiteness⟩ := stages cDep
  obtain ⟨fin, second⟩ := _root_.GlobalTheory.T.sFino_and_secondNo_of_sFinl'
    hH.cover hA.a7 hA.a5 hN.pr hN.ser datE holdsW hA.a9 hN.arch.pht hL sMt sRat sCusp cDep finiteness
  have has3 := _root_.GlobalTheory.Mem.Top.Bl.has3_neo_of_localLanglands_alt
    hL cDep hW sA sMt sRat sCusp settings series points sC fin SExt.none (geoCl anyGeometry)
  have lv := _root_.GlobalTheory.T.lv3Mv_extensionWithOrigin_and_NEog hL cDep SExt.none (geoCl anyGeometry)
  refine exists_baseLattice_of_pair_alt hA hE hH hL hN
    (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep)
    (_root_.GlobalTheory.HeightCounting.Up.GeometricNormExtension hL cDep)
    ?_ ?_ has3 lv.1 lv.2
    (_root_.GlobalTheory.T.slot_mv_extension_with_origin_geo_cl hL cDep anyGeometry)
    (second SExt.none (geoCl anyGeometry)) hMQ
  · intro K B f T w Z Wt p0 t nch n xd c h
    exact ⟨h.1.1⟩
  · intro K B f T w Z Wt p0 t nch n xd c h
    exact ⟨⟨h.1⟩, h.2.down⟩
end GlobalTheory.Mem.Top.Bl
end
section
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up

theorem _root_.GlobalTheory.T.member_exists_baseLattice_alt : _root_.GlobalTheory.Mem.Top.Bl.HypAAlt → _root_.GlobalTheory.Mem.Top.Bl.EllipticHypothesis → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → ExistsUnlocalizedSaturatedState → ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.Mem.Top.Bl.LocalLanglandsHypothesis hL → ∀ cDep : ℝ, _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCondition (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)) → MemberE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s ∧ GlobalTheory.Fc.ExBL KPx (IsBuiltE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (IsGoodE (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry)).s) (_root_.GlobalTheory.Mem.Top.Bl.BundleLinkage (_root_.GlobalTheory.Mem.Top.Bl.parametersOfExtension (_root_.GlobalTheory.HeightCounting.Up.extensionWithOrigin hL cDep) SExt.none (geoCl anyGeometry))) := by
  exact _root_.GlobalTheory.Mem.Top.Bl.exists_baseLattice_of_prime_alt
end
end
