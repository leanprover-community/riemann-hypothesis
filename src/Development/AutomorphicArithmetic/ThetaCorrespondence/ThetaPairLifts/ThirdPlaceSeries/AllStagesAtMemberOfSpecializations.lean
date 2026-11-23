module

public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DiscreteSeriesUpqUniqueOfClassification
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.PublishedInputsThirdLayer
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ThetaDataExists
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SettingsFormsExistList
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MultiplicityCoverHypotheses
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FinitenessOfHyp
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.IsotypicOverAllComponents
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocalParameterStableAtUnramifiedPlace
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MultiplicityOfPrimitive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionSeriesB0
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionSeriesB2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReductionToLocalLanglandsA
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SCuspOfParSt
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SLarge
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SRatOfIsotInternal
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SXdAll
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SecondBoundOfPrimitive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SeriesCoverOfPrimitive
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.StepsPin
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
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
namespace GlobalTheory.HeightCounting.Up
theorem all_stages_of_specializations_alt : GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists →
    GlobalTheory.Published.DiscreteSeriesUpqUnique → _root_.GlobalTheory.Mem.Top.Bl.MultiplicityCoverHypotheses → _root_.GlobalTheory.HeightCounting.Up.PublishedInputsThirdLayerAlt → SerN →
    ∀ hL : _root_.UpperTheory.Zero.LLC.RecTExists, _root_.GlobalTheory.HeightCounting.ArchimedeanComparison' hL → _root_.GlobalTheory.HeightCounting.Up.PointStatement hL →
    _root_.GlobalTheory.HeightCounting.Up.SameGaloisLevelExists hL ∧ SMt ∧ _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL ∧ _root_.GlobalTheory.HeightCounting.Up.CuspStatement' hL ∧ _root_.GlobalTheory.HeightCounting.Up.FirstIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.SecondIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.ThirdIntermediateLevelExists hL ∧ _root_.GlobalTheory.HeightCounting.Up.StrictHenselianAcyclicLevelNonempty hL ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessStatement hL ∧
      ∀ cDep : ℝ, _root_.GlobalTheory.HeightCounting.Up.SettingsFormsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.SeriesExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.ModuliPointsExistList' hL cDep ∧ _root_.GlobalTheory.HeightCounting.Up.FinitenessListStatement hL cDep := by
  intro hCW hHM hW hD hU hH hP hS hL hA hPt
  have hMt : SMt := _root_.GlobalTheory.T.sMt_of_published_inputs' hP
  have hRat : _root_.GlobalTheory.HeightCounting.Up.RationalityStatementThirdPlaceSeries hL := _root_.GlobalTheory.HeightCounting.RatSide.sRat_of_isotInternal_inputs hU hP hS (_root_.GlobalTheory.HeightCounting.Up.IsotAtStates.isotInternal_at_states hW hD hH hP) hL
  have hPar : _root_.GlobalTheory.HeightCounting.Up.ParameterStatement hL := _root_.GlobalTheory.T.parSt_of_third_layer_sMt hP hMt hL
  have hEta : _root_.GlobalTheory.HeightCounting.Up.EtaStatement' hL := _root_.GlobalTheory.StEta.sEta_alt_alt_alt hP hL hPt
  have hFin := _root_.GlobalTheory.T.sFin_and_sFinl_of_archCmp_sEta_thetaData hW hD hP hL hA hEta (_root_.GlobalTheory.HeightCounting.Up.sXd_all_alt hL)
  have hG := _root_.GlobalTheory.HeightCounting.UpPin.steps_pin_alt hL 0
  refine ⟨_root_.GlobalTheory.T.stageASameGalois_of_inputs_phtCmp hP hA.pht hL, hMt, hRat, _root_.GlobalTheory.SCuspRows.sCusp_of_parSt_alt_alt hP hL hPar hRat, hG.1 (_root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN hP hS hL 0),
    hG.2.1 (_root_.GlobalTheory.T.seriesExistList_of_inputs_serN hP hS hL 0), hG.2.2.1 (_root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN hP hS hL 0), _root_.GlobalTheory.T.stage_c_nonempty_of_prints_third_layer hH.cover hCW hHM hP hS hL, hFin.1, fun c => ?_⟩
  exact ⟨_root_.GlobalTheory.T.settingsFormsExistList_of_inputs_serN hP hS hL c, _root_.GlobalTheory.T.seriesExistList_of_inputs_serN hP hS hL c, _root_.GlobalTheory.T.moduliPointsExistList_of_inputs_serN hP hS hL c, hFin.2 c⟩
end GlobalTheory.HeightCounting.Up
end

alias GlobalTheory.T.all_stages_at_member_of_specializations_alt :=
  GlobalTheory.HeightCounting.Up.all_stages_of_specializations_alt
end
