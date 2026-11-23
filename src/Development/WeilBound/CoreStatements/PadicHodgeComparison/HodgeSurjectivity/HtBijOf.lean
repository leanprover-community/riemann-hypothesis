module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.HtBijOfParts
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechDApply
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsLocalizationAway
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CocycleZeroAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DWedgeExists
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaleMapRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTheta
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormConsEqSmul
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MapHEmptyBij
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemBOfSub
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OneResOfOneLow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiCongrRightSingle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelNullCast
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SglMem
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SlantOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedLogCocycleD
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.HodgeTateDimensionEquality
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoLow
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.OntoOf3Pf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.Retract
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.ChartLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.DivisorCoverOfChartLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.EtaleChartBaseChange.RelInjOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.ClsZeroOfNull
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NullClassVanishing.CupLaws
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.AffRelOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Faithful
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormCup
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormUniq
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.IsoBij
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.OmNatB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.RelLiftOf
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarRelOf
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime

@[expose] public section

namespace CrystallineSemistableComparison.Onto

theorem parts : Parts := by
  exact {
    mv := GlobalTheory.CompanionTheory.Onto.mvBij
    surj := GlobalTheory.CompanionTheory.OneSurjC.oneSurj
    cov := GlobalTheory.CompanionTheory.CovDescent.covDesc
    site := siteLaws_pf
    on := onIso_pf
    zar := zarAbs_pf
    laws := GlobalTheory.CompanionTheory.OntoForms.formLaws
    dw := GlobalTheory.CompanionTheory.Forms.dWedge_exists
    dl := GlobalTheory.CompanionTheory.OntoDLog.dLog
    kun := GlobalTheory.CompanionTheory.OmKun.omKun
    fc := formCup_pf
    div := divisor_cover_of_chart_laws chartLaws_pf
    chart := chartLaws_pf
    cup := cupLaws_pf
    zarRel := zarRelOf_pf
    affRel := affRelOf_pf
    lift := relLiftOf_pf
    inj := relInjOf_pf topRes_pf
    cone := GlobalTheory.CompanionTheory.ConeKillC.coneKillOf
    killOf := killOf3_pf
    low := ontoLow_pf
    retr := retract_pf
    aff := GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf
    c1 := GlobalTheory.CompanionTheory.OntoFirstChernCocycle.main
    kill := GlobalTheory.CompanionTheory.RelKill.relKillOf topRes_pf formUniq_pf omRes_pf
    kunAff := GlobalTheory.CompanionTheory.KunAffP.kunAffOf formUniq_pf
    nat := omNatB_pf
    iso := isoBij_pf
    bij := GlobalTheory.CompanionTheory.ChartBijOf.chartBij_of
      GlobalTheory.CompanionTheory.SurjectionOntoH4.h4a siteLaws_pf
      GlobalTheory.CompanionTheory.CechOne.oneLow
      (GlobalTheory.CompanionTheory.OneResProof.oneRes_of_oneLow
        GlobalTheory.CompanionTheory.CechOne.oneLow)
      GlobalTheory.CompanionTheory.CovDescent.covDesc (zarRelOf_pf siteLaws_pf onIso_pf zarAbs_pf)
      (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf) omNatB_pf omRes_pf
      (affRelOf_pf siteLaws_pf onIso_pf (GlobalTheory.CompanionTheory.AffOmP.affOm formUniq_pf)
        omNatB_pf GlobalTheory.CompanionTheory.OntoForms.formLaws)
      GlobalTheory.CompanionTheory.OntoForms.formLaws chartLaws_pf
    onto := ontoOf3_pf
    slant := GlobalTheory.CompanionTheory.KunGlue.slantOf topRes_pf
  }

theorem htBij_of  (hH : HT.HodgeTateMapExists) (hS : SqEx3) (hD : DiagEt3) (hF : EtFin) : HTBij :=
  htBij_of_parts (parts ) rank_equality hH hS hD hF

end CrystallineSemistableComparison.Onto
