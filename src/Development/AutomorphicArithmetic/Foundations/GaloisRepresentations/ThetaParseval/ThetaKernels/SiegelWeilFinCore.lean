module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisWk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcFcS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcOrbS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAfcUExS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAstepTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopField
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKlocopTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitGIinvCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsplitSplitCut
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKunfMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoAuto
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTautoCoef
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTbijMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTparMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilTweylCommB
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.HolomorphicAverageUniform
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilStandard.SiegelWeilStdOf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.VacuumGeneratesPolynomials
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
noncomputable section
open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Fin
theorem tTheta_k : _root_.PositivityTheory.SiegelWeilFormula.TTheta_k := _root_.PositivityTheory.SiegelWeilFormula.Tpar.tTheta_of_k (_root_.PositivityTheory.SiegelWeilFormula.tweyl.tthetaComm_k _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij)
theorem tAll_of_k (hW : _root_.PositivityTheory.SiegelWeilFormula.TWeyl_k) : _root_.PositivityTheory.SiegelWeilFormula.TAll_k := ⟨_root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij, _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k, hW, _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k, _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaAuto_k GlobalTheory.T.siegel_set_unitary _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k⟩
theorem thetaCoef_k : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k := _root_.PositivityTheory.SiegelWeilFormula.Tauto.thetaCoef_k GlobalTheory.T.siegel_set_unitary _root_.PositivityTheory.SiegelWeilFormula.TBij_k.tBij _root_.PositivityTheory.SiegelWeilFormula.Tpar.tPar_k _root_.PositivityTheory.SiegelWeilFormula.Fin.tTheta_k
theorem siegelWeilStd_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k)
    (hCT : _root_.PositivityTheory.SiegelWeilFormula.CTSplit_k) (hH : HolLead) : _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := by
  have hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
  have hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
  have hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k := _root_.PositivityTheory.SiegelWeilFormula.locOpEx_of_tAll_k hT
  have hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k := _root_.PositivityTheory.SiegelWeilFormula.KSplit.gSplit_of_k hF (_root_.PositivityTheory.SiegelWeilFormula.KAway.awayAct_of_tAll_k hT)
  have hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k := _root_.PositivityTheory.SiegelWeilFormula.Avac.vacK_of_k hT hF hLo hLI (_root_.PositivityTheory.SiegelWeilFormula.KAway.finAct_of_tAll_k hT)
  have hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k whitGenLt _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWE : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
    _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_k hT hA _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k hF hKP _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenEq _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hWL : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k := _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_k hVK hT hA hF _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k whitGenLow _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k hPK
  have hSt : _root_.PositivityTheory.SiegelWeilFormula.Step_k := _root_.PositivityTheory.SiegelWeilFormula.AStep.stepOf_k hH Holtb.holT hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hA _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k hF (_root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1) hLo hLI hGS hPK _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k
    _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k (_root_.PositivityTheory.SiegelWeilFormula.KSing.lamSing_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.Krd.denseW_k hA) _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hWL hVK
    (_root_.PositivityTheory.SiegelWeilFormula.Avac.iwaQ_of'_k hT) hCT _root_.PositivityTheory.SiegelWeilFormula.Afc.uEx_k (_root_.PositivityTheory.SiegelWeilFormula.Afc.fcConj_of_k hA) _root_.PositivityTheory.SiegelWeilFormula.Afc.orbRes_k
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.siegelWeilStd_of_k AbsSt.absThm hT _root_.PositivityTheory.SiegelWeilFormula.Fin.thetaCoef_k hLo hLI hGS (_root_.PositivityTheory.SiegelWeilFormula.KSplit.gIinv_of_k hT hF) hGD hKP hPK _root_.PositivityTheory.SiegelWeilFormula.kunf.unfold_k hW hWE
    AbsSt.vacuum_generates_polynomials hLD hVK hSt
end PositivityTheory.SiegelWeilFormula.Fin
end
end
