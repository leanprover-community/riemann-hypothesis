module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HodgeTraceFromLefschetzAndGroupSide
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.SigmaSplit
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsProjOverSPow
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SPowSmooth
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.HeckeTraceSemiHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.LevelIsPullback
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PAltLin
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntFn
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCntSum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PCoeffOcc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PFnDecomp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGeoStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHExpInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeEig
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeFin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHomEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHopWord
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKNNormal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSHodge
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSProj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLefSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PLegBc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PMapEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PModelBc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.POccOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPolPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PPowComp
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaFEt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PSigmaSplit
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTatePull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PTransPull
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PUnifBound
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PullCongr
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

namespace UpperTheory.Gal.LocalSmoothExtension

theorem HopWord_holds : HopWord := hopWord_of Tw.fnRing Tw.hopLin Tw.hopMul
theorem TransPull_holds : TransPull := transPull_of homEx_of polPull_of tatePull_of
theorem KSBc_holds : KSBc := kSBc_of (modelBc_of mapEq_of) (legBc_of mapEq_of TransPull_holds) powComp_of
theorem MemOp_holds : MemOp :=
  memOp2_of kNNormal_of cntFn_of cntSum_of sigmaFEt_of (sigmaSplit_of sigmaFEt_of Tw.splitsPts Tw.ptsOfSplits)
    Tw.twGal Tw.hopEx
theorem OccOf_holds : OccOf :=
  occOf_of MemOp_holds Tw.hodgeGood Tw.hodgeTr Tw.bcGood Tw.opBc Tw.opTr Tw.bcSplits
theorem KSProj_holds : KSProj := kSProj_of GlobalTheory.WeightTwoHeckePower.sPow_smooth GlobalTheory.WeightTwoHeckePower.isProjOver_sPow

theorem hodgeTrace_of_lefschetz_and_groupSide : HodgeTraceFromLefschetzAndGroupSide := fun hW hP hF h₁ h₂ =>
  have hT : UpperTheory.Gal.LocalSmoothExtension.HodgeTr :=
    hodgeTr_of (GroupTop_of h₁ h₂) fnDecomp_of HopWord_holds altLin_of
      (geoStep_of hW hP hF lefSum_of Tw.hodgeGood Tw.hodgeTr Tw.hopOp Tw.opTr)
      CxLin_holds Tw.hodgeGood
  have hE : HodgeEig :=
    hodgeEig_of hT hP (hodgeFin_of hW) unifBound_of hExpInj_of coeffOcc_of EigOf_holds HopWord_holds Tw.hodgeGood
  ⟨hT, hE, kSHodge_of hE KSBc_holds SpecConj_holds MemOp_holds fnDecomp_of OccOf_holds⟩

theorem ksHodge_of_inputs (hW : HolomorphicLefschetzFormula) (hF : FixK) (h₁ : GlobalTheory.RootSumWeights.MarkWeightedFixedPointEqDefinitePairOdd) (h₂ : GlobalTheory.LKDef.TraceDefinitePairsEqAutomorphicTrace) :
    UpperTheory.Gal.Int.Geo.KSHodge :=
  (hodgeTrace_of_lefschetz_and_groupSide hW KSProj_holds hF h₁ h₂).2.2

end UpperTheory.Gal.LocalSmoothExtension
