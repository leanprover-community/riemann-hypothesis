module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ActsExK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultOfK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilFinFinal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Stab2CptK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGSplitFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.TPGTop
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicKAlt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseBoxSec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseDblW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseDense
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseEisCont
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFinLevel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseFrameConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseHgtInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseNormZeta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkBaseSWStd
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkEstEpsOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThkTowModel
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Unfold0K
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.VacFix2K
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.WpSTop
public import Development.AutomorphicArithmetic.ThetaCorrespondence.WeilRepresentation.WeilTheta
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.EvIHalfTrace
public import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.RLLieH
import Development.WeilBound.ThetaLifts.CartanFactorisation.Unimod
import Development.WeilBound.ThetaLifts.FrameEstimates.FundamentalDomainFiniteVolume
import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
import Development.WeilBound.ThetaLifts.FrameEstimates.SiegelAll
public import Development.WeilBound.ThetaLifts.Reductions.LieScalar2
public import Development.WeilBound.ThetaLifts.Reductions.LocalLift
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section



section
namespace UpperTheory.TP
open GlobalTheory.ThK.Dbl
theorem tools_holds_k : _root_.UpperTheory.TP.Tools_k :=
  have p1 := _root_.GlobalTheory.ThK.Dbl.siegelWeilAniso_of_k _root_.PositivityTheory.SiegelWeilFormula.Fin.siegelWeilStd_k _root_.GlobalTheory.ThK.Dbl.frameConj_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l1 := _root_.GlobalTheory.ThK.Dbl.boxSecX_of_k _root_.GlobalTheory.ThK.Dbl.finLevel_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
  have l2 : GlobalTheory.RealLift.LieSecond := PositivityTheory.ThKR.lieSecond2 PositivityTheory.ThKR.localLift_holds PositivityTheory.RL.derEx
  { swFull := _root_.GlobalTheory.ThK.Dbl.swFullX_of_k p1.2 (_root_.GlobalTheory.ThK.Dbl.eisContinues_of_k _root_.PositivityTheory.RgEis.Hd.eisBL_k _root_.GlobalTheory.ThK.Dbl.frameConj_k) l1
    boxSec := l1
    dbl := _root_.GlobalTheory.ThK.Dbl.dblX_k
    stab2 := _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k
    cpt := _root_.GlobalTheory.ThK.Dbl.cptAll_of_k PositivityTheory.ThKEst.grpTop_of _root_.PositivityTheory.ThKEst.epsOf_of_k
      (PositivityTheory.ThKEst.siegelAll_of UpperTheory.Lit.siegelSetUnitary_of_core) PositivityTheory.ThKEst.finVolU PositivityTheory.ThKF.unimodularity_holds
    basic := _root_.PositivityTheory.ThKF0.thetaBasic_k
    polSch := _root_.GlobalTheory.ThK.Dbl.polSch_k
    unfold0 := _root_.GlobalTheory.ThK.Dbl.unfold0_k
    pairEx := _root_.PositivityTheory.ThKG.Tow.pairEx_of_k _root_.PositivityTheory.ThKG.Tow.modelEx_k _root_.PositivityTheory.ThKW.S.weilEx_k
    split := _root_.UpperTheory.TP.splitFree_k
    vacFix := _root_.GlobalTheory.ThK.Dbl.vacFix2_k
    acts := _root_.PositivityTheory.ThKF0.actsEx_k
    lie1 := PositivityTheory.RL.lieFirst l2
    lie2 := l2 }
theorem tLift_holds_k : _root_.UpperTheory.TP.TLift_k := _root_.UpperTheory.TP.tLift_of_tools_k _root_.UpperTheory.TP.tools_holds_k (_root_.GlobalTheory.ThK.Dbl.hgtEx_of_k _root_.GlobalTheory.ThK.Dbl.stab2Cpt_k)
end UpperTheory.TP
end
