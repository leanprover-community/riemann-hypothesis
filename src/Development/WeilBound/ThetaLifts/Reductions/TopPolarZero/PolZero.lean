module

public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLEntireAndNonzeroAtOne
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.FrameEstimates.SquareIntegrableWeilRange
public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesS
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.UnitaryDensity.EqTopOfLines
public import Development.WeilBound.ThetaLifts.LatticeBasics.BoxSec
public import Development.WeilBound.ThetaLifts.LatticeBasics.CartanBound2
public import Development.WeilBound.ThetaLifts.LatticeBasics.CoefLine
public import Development.WeilBound.ThetaLifts.LatticeBasics.EisCont
public import Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsGauss
public import Development.WeilBound.ThetaLifts.LatticeBasics.FinLevel
public import Development.WeilBound.ThetaLifts.LatticeBasics.FrameConj
public import Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe
public import Development.WeilBound.ThetaLifts.LatticeBasics.HermCpt
public import Development.WeilBound.ThetaLifts.LatticeBasics.HgtIntOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.LocDist
public import Development.WeilBound.ThetaLifts.LatticeBasics.PairsFin
public import Development.WeilBound.ThetaLifts.LatticeBasics.PolZero
public import Development.WeilBound.ThetaLifts.LatticeBasics.RatEquiv
import Development.WeilBound.ThetaLifts.LatticeBasics.SWFull
public import Development.WeilBound.ThetaLifts.LatticeBasics.SiegelWeilAnisoOf
public import Development.WeilBound.ThetaLifts.LatticeBasics.ThConstFin
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

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)
open PositivityTheory.ThKEst (GrpTop EpsOf SiegelAll FinVolU)
open PositivityTheory.ThKF (Unimod ArchOp ICont PureAct CartanConj CartanMove)

theorem _root_.PositivityTheory.ThKR.polynomial_vanishing_of_compactness (p0 : SiegelWeilStd) (p2 : EisBL) (p5 : GlobalTheory.Published.HeckeLEntireAndNonzeroAtOne)
    (hN : NonZeroAn) (hF : Factor) (hM : MatchEx) (hB : ThetaBasic) (hW : WeilConv) (hD : KDecay) (hI : ICont)
    (g1 : GrpTop) (g2 : EpsOf) (g3 : SiegelAll) (g4 : FinVolU) (g5 : Unimod) : PolZero :=
  have p1 := siegelWeilAniso_of p0 frameConj finLevel stab2Cpt
  have hc := cptAll_of g1 g2 g3 g4 g5
  have l1 := boxSec_of finLevel stab2Cpt
  have l6 := pairsStable
  polZero_of hc (hermLine_of' hc l6 pairsIrr hF hN hW hB hI hM)
    (coefLine_of (swFull_of p1.1 (eisContinues_of p2 frameConj) l1) l1 dblW (hgtEx_of stab2Cpt) (hgtInt_of stab2Cpt) stab2Cpt hc l6 hM
      hB hI polSch)
    (thConst_of' locDist goodNe (PositivityTheory.SA.constOfGood p5) hF hM hB hD g1 g2 g4 g5) hN hM hB hI polSch

end GlobalTheory.ThK.Dbl
