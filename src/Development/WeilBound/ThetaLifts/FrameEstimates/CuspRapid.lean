module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.WeilBound.ThetaLifts.CartanFactorisation.CartanConj
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.OrthogonalDecomposition.SigThConst
public import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
public import Development.WeilBound.ThetaLifts.FrameEstimates.BlockForm
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefBd
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefEq
public import Development.WeilBound.ThetaLifts.FrameEstimates.CoefReal
public import Development.WeilBound.ThetaLifts.FrameEstimates.CuspRapidOf
public import Development.WeilBound.ThetaLifts.FrameEstimates.DomContinuous
public import Development.WeilBound.ThetaLifts.FrameEstimates.FourierInj
public import Development.WeilBound.ThetaLifts.FrameEstimates.GrpTop
public import Development.WeilBound.ThetaLifts.FrameEstimates.IInvOfParts
public import Development.WeilBound.ThetaLifts.FrameEstimates.InitialPairs.TriplePairHolds
public import Development.WeilBound.ThetaLifts.FrameEstimates.IsCompactIntV
public import Development.WeilBound.ThetaLifts.FrameEstimates.LinDer
public import Development.WeilBound.ThetaLifts.FrameEstimates.LineEx
public import Development.WeilBound.ThetaLifts.FrameEstimates.LineGen
public import Development.WeilBound.ThetaLifts.FrameEstimates.OneMemLines
public import Development.WeilBound.ThetaLifts.FrameEstimates.SchrAddPt
public import Development.WeilBound.ThetaLifts.FrameEstimates.SigRapid
public import Development.WeilBound.ThetaLifts.FrameEstimates.UMGLin
public import Development.WeilBound.ThetaLifts.FrameEstimates.UMGSmooth
public import Development.WeilBound.ThetaLifts.FrameEstimates.WeilConv
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

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem umgSmooth : UMGSmooth := umgSmooth_of (linDer_of lineGen_of lineEx_of) lineGen_of

theorem cuspRapid (h : GlobalTheory.Published.SiegelSetUnitary) : CuspRapid := cuspRapid_of h umgSmooth

theorem level : Level := level_of coefEq_of fourierInj_of (coefBd_of coefReal_of)

theorem iDer (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IDer := iDer_of hB hO hL (iInv_of hB)

theorem iUMG (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) : IUMG :=
  iUMG_of hB grpTop_of epsOf_of (iDer hB hO hL) level (iInv_of hB)

theorem sigRapid (h : GlobalTheory.Published.SiegelSetUnitary) (hB : ThetaBasic) (hO : PositivityTheory.ThKF.ArchOp) (hL : PositivityTheory.ThKF.ArchLie) :
    PositivityTheory.ThKEnd.Orth.SigRapid :=
  sigRapid_of hB umgLin_of epsOf_of (iUMG hB hO hL) (iInv_of hB) Sq.triplePair_holds (domWeil_of_U (domWeilU h)) (domSoU h)
    soFin_of (cuspRapid h)

end PositivityTheory.ThKEst

end
