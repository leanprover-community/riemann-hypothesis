module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgIsoPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAlgTr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGood
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFnRing
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGalInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeFun
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeGood
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeInj
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHodgeTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopDeep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopLin
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopMul
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHopOp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POpTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPlInv
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwSplit
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

@[expose] public section

namespace UpperTheory.Gal.LocalSmoothExtension.Tw

open UpperTheory.Gal.G3

theorem splitsPts : SplitsPts := pSplitsPts pIsoPts
theorem ptsOfSplits : PtsOfSplits := pPtsOfSplits
theorem bcSplits : BcSplits := by
  exact pBcSplits (pSplitsBasic splitsPts ptsOfSplits)
theorem bcGood : BcGood.{0} := pBcGood bcSplits (pBcGal bcSplits)
theorem opBc : OpBc.{0} := pOpBc bcSplits (pBcGal bcSplits)
theorem opTr : OpTr.{0} := pOpTr
theorem twSplit : TwSplit := pTwSplit splitsPts
theorem twGal : TwGal := pTwGal twSplit
theorem plInv : PlInv.{0} := pPlInv pGalInv twGal
theorem hopDeep : HopDeep.{0} := pHopDeep plInv
theorem hopEx : HopEx.{0} := pHopEx plInv hopDeep
theorem fnRing : FnRing := pFnRing
theorem hopLin : HopLin.{0} := by
  exact pHopLin fnRing hopDeep hopEx
theorem hopMul : HopMul.{0} := by
  exact pHopMul fnRing hopDeep hopEx
theorem hopOp : HopOp.{0} := by
  exact pHopOp fnRing hopEx twSplit twGal
theorem hodgeTr : HodgeTr := by
  exact pHodgeTr (pHodgeFun ptsOfSplits (pAlgSplit (pAlgIsoPts pIsoPts)) pAlgTr)
theorem hodgeGood : HodgeGood := pHodgeGood hodgeTr pHodgeInj

end UpperTheory.Gal.LocalSmoothExtension.Tw
