module

public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.CuspReadPTrue
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.ArEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.BadFinite
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbEll
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.CmbTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.GenSt
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.HeckeFunctionIsHecke
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.LvEx
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.MultOfKer
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PeakRun
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PositionTest
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowNorm
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.PowRep
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RealUnivNe
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.FiniteAdelicEstimates.RepAlg
import Development.AutomorphicArithmetic.Foundations.Convolution.EndomorphismSlices.REndoOf
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

open UpperTheory.V.Z.Tf.GlobalTraceComparison PositivityTheory.Rg.BcB.Desc

namespace UpperTheory.Zero.ConvolutionTheory.EB

theorem specP (P : Pred) (h : CuspReadP P) : Spec P := rSpec_of peakRun genSt ptOk hkMul repAlg positionTest P (rRead P h)

theorem endoP (P : Pred) (h : CuspReadP P) : EndoP P :=
  rEndo_of arEx lvEx powRep cmbTest cmbEll repAlg powNorm P (specP P h)

theorem stableP (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) (P : Pred) (h : CuspReadP P) :
    StableP P := rStable h2 h3 h5 (cmbPi h1 h4) P (specP P h)

theorem endoBlockG (h : CuspReadI) : EndoBlockG := endoG_of (endoP _ (cuspReadP_inf h))

theorem stableBlockG (h : CuspReadI) (h1 : PiTerm) (h2 : PiFin) (h3 : PiAdm) (h4 : TwTrSum) (h5 : GrowthPiJ) : StableBlockG :=
  stableG_of (stableP h1 h2 h3 h4 h5 _ (cuspReadP_inf h))

end UpperTheory.Zero.ConvolutionTheory.EB
