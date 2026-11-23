module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ASmooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.CprsMulRight
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.EvalPowE
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.FixFAnti
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.HomogMonomial
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.KillEx
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.OneSide
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SepPoly
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TrOnBot
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
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


open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci in
theorem UpperTheory.ConvolutionTheory.ci : UpperTheory.ConvolutionTheory.CI :=
  ciOf (trExp expForm) (evVal evEx Dp.parEx) valBc (killEx Dp.parEx) kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) evEx kill
