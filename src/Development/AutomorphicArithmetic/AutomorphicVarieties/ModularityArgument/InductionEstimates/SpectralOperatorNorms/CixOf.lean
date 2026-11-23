module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FamEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.FinsumSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillEx2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.KillExempt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.SpectralOperatorNorms.ChebyshevNormEstimates.OneSideX
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.ExistsPositivePeriodLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.PairFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ScatteringLimits.ConvolutionSpectra.ImportsAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.CprsMulRight
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.EvalPowE
import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.ExpForm
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.FixFAnti
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.HomogMonomial
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.OneSide
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.SepPoly
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpecAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockHeckeSlices.Imports
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.CuspidalMultiplicityOneTotallyComplex
import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.ParEx
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.EvExSub
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.TwInt
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspTrBand
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.DecayTraceClass
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.PolyBdAll
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SmoothDecay
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


open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.Ci UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.cix_of (hK : KernX) (hT : ForAllC fun _ _ _ μ _ _ _ _ _ _ _ _ A A' => TruncCpt μ A A') : CIx :=
  cixOf Dp.parEx (trExp expForm) (evVal evEx Dp.parEx) valBc killEx2 kfBc truncSpec sepPoly
    (oneSide K.kern2 C.polyBdAll C.smoothDecay C.decayTraceClass C.cuspTrBand Dp.multiplicity_one_cuspidal_spectrum_normOneGL evEx) (oneSideX hK evEx) evEx kill
    killExempt (famEx hT unitB pairFacts UpperTheory.V.Z.IntegralApplyAeEq.main)
