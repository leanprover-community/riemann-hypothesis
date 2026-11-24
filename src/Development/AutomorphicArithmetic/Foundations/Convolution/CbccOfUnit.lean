module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
public import Development.WeilBound.RepresentationTheoryGL.TwistedFactors.IntegralUnitBaseChange.InvTransposeGLInvTransposeGL
public import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.Ci
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.GmOfBcfl
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CbccOfCore
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

@[expose] public section

theorem UpperTheory.ConvolutionTheory.cbcc_of_unit (h : PositivityTheory.Rg.Tf.Loc.BCFLUnit) : UpperTheory.V.Z.Bc.CBCc :=
  UpperTheory.ConvolutionTheory.T.cbcc_of_core UpperTheory.ConvolutionTheory.ci (UpperTheory.ConvolutionTheory.GM.gm_of_bcfl h)
