module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.BaseChangeUnits.ComplexBaseChangeOfLiterature
public import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Cbcc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreDesc
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.CoreLift
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.DescStep
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftAll
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.LiftStep
import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.Places
public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStrong
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

@[expose] public section

theorem UpperTheory.ConvolutionTheory.T.cbcc_of_core (hC : UpperTheory.ConvolutionTheory.CI) (hG : UpperTheory.ConvolutionTheory.GM.GM) : UpperTheory.V.Z.Bc.CBCc :=
  have a := liftStep (coreLift hC hG)
  have b := liftAll a
  have c := descStep (coreDesc hC hG) b
  cbcc places a b c (splitStrong c)
