module

public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharInt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CoefPer
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.DMOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Dens
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianMatrixBasisOne
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.HermitianStandardVector
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.LatSum
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MeanZero
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.MomKill
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.OrbFn
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.RatGl
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Rev
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThCont
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.UnitsCpt
public import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
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

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

theorem maj_holds : Maj := maj latSum decE

theorem meanZero_holds : MeanZero := meanZero decE

theorem thetaConstantTerm_eq : ThetaLiftEqAnisotropicPart := f0Eq maj_holds thCont meanZero_holds (rank1 decE maj_holds orb1)

theorem rev_holds : Rev :=
  rev thetaConstantTerm_eq (coef maj_holds thCont) (thetaPairing_constantTerm_cuspidal maj_holds thCont thetaConstantTerm_eq (coef maj_holds thCont)) dens (fub maj_holds thCont)
    (coefPer decE maj_holds orbS momKill (orbFn orbS))

end UpperTheory.ConvolutionTheory.RankTwoDescent
