module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatMem
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.HatN
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralMulLeftAdele
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.IntegralScale
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.QuaternaryFourierEqAdelic
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.Sl2InductionUnipotentWeyl
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaReindexing.ThetaSq
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

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.hatSt :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [IsTotallyReal F] [_root_.NumberField.IsTotallyComplex E] (D : Dat F E) (W : Weil D), St.Hat W := by
  intro F E _ _ _ _ _ _ _ D W
  have hδ : D.δ ≠ 0 := by
    intro h0
    have hθ : D.θ = 0 := by
      have h := D.sq
      rw [h0, map_zero] at h
      exact pow_eq_zero_iff (two_ne_zero) |>.mp h
    exact D.b.ne_zero 1 (by rw [D.b1, hθ])
  refine
    { n := _root_.UpperTheory.ConvolutionTheory.R2.D.hatN F E D W
      m := _root_.UpperTheory.ConvolutionTheory.R2.D.hatM F E D W
      w := ?_
      nE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatNE F E D W
      aE := _root_.UpperTheory.ConvolutionTheory.R2.D.hatAE F E D W
      mem := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).1
      th := fun φ => (_root_.UpperTheory.ConvolutionTheory.R2.D.hatMem F φ).2
      row := _root_.UpperTheory.ConvolutionTheory.R2.D.row F E D W }
  intro φ v
  have h : (W.Om (wW F) φ).1 = ft4 D.δ φ.1 := funext (W.Om_w φ)
  rw [h]
  exact _root_.UpperTheory.ConvolutionTheory.R2.D.hatW F D.δ φ v hδ
