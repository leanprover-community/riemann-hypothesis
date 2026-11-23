module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TensFun
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.LocHeckeInert

@[expose] public section

noncomputable section

open MeasureTheory NumberField IsDedekindDomain Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.RightCosetSpace
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM UpperTheory.ConvolutionTheory.C
open scoped RestrictedProduct Classical

namespace PositivityTheory.TfC.FixLev

variable {K : Type} [Field K] [NumberField K] {n : ℕ}

theorem finAt_finEmb (u : AdelicGLn.FiniteAdelicGL K n) (v : Pl K) :
    finAt v (finEmb K n u) =
      (AdelicGLn.finiteRestrictedEquiv K n u v : GL (Fin n) (v.adicCompletion K)) := by
  ext a b
  rw [finAt_apply, AdelicGLn.finiteRestrictedEquiv_apply, ← AdelicGLn.prodEquiv_apply_snd,
    prodEquiv_finEmb]


variable (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure]


end PositivityTheory.TfC.FixLev
