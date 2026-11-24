module

public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.DefsObj
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open GlobalTheory.CuspRep (CuspSub GA Af Ad finGL locGL)
open UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Dp UpperTheory.V

private theorem localEmbedding_eq {K : Type} [Field K] [NumberField K] {n : ℕ}
    (w : HeightOneSpectrum (𝓞 K)) (g : GL (Fin n) (w.adicCompletion K)) :
    AdelicGLn.localEmbedding w g = locGL K n w g := by
  classical
  refine Units.ext <| Matrix.ext fun a b => FiniteAdeleRing.ext K fun v => ?_
  change ((AdelicGLn.finiteRestrictedEquiv K n).symm _ : AdelicGLn.FiniteAdelicGL K n) a b v = _
  rw [AdelicGLn.finiteRestrictedEquiv_symm_apply, RestrictedProduct.coe_mulSingle_apply]
  by_cases h : v = w
  · subst h
    rw [Pi.mulSingle_eq_same]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL v g)).symm
  · rw [Pi.mulSingle_eq_of_ne h]
    exact (congrArg (fun x : GL (Fin n) (v.adicCompletion K) => x a b) (GlobalTheory.CuspRep.pLoc_locGL_of_ne h g)).symm

private theorem finProj_eq {K : Type} [Field K] [NumberField K] {n : ℕ} (u : AdelicGLn.FiniteAdelicGL K n) :
    MultiplicityOne.finProj K n u = retractOne (finGL K n u) := by
  rw [← Fb.finEmb_eq]
  exact Subtype.ext rfl

theorem UpperTheory.ConvolutionTheory.Dp.rhoLoc :
    UpperTheory.ConvolutionTheory.Dp.RhoLoc := by
  intro K _ _ n μ _ w g v
  change rightRegularRep (rationalGLOne (K := K) (n := n)) μ (MultiplicityOne.finProj K n (AdelicGLn.localEmbedding w g)) v =
    rightRegularRep (rationalGLOne (K := K) (n := n)) μ (retractOne (finGL K n (locGL K n w g))) v
  rw [finProj_eq, localEmbedding_eq]
