module

public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.integrated_rightRegular_eq_localOperator :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (μ : Measure (normOneGL (K := K) (n := n))) [μ.IsHaarMeasure] (w : Pl K)
          [MeasurableSpace (Gw n w)] [BorelSpace (Gw n w)] (mw : Measure (Gw n w)) [mw.IsHaarMeasure]
          (ψ : CompactlySupportedContinuousMap (Gw n w) ℂ) (T : LL μ →L[ℂ] LL μ), IsOloc μ w mw ψ T →
          (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
            (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1).integrated mw (UnitaryRep.ccToL1 mw ψ) = T := by
  intro K _ _ n μ _ w _ _ mw _ ψ T h
  refine ContinuousLinearMap.ext fun v => ext_inner_left ℂ fun u => ?_
  rw [UnitaryRep.inner_integrated, h u v]
  refine integral_congr_ae ((RightCosetSpace.coeFn_compactSupportToL1 mw ψ).mono fun g hg => ?_)
  have hr : (((rightRegularRep (rationalGLOne (K := K) (n := n)) μ).compHom (MultiplicityOne.finProj K n) MultiplicityOne.continuous_finProj).compHom
      (AdelicGLn.localEmbedding w) (UpperTheory.ConvolutionTheory.Tf.locEmb K n w).1) g = rhoL μ w g := by
    simp only [UnitaryRep.compHom_apply]
    rfl
  simp only [hr]
  exact congrArg (· * ⟪u, rhoL μ w g v⟫_ℂ) hg
