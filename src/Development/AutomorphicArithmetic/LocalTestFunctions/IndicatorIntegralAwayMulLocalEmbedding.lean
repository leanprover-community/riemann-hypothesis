module

public import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.SummandFactor
public import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.KernelTransforms.LocEmb
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

open MeasureTheory NumberField IsDedekindDomain MvPolynomial
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C
open scoped TensorProduct InnerProductSpace ComplexConjugate Pointwise

theorem UpperTheory.indicator_integral_away_mul_localEmbedding :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (w : Fin r → Pl K) (i : Fin r) (y : Gw n (w i)) (x : AdelicGLn.FiniteAdelicGL K n),
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator (1 : AdelicGLn.FiniteAdelicGL K n → ℂ) (AdelicGLn.localEmbedding (w i) y * x) =
          ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n)).indicator 1 x := by
  intro K _ _ n r w i y x
  have key : ∀ v, v ∉ Set.range w →
      finAt v (finEmb K n (AdelicGLn.localEmbedding (w i) y * x)) = finAt v (finEmb K n x) := by
    intro v hv
    have hne : v ≠ w i := fun h => hv ⟨i, h.symm⟩
    have h1 := (UpperTheory.ConvolutionTheory.Tf.locEmb K n (w i)).2.2.1 v hne y
    have e : ∀ z : AdelicGLn.FiniteAdelicGL K n,
        finAt v (finEmb K n z) = AdelicGLn.finiteRestrictedEquiv K n z v := fun z => rfl
    rw [e] at h1
    rw [e, e, map_mul, RestrictedProduct.mul_apply, h1, one_mul]
  have hmem : (AdelicGLn.localEmbedding (w i) y * x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) ↔
      (x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))) := by
    simp only [Set.mem_setOf_eq]
    exact forall₂_congr fun v hv => by rw [key v hv]
  by_cases hx : x ∈ ({y | ∀ v, v ∉ Set.range w → finAt v (finEmb K n y) ∈ GLnLocal.integralGL (v.adicCompletion K) n} : Set (AdelicGLn.FiniteAdelicGL K n))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem (hmem.2 hx)]
    rfl
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem (fun h => hx (hmem.1 h))]
