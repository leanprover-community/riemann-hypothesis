module

public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStableCartan
import Mathlib.Algebra.Module.StablyFree.Basic
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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
public import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

private theorem algebra_trace_pi_eq_sum_trace {R A ι : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype ι]
    [Module.Free R A] [Module.Finite R A] (x : ι → A) :
    Algebra.trace R (ι → A) x = ∑ i, Algebra.trace R A (x i) := by
  classical
  let b := Module.Free.chooseBasis R A
  rw [Algebra.trace_eq_matrix_trace (Pi.basis fun _ : ι => b), Matrix.trace, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Algebra.leftMulMatrix_eq_repr_mul, Pi.basis_repr, Pi.basis_apply]

theorem UpperTheory.trace_mixedSpace_eq_mixedTraceL_mul :
    ∀ (K : Type) [Field K] [NumberField K] (x : NumberField.mixedEmbedding.mixedSpace K),
      Algebra.trace ℝ (NumberField.mixedEmbedding.mixedSpace K) x =
        mixedTraceL (K := K) (x * ((fun _ => (1 : ℝ)), (fun _ => (2 : ℂ)))) := by
  classical
  intro K _ _ x
  rw [Algebra.trace_prod_apply, algebra_trace_pi_eq_sum_trace, algebra_trace_pi_eq_sum_trace]
  simp [mixedTraceL, Algebra.trace_complex_apply, mul_comm]
