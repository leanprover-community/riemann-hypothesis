module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Development.AutomorphicArithmetic.Foundations.Convolution.PowerSumTraces.CuspidalMultiplicityOneTotallyComplex
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.Archimedean
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.AltSum
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.Counting
import GroundTheory.AutomorphicForms.QuotientMeasure
import GroundTheory.AutomorphicForms.ReductionBlock
public import Mathlib.Analysis.Normed.Module.FiniteDimension

@[expose] public section

open MeasureTheory NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C Polynomial Topology

theorem UpperTheory.finiteDimensional_of_compact_near_identity :
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (T : H →L[ℂ] H) (S : Submodule ℂ H), IsCompactOperator T → (∀ v ∈ S, ‖T v - v‖ ≤ 1 / 2 * ‖v‖) → FiniteDimensional ℂ S := by
  intro H _ _ _ T S hT hS
  have hcl : IsClosed {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
    isClosed_le (by fun_prop) (by fun_prop)
  have hS' : ∀ v ∈ S.topologicalClosure, ‖T v - v‖ ≤ 1 / 2 * ‖v‖ := by
    intro v hv
    have : closure (S : Set H) ⊆ {v : H | ‖T v - v‖ ≤ 1 / 2 * ‖v‖} :=
      closure_minimal (fun w hw => hS w hw) hcl
    exact this hv
  haveI : CompleteSpace S.topologicalClosure :=
    S.isClosed_topologicalClosure.completeSpace_coe
  let f : S.topologicalClosure →L[ℂ] H := T.comp S.topologicalClosure.subtypeL
  have hf : ∀ x : S.topologicalClosure, ‖x‖ ≤ ((2 : NNReal) : ℝ) * ‖f x‖ := by
    intro x
    have h1 := hS' x.1 x.2
    have h2 : ‖(x : H)‖ ≤ ‖T x‖ + ‖T x - x‖ := by
      have : (x : H) = T x - (T x - x) := by abel
      calc ‖(x : H)‖ = ‖T x - (T x - x)‖ := congrArg norm this
        _ ≤ _ := norm_sub_le _ _
    have h3 : ‖x‖ = ‖(x : H)‖ := rfl
    have h4 : f x = T x := rfl
    rw [h3, h4]
    push_cast
    linarith
  have hanti : AntilipschitzWith 2 f := f.antilipschitz_of_bound hf
  have hemb : IsClosedEmbedding f := hanti.isClosedEmbedding f.uniformContinuous
  obtain ⟨K, hK, hKsub⟩ := IsCompactOperator.image_closedBall_subset_compact (f := (T : H →ₗ[ℂ] H)) hT 1
  have hc : IsCompact (Metric.closedBall (0 : S.topologicalClosure) 1) := by
    refine (hemb.isCompact_preimage hK).of_isClosed_subset Metric.isClosed_closedBall ?_
    intro x hx
    apply hKsub
    refine ⟨(x : H), ?_, rfl⟩
    rw [mem_closedBall_zero_iff] at hx ⊢
    exact hx
  haveI : FiniteDimensional ℂ S.topologicalClosure :=
    FiniteDimensional.of_isCompact_closedBall₀ ℂ one_pos hc
  exact Submodule.finiteDimensional_of_le S.le_topologicalClosure
