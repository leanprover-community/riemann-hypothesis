module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
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
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

private theorem summable_rational_schwartz (F : Type) [Field F] [NumberField F] (φ : S4 F) :
    Summable (fun ξ : Fin 4 → F => φ.1 fun i => rt (ξ i)) := by
  obtain ⟨-, K, hK, hB⟩ := wtBound F φ
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨B, hB⟩ := hB N
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by
    simp [ab]
  have hs := (hC 1 hab).1
  refine Summable.of_norm_bounded (g := fun ξ => B * wt K N (sc (1 : (A F)ˣ) ξ)) (hs.mul_left B) ?_
  intro ξ
  have := hB () (Set.mem_univ _) (fun i => rt (ξ i))
  have hsc : sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    funext i
    exact one_mul _
  rw [hsc]
  exact this

theorem UpperTheory.ConvolutionTheory.R2.Ff.thLin :
    ∀ (F : Type) [Field F] [NumberField F], ThLin F := by
  intro F _ _
  refine ⟨fun φ φ' => ?_, fun c φ => ?_⟩
  · have h : ∀ ξ : Fin 4 → F, (φ + φ').1 (fun i => rt (ξ i)) =
        φ.1 (fun i => rt (ξ i)) + φ'.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact (summable_rational_schwartz F φ).tsum_add (summable_rational_schwartz F φ')
  · have h : ∀ ξ : Fin 4 → F, (c • φ).1 (fun i => rt (ξ i)) =
        c * φ.1 (fun i => rt (ξ i)) := fun ξ => rfl
    simp only [Th, h]
    exact tsum_mul_left
