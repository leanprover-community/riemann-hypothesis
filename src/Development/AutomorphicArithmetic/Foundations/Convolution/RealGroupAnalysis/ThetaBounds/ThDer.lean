module

public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.UnfoldedThetaIntegralConvergesSimilitudeOne
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.EmbPiInjective
public import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.WtBound
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Calculus.SmoothSeries
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
import Mathlib.Tactic.ReduceModChar

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff
open scoped Classical

theorem UpperTheory.ConvolutionTheory.R2.Ff.thDer :
    ∀ (F : Type) [Field F] [NumberField F], ThDer F := by
  intro F _ _ Ψ Ψ' hD t hDom
  obtain ⟨K, hK, hB⟩ := hDom
  obtain ⟨N, hN⟩ := wtSum F
  obtain ⟨C, hC⟩ := hN K hK 1 one_pos
  have hab : (1 : ℝ) ≤ ab (1 : (A F)ˣ) := by simp [ab]
  have hsum := (hC 1 hab).1
  obtain ⟨B, hB⟩ := hB N
  have hsc : ∀ ξ : Fin 4 → F, sc (1 : (A F)ˣ) ξ = fun i => rt (ξ i) := by
    intro ξ; funext i; simp [sc]
  obtain ⟨-, K', hK', hB'⟩ := wtBound F (Ψ t)
  have hs0 : Summable (fun ξ : Fin 4 → F => (Ψ t).1 fun i => rt (ξ i)) := by
    obtain ⟨B', hB'⟩ := hB' N
    obtain ⟨C', hC'⟩ := hN K' hK' 1 one_pos
    refine Summable.of_norm_bounded (g := fun ξ : Fin 4 → F => B' * wt K' N (sc (1 : (A F)ˣ) ξ)) ((hC' 1 hab).1.mul_left B') ?_
    intro ξ
    rw [hsc]
    exact hB' () (Set.mem_univ _) _
  have key := hasDerivAt_tsum_of_isPreconnected (𝕜 := ℝ) (F := ℂ)
    (u := fun ξ : Fin 4 → F => B * wt K N (sc (1 : (A F)ˣ) ξ))
    (g := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ s).1 fun i => rt (ξ i))
    (g' := fun (ξ : Fin 4 → F) (s : ℝ) => (Ψ' s).1 fun i => rt (ξ i))
    (t := Metric.ball t 1) (y₀ := t) (y := t)
    (hsum.mul_left B) Metric.isOpen_ball (convex_ball t 1).isPreconnected
    (fun ξ y _ => hD y _)
    (fun ξ y hy => by rw [hsc]; exact hB y hy _)
    (Metric.mem_ball_self one_pos) hs0 (Metric.mem_ball_self one_pos)
  exact key
