module

public import Development.AutomorphicArithmetic.Foundations.Convolution.TraceSplitting.SplitStable
public import Development.AutomorphicArithmetic.Foundations.Convolution.CentreSplitting.AtInj
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

theorem UpperTheory.ConvolutionTheory.T.oneTerm :
    UpperTheory.ConvolutionTheory.T.OneTerm := by
  intro K _ _ _ n l _ μ _ θ 𝔰 V Λ t hV hθ hAt x j
  have hset : {V' : Submodule ℂ (UpperTheory.ConvolutionTheory.C.LL μ) | UpperTheory.ConvolutionTheory.C.IsSummand μ V' ∧
      V'.map (θ.U : UpperTheory.ConvolutionTheory.C.LL μ →ₗ[ℂ] UpperTheory.ConvolutionTheory.C.LL μ) = V' ∧
      UpperTheory.ConvolutionTheory.At μ 𝔰.S V' Λ t} = {V} := by
    ext V'
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, -, h3⟩
      exact UpperTheory.ConvolutionTheory.Dp.atInj K n μ V' V h1 hV 𝔰.S 𝔰.finS t h3.2 hAt.2
    · rintro rfl
      exact ⟨hV, hθ, hAt⟩
  unfold UpperTheory.ConvolutionTheory.Side.tr
  rw [hset, finsum_mem_singleton]
