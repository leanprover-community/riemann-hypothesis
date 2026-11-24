module

public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.HoloWeakStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates.C

open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal

theorem ident : IdentStatement := by
  intro n Ω F a hΩ hc hF ha h0 x hx
  set L : ℂ → V n := fun t => a + t • (x - a) with hL
  have hLd : Differentiable ℂ L := (differentiable_const a).add (differentiable_id.smul_const (x - a))
  have hLc : Continuous L := hLd.continuous
  set U : Set ℂ := L ⁻¹' Ω with hU
  have hUo : IsOpen U := hΩ.preimage hLc
  have hUconv : Convex ℝ U := by
    intro t1 ht1 t2 ht2 s1 s2 hs1 hs2 hs
    show L (s1 • t1 + s2 • t2) ∈ Ω
    have key : L (s1 • t1 + s2 • t2) = s1 • L t1 + s2 • L t2 := by
      have e : s1 • L t1 + s2 • L t2 = (s1 + s2) • a + (s1 • t1 + s2 • t2) • (x - a) := by
        simp only [hL, smul_add, add_smul, smul_assoc]
        abel
      rw [e, hs, one_smul]
    rw [key]
    exact hc ht1 ht2 hs1 hs2 hs
  have hG : DifferentiableOn ℂ (F ∘ L) U := hF.comp hLd.differentiableOn (fun t ht => ht)
  have hA : AnalyticOnNhd ℂ (F ∘ L) U := hG.analyticOnNhd hUo
  have h0U : (0 : ℂ) ∈ U := by
    show L 0 ∈ Ω
    simpa [hL] using ha
  have h1U : (1 : ℂ) ∈ U := by
    show L 1 ∈ Ω
    simpa [hL] using hx
  have hL0 : L 0 = a := by simp [hL]
  have hev : F ∘ L =ᶠ[𝓝 0] 0 := by
    have ht : Filter.Tendsto L (𝓝 0) (𝓝 a) := by
      rw [← hL0]
      exact hLc.continuousAt.tendsto
    exact ht.eventually h0
  have hEq := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUconv.isPreconnected h0U hev
  have h1 := hEq h1U
  simpa [hL] using h1

end ReciprocityTheory.L2DbarEstimates.C
