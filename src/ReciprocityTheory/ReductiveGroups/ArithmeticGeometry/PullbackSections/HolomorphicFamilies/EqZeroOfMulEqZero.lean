module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.FDeriv.Defs
public import Lemmata.FirstBlockLemmaJ.Imports
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf

open Metric Set Filter Topology

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem eq_zero_of_eventually {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {g : V → ℂ}
    (hg : DifferentiableOn ℂ g U) {x0 : V} (hx0 : x0 ∈ U) (h0 : g =ᶠ[𝓝 x0] 0) : ∀ y ∈ U, g y = 0 := by
  have hZo : IsOpen {x : V | g =ᶠ[𝓝 x] 0} := isOpen_setOfPred_eventually_nhds
  have hsub : U ⊆ {x : V | g =ᶠ[𝓝 x] 0} := by
    refine hc.subset_of_closure_inter_subset hZo ⟨x0, hx0, h0⟩ ?_
    rintro x ⟨hxc, hxU⟩
    obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.mp hU x hxU
    obtain ⟨z, hzZ, hzd⟩ := Metric.mem_closure_iff.mp hxc ε hε
    have hzb : z ∈ ball x ε := by rw [mem_ball, dist_comm]; exact hzd
    have hall := _root_.Bl.FirstBlockLemmaJ.goal1 (hg.mono hb) hzb hzZ
    exact Filter.eventually_of_mem (ball_mem_nhds x hε) hall
  intro y hy
  exact (hsub hy).self_of_nhds

theorem eq_zero_of_mul_eq_zero {U : Set V} (hU : IsOpen U) (hc : IsPreconnected U) {f g : V → ℂ}
    (hf : DifferentiableOn ℂ f U) (hg : DifferentiableOn ℂ g U) (hfg : ∀ y ∈ U, f y * g y = 0)
    {x0 : V} (hx0 : x0 ∈ U) (h0 : f x0 ≠ 0) : ∀ y ∈ U, g y = 0 := by
  refine eq_zero_of_eventually hU hc hg hx0 ?_
  have h1 : ∀ᶠ y in 𝓝 x0, f y ≠ 0 := (hf.continuousOn.continuousAt (hU.mem_nhds hx0)).eventually_ne h0
  filter_upwards [h1, hU.mem_nhds hx0] with y hy hyU
  exact (mul_eq_zero.mp (hfg y hyU)).resolve_left hy

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf
