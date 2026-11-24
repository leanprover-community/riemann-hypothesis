module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Complex.CauchyIntegral

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.ComplexAnalysis

theorem iteratedDeriv_zero_eq_of_eq_on_real_points (f g : ℂ → ℂ) (ρ : ℝ) (hρ : 0 < ρ)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 ρ)) (hg : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (h : ∀ s : ℝ, |s| < ρ → f s = g s) (r : ℕ) :
    iteratedDeriv r f 0 = iteratedDeriv r g 0 := by

  have hU : IsOpen (Metric.ball (0 : ℂ) ρ) := Metric.isOpen_ball
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) ρ := Metric.mem_ball_self hρ
  have hreal : ∀ᶠ s : ℝ in 𝓝[≠] 0, f s = g s := by
    have hs : {s : ℝ | |s| < ρ} ∈ 𝓝 (0 : ℝ) :=
      (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using hρ)
    exact Filter.mem_of_superset (nhdsWithin_le_nhds hs) fun s hs' => h s hs'
  have htend : Tendsto (fun s : ℝ => (s : ℂ)) (𝓝[≠] 0) (𝓝[≠] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hc := Complex.continuous_ofReal.tendsto (0 : ℝ)
      simpa using hc.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      simpa using hs
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = g z := htend.frequently hreal.frequently
  have heq : Set.EqOn f g (Metric.ball 0 ρ) :=
    (hf.analyticOnNhd hU).eqOn_of_preconnected_of_frequently_eq (hg.analyticOnNhd hU)
      (convex_ball (0 : ℂ) ρ).isPreconnected h0 hfreq
  have hev : f =ᶠ[𝓝 0] g := Filter.mem_of_superset (hU.mem_nhds h0) heq
  exact hev.iteratedDeriv_eq r

end GlobalTheory.CompanionTheory.ComplexAnalysis
