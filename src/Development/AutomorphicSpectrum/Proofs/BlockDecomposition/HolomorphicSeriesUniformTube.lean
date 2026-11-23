module

public import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.LocallyUniformLimit
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
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.Calculus.FDeriv.Basic

@[expose] public section

open Filter Topology

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem tubeGood_tsum (ι X T : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]
    [TopologicalSpace T] (t : ι → ℂ × ℂ → T → X) (Ω : Set (ℝ × ℝ))
    (hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g)
    (hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × T => t r y.1 y.2)
    (hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : ι → ℝ, Summable u ∧
      ∀ l ∈ PositivityTheory.RgEis.tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r) :
    PositivityTheory.RgEis.TubeGood (fun l g => ∑' r, t r l g) Ω ∧
      ∀ l ∈ PositivityTheory.RgEis.tube Ω, ∀ g, Summable fun r => ‖t r l g‖ := by
  have hc : Continuous fun l : ℂ × ℂ => (l.1.re, l.2.re) := by fun_prop
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro g p v τ₀ hτ₀
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hτ₀ g
    have hline : Continuous fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re) :=
      hc.comp (by fun_prop : Continuous fun τ : ℂ => p + τ • v)
    have hS : (fun τ : ℂ => ((p + τ • v).1.re, (p + τ • v).2.re)) ⁻¹' V ∈ 𝓝 τ₀ :=
      hline.continuousAt.preimage_mem_nhds hV
    obtain ⟨S, hSsub, hSo, hτS⟩ := mem_nhds_iff.1 hS
    have hd : DifferentiableOn ℂ (fun τ : ℂ => ∑' r, t r (p + τ • v) g) S :=
      Complex.differentiableOn_tsum_of_summable_norm hu
        (fun r => (hhol r g p v).differentiableOn) hSo
        (fun r τ hτ => hb _ (hSsub hτ) g (mem_of_mem_nhds hU) r)
    exact ((hd τ₀ hτS).differentiableAt (hSo.mem_nhds hτS)).differentiableWithinAt
  · rintro ⟨l₀, g₀⟩ ⟨hl₀, -⟩
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl₀ g₀
    have hVl : (fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V ∈ 𝓝 l₀ :=
      hc.continuousAt.preimage_mem_nhds hV
    have hS : ((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U ∈ 𝓝 (l₀, g₀) :=
      prod_mem_nhds hVl hU
    have hd : ContinuousOn (fun y : (ℂ × ℂ) × T => ∑' r, t r y.1 y.2)
        (((fun l : ℂ × ℂ => (l.1.re, l.2.re)) ⁻¹' V) ×ˢ U) :=
      continuousOn_tsum (fun r => (hcont r).continuousOn) hu
        (fun r y hy => hb _ hy.1 _ hy.2 r)
    exact (hd.continuousAt hS).continuousWithinAt
  · intro C hCΩ hC g
    refine hC.induction_on
      (p := fun S => ∃ U ∈ 𝓝 g, ∃ M : ℝ, ∀ l ∈ PositivityTheory.RgEis.tube S, ∀ g' ∈ U,
        ‖∑' r, t r l g'‖ ≤ M) ?_ ?_ ?_ ?_
    · exact ⟨Set.univ, univ_mem, 0, fun l hl => hl.elim⟩
    · rintro s s' hss ⟨U, hU, M, hM⟩
      exact ⟨U, hU, M, fun l hl g' hg' => hM l (hss hl) g' hg'⟩
    · rintro s s' ⟨U, hU, M, hM⟩ ⟨U', hU', M', hM'⟩
      refine ⟨U ∩ U', inter_mem hU hU', max M M', ?_⟩
      rintro l (hl | hl) g' hg'
      · exact (hM l hl g' hg'.1).trans (le_max_left _ _)
      · exact (hM' l hl g' hg'.2).trans (le_max_right _ _)
    · intro x hx
      obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom x (hCΩ hx) g
      exact ⟨V, mem_nhdsWithin_of_mem_nhds hV, U, hU, ∑' r, u r, fun l hl g' hg' =>
        tsum_of_norm_bounded hu.hasSum (fun r => hb l hl g' hg' r)⟩
  · intro l hl g
    obtain ⟨V, hV, U, hU, u, hu, hb⟩ := hdom _ hl g
    exact Summable.of_nonneg_of_le (fun r => norm_nonneg _)
      (fun r => hb l (show (l.1.re, l.2.re) ∈ V from mem_of_mem_nhds hV) g (mem_of_mem_nhds hU) r) hu

end GlobalTheory.CompanionTheory.RgEisCross
