module

public import Mathlib.Analysis.CStarAlgebra.Classes
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

@[expose] public section

open Filter Topology

namespace GlobalTheory

theorem real_pos_at_one_of_right (L : ℂ → ℂ) (hc : ContinuousAt L 1) (h1 : L 1 ≠ 0)
    (h : ∀ s : ℂ, 1 < s.re → s.im = 0 → (L s).im = 0 ∧ 0 < (L s).re) :
    (L 1).im = 0 ∧ 0 < (L 1).re := by
  have ht : Tendsto (fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (L 1)) := by
    have h0 : Tendsto (fun t : ℝ => (t : ℂ)) (𝓝 (1 : ℝ)) (𝓝 (1 : ℂ)) := by
      simpa using Complex.continuous_ofReal.tendsto 1
    exact (hc.tendsto.comp h0).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), (L (t : ℂ)).im = 0 ∧ 0 < (L (t : ℂ)).re := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t (by simpa using ht) (by simp)
  have him : (L 1).im = 0 := by
    have h2 := (Complex.continuous_im.tendsto _).comp ht
    have h3 : Tendsto (Complex.im ∘ fun t : ℝ => L (t : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 0) :=
      tendsto_const_nhds.congr' (hev.mono fun t ht => ht.1.symm)
    exact tendsto_nhds_unique h2 h3
  have hre : 0 ≤ (L 1).re :=
    ge_of_tendsto ((Complex.continuous_re.tendsto _).comp ht) (hev.mono fun t ht => ht.2.le)
  refine ⟨him, lt_of_le_of_ne hre fun h0 => h1 ?_⟩
  exact Complex.ext h0.symm him

end GlobalTheory
