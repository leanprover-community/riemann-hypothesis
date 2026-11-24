module

public import Formalism.LocalRingCardinality.DataParams₂
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.BasicNotions

namespace GlobalTheory

theorem scale_large_three (eps : ℝ) (he : 0 < eps) : ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x →
    Real.log (4 * s.x) ≤ s.L ∧ 8 ≤ s.X' ∧ 2 ≤ s.x := by
  have h1 : ∀ᶠ x : ℝ in Filter.atTop, Real.log x ≤ (1/2) * x ^ eps := by
    have := (isLittleO_log_rpow_atTop he).bound (c := 1/2) (by norm_num)
    filter_upwards [this, Filter.eventually_gt_atTop 1] with x hx hx1
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1.le
    have hp : 0 ≤ x ^ eps := Real.rpow_nonneg (by linarith) _
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hl, abs_of_nonneg hp] at hx
    exact hx
  have h2 : ∀ᶠ x : ℝ in Filter.atTop, Real.log 4 ≤ (1/2) * x ^ eps := by
    have := (tendsto_rpow_atTop he).eventually_ge_atTop (2 * Real.log 4)
    filter_upwards [this] with x hx
    linarith
  have h3 : ∀ᶠ x : ℝ in Filter.atTop, (3 : ℝ) ≤ x ^ (eps / 3) :=
    (tendsto_rpow_atTop (by linarith : 0 < eps / 3)).eventually_ge_atTop 3
  obtain ⟨x0, hx0⟩ := Filter.eventually_atTop.1
    (h1.and (h2.and (h3.and (Filter.eventually_ge_atTop (2 : ℝ)))))
  refine ⟨x0, fun s hs hx => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hx0 s.x hx
  have hxpos : 0 < s.x := by linarith
  refine ⟨?_, ?_, a4⟩
  · show Real.log (4 * s.x) ≤ s.x ^ s.eps
    rw [Real.log_mul (by norm_num) hxpos.ne', hs]
    linarith
  · show 8 ≤ Real.exp (s.x ^ (s.eps / 3))
    rw [hs]
    have he1 : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ); linarith
    have h8 : (8 : ℝ) ≤ Real.exp 3 := by
      have : Real.exp 3 = Real.exp 1 ^ 3 := by
        rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) he1 3]
    exact h8.trans (Real.exp_le_exp.2 a3)

end GlobalTheory
