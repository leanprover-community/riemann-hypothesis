module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.CategoryTheory.Countable
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
