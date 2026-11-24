module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
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
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.MeasureTheory.Measure.WithDensity

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace GlobalTheory

theorem lintegral_sublevel_tail_le (Y : Type) [MeasurableSpace Y] (μ : Measure Y) (g : Y → ℝ≥0∞)
    (x : Y → ℝ) (hx : Measurable x) (hg : ∫⁻ y, g y ∂μ < ⊤) (_hm : Measurable g)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ T0 : ℝ, ∀ T, T0 ≤ T → ∫⁻ y in {y | x y ≤ -T + 1}, g y ∂μ ≤ ε := by
  have hms : ∀ T : ℝ, MeasurableSet {y | x y ≤ -T + 1} := fun T =>
    measurableSet_le hx measurable_const
  haveI : IsFiniteMeasure (μ.withDensity g) := isFiniteMeasure_withDensity hg.ne
  have hanti : Antitone (fun n : ℕ => {y | x y ≤ -(n : ℝ) + 1}) := by
    intro a b hab y hy
    have : (a : ℝ) ≤ b := by exact_mod_cast hab
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  have h := tendsto_measure_iInter_atTop (μ := μ.withDensity g)
    (fun n : ℕ => (hms n).nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
  have hem : (⋂ n : ℕ, {y | x y ≤ -(n : ℝ) + 1}) = ∅ := by
    ext y
    simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall,
      not_le]
    obtain ⟨n, hn⟩ := exists_nat_gt (1 - x y)
    exact ⟨n, by linarith⟩
  rw [hem, measure_empty] at h
  obtain ⟨n, hn⟩ := (h.eventually (ge_mem_nhds hε)).exists
  refine ⟨n, fun T hT => ?_⟩
  rw [← withDensity_apply _ (hms T)]
  refine le_trans (measure_mono ?_) hn
  intro y hy
  simp only [Set.mem_setOf_eq] at hy ⊢
  linarith

end GlobalTheory
