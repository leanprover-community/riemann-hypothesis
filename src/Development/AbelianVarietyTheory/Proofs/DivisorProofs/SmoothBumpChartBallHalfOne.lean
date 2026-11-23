module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxD
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.BumpFunction.Basic

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_bump_chart_ball : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (i : ι) (p : V n) (ρ : ℝ), 0 < ρ → closedBall p ρ ⊆ (A.chart i).target → ∃ χ : Y → ℝ, A.SmoothFn χ ∧ tsupport χ ⊆ (A.chart i).source ∩ A.chart i ⁻¹' ball p ρ ∧ ∀ y ∈ (A.chart i).source, A.chart i y ∈ ball p (ρ / 2) → χ y = 1 := by
  intro n Y _ _ _ _ _ ι La _ A i p ρ hρ hK
  let b : ContDiffBump p := ⟨ρ / 2, 3 * ρ / 4, by linarith, by linarith⟩
  have hK0 : IsCompact (closedBall p (3 * ρ / 4)) := isCompact_closedBall p _
  have hK0t : closedBall p (3 * ρ / 4) ⊆ (A.chart i).target :=
    (closedBall_subset_closedBall (by linarith)).trans hK
  have hβs : ∀ u, (b : V n → ℝ) u ≠ 0 → u ∈ closedBall p (3 * ρ / 4) := by
    intro u hu
    have : u ∈ Function.support (b : V n → ℝ) := hu
    rw [b.support_eq] at this
    exact ball_subset_closedBall this
  refine ⟨A.chiC i b, A.chiC_smooth b.contDiff hβs hK0 hK0t, ?_, ?_⟩
  · have hC := (A.isCompact_chartImage hK0 hK0t).isClosed
    have hsup : Function.support (A.chiC i b) ⊆ (A.chart i).symm '' closedBall p (3 * ρ / 4) := by
      intro y hy
      by_contra h
      exact hy (A.chiC_eq_zero hβs h)
    refine (closure_minimal hsup hC).trans ?_
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨(A.chart i).map_target (hK0t hu), ?_⟩
    show A.chart i ((A.chart i).symm u) ∈ ball p ρ
    rw [(A.chart i).right_inv (hK0t hu)]
    exact closedBall_subset_ball (by linarith) hu
  · intro y hy hb
    rw [A.chiC_of_mem hy]
    exact b.one_of_mem_closedBall (ball_subset_closedBall hb)

end GlobalTheory
