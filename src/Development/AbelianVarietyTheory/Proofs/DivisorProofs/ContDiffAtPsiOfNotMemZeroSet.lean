module

public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.InnerProductSpace.Calculus
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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.LintegralBallRpowLtTop
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem contDiffAt_psi_of_notMem_zeroSet : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (L : La) (s : Fin n → ι → Y → ℂ), (∀ k, A.IsSec L (s k)) → ∀ y, y ∉ A.zeroSet s → ∀ i, y ∈ (A.chart i).source → ContDiffAt ℝ ∞ (psi A L s ∘ (A.chart i).symm) (A.chart i y) := by
  intro n Y _ _ _ _ _ ι La _ A L s hs y hy i hi
  have hv : A.chart i y ∈ (A.chart i).target := (A.chart i).map_source hi
  have hU : (A.chart i).target ∈ 𝓝 (A.chart i y) := (A.chart i).open_target.mem_nhds hv
  have hsk : ∀ k, ContDiffAt ℝ ∞ (s k i ∘ (A.chart i).symm) (A.chart i y) := fun k =>
    hyq_contDiffAt_of_holo (A.chart i).open_target (by simpa using (hs k).1 i) hv
  have hph : ContDiffAt ℝ ∞ (A.ph L i ∘ (A.chart i).symm) (A.chart i y) :=
    (A.smooth_ph L i).contDiffAt hU
  have h1 : ContDiffAt ℝ ∞ (fun v => ∑ k, ‖(s k i ∘ (A.chart i).symm) v‖ ^ 2 *
      Real.exp (-(A.ph L i ∘ (A.chart i).symm) v)) (A.chart i y) :=
    ContDiffAt.sum fun k _ => ((hsk k).norm_sq ℂ).mul hph.neg.exp
  have h2 : ContDiffAt ℝ ∞ (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [hU] with v hv'
    simp only [Function.comp, WeightedAtlas.sqn]
    exact Finset.sum_congr rfl fun k _ =>
      WeightedAtlas.nsq_eq_chart A (hs k) ((A.chart i).map_target hv')
  have hpos : 0 < A.sqn L s y := by
    obtain ⟨k, hk⟩ : ∃ k, s k (A.pick y) y ≠ 0 := by
      by_contra h
      exact hy fun k => by_contra fun hk => h ⟨k, hk⟩
    unfold WeightedAtlas.sqn WeightedAtlas.nsq
    refine Finset.sum_pos' (fun _ _ => by positivity) ⟨k, Finset.mem_univ _, ?_⟩
    have := norm_pos_iff.2 hk
    positivity
  have h3 : (A.sqn L s ∘ (A.chart i).symm) (A.chart i y) ≠ 0 := by
    simp only [Function.comp, (A.chart i).left_inv hi]
    exact hpos.ne'
  exact contDiffAt_const.mul (h2.log h3)

end GlobalTheory.OTY
