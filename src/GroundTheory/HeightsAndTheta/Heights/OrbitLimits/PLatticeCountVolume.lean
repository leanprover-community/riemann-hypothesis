module

public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsLatticeCountVolume
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
import Mathlib.Dynamics.Ergodic.Action.Regular
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace LatticeCountVolume

theorem measure_le_encard_mul {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (La : Submodule ℤ E) [DiscreteTopology La] [IsZLattice ℝ La]
    (S T : Set E) (hS : MeasurableSet S) (hST : ∀ x ∈ S, ∀ y ∈ S, x - y ∈ T) {F : Set E}
    (fund : IsAddFundamentalDomain La F μ) :
    μ S ≤ (({x : E | x ∈ La ∧ x ∈ T}.encard : ℕ∞) : ℝ≥0∞) * μ F := by
  have : MeasurableVAdd La E := (inferInstance : MeasurableVAdd La.toAddSubgroup E)
  have : VAddInvariantMeasure La E μ :=
    (inferInstance : VAddInvariantMeasure La.toAddSubgroup E μ)
  have : Countable La := inferInstance
  set A := {x : E | x ∈ La ∧ x ∈ T} with hAdef
  have key : ∀ y : E, ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) ≤
      ((A.encard : ℕ∞) : ℝ≥0∞) := by
    intro y
    set U : Set La := {g | (g : E) + y ∈ S} with hUdef
    have h1 : ∑' g : La, S.indicator (1 : E → ℝ≥0∞) (g +ᵥ y) =
        ∑' g : La, U.indicator (1 : La → ℝ≥0∞) g := by
      congr 1
    rw [h1, ← tsum_subtype]
    simp only [Pi.one_apply]
    rw [ENNReal.tsum_set_one]
    refine ENat.toENNReal_le.mpr ?_
    rcases U.eq_empty_or_nonempty with hU | ⟨g₀, hg₀⟩
    · simp [hU]
    refine Set.encard_le_encard_of_injOn (f := fun g : La => (g : E) - g₀) ?_ ?_
    · intro g hg
      refine ⟨La.sub_mem g.2 g₀.2, ?_⟩
      have hsub : (g : E) - g₀ = ((g : E) + y) - ((g₀ : E) + y) := by abel
      show (g : E) - g₀ ∈ T
      rw [hsub]
      exact hST _ hg _ hg₀
    · intro g _ g' _ h
      exact Subtype.ext (sub_left_injective h)
  calc μ S = ∫⁻ z, S.indicator 1 z ∂μ := (lintegral_indicator_one hS).symm
    _ = ∑' g : La, ∫⁻ z in F, S.indicator 1 (g +ᵥ z) ∂μ := fund.lintegral_eq_tsum'' _
    _ = ∫⁻ z in F, ∑' g : La, S.indicator 1 (g +ᵥ z) ∂μ :=
        (lintegral_tsum fun g => ((measurable_one.indicator hS).comp
          (measurable_const_vadd g)).aemeasurable).symm
    _ ≤ ∫⁻ _ in F, ((A.encard : ℕ∞) : ℝ≥0∞) ∂μ := lintegral_mono fun z => key z
    _ = ((A.encard : ℕ∞) : ℝ≥0∞) * μ F := setLIntegral_const _ _


open scoped Classical in
theorem proof : LatticeCountVolume.Statement := by
  intro E _ _ _ _ _ μ _ La _ _ S T hS hST
  set b := Module.Free.chooseBasis ℤ La
  have fund := ZLattice.isAddFundamentalDomain b μ
  have hcov := ZLattice.covolume_eq_measure_fundamentalDomain La μ fund
  have hFtop : μ (ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ)) ≠ ⊤ :=
    (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  rw [hcov, measureReal_def, ENNReal.ofReal_toReal hFtop]
  exact measure_le_encard_mul μ La S T hS hST fund

end LatticeCountVolume

end

end GroundTheory.Heights₂.Heights.Targets
