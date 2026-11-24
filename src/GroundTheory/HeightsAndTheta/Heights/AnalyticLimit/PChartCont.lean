module

public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StRegSectionParts
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

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem continuousOn_of_chart_continuousOn {X : Type} [TopologicalSpace X] {D : ℕ} (A : FinHolAtlas D X)
    {U : Set X} (hU : IsOpen U) {E : Type} [TopologicalSpace E] (h : X → E)
    (hc : ∀ j, ContinuousOn (h ∘ (A.chart j).symm) ((A.chart j).target ∩ (A.chart j).symm ⁻¹' U)) :
    ContinuousOn h U := by
  intro x hx
  obtain ⟨m, hm⟩ := A.cover x
  set c := A.chart m
  have hT : IsOpen (c.target ∩ c.symm ⁻¹' U) := c.isOpen_inter_preimage_symm hU
  have hcx : c x ∈ c.target ∩ c.symm ⁻¹' U := ⟨c.map_source hm, by simpa [c.left_inv hm] using hx⟩
  have h1 : ContinuousAt (h ∘ c.symm) (c x) := (hc m).continuousAt (hT.mem_nhds hcx)
  have h2 : ContinuousAt ((h ∘ c.symm) ∘ c) x := by
    apply ContinuousAt.comp (f := c)
    · exact h1
    · exact c.continuousAt hm
  have heq : (h ∘ c.symm) ∘ c =ᶠ[nhds x] h := by
    filter_upwards [c.open_source.mem_nhds hm] with y hy
    simp [c.left_inv hy]
  exact (h2.congr heq).continuousWithinAt

theorem ChartCont.proof : ChartCont.Statement := by
  intro X _ D A U hU
  refine ⟨fun f hf => ?_, fun g hg => ?_⟩
  · exact continuousOn_of_chart_continuousOn A hU f fun j => (hf j).continuousOn
  · exact continuousOn_of_chart_continuousOn A hU g fun j => (hg j).continuousOn

end GroundTheory.Heights₂.Heights.AnalyticLimit
