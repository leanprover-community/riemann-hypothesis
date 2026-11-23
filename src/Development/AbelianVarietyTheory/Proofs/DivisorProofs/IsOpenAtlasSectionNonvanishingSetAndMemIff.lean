module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem isOpen_nz_and_mem_nz_iff : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (Λ : La) (τ : ι → Y → ℂ), A.IsSec Λ τ → IsOpen (nz A τ) ∧ ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
  intro n Y _ _ _ _ _ ι La _ A Λ τ h
  have key : ∀ i y, y ∈ (A.chart i).source → (y ∈ nz A τ ↔ τ i y ≠ 0) := by
    intro i y hy
    have e := h.2 i (A.pick y) y (Set.mem_univ _) hy (A.mem_pick y)
    have g := A.g_ne Λ i (A.pick y) y hy (A.mem_pick y)
    simp only [nz, Set.mem_setOf_eq, e, ne_eq, mul_eq_zero, g, false_or]
  refine ⟨?_, key⟩
  have cont : ∀ i, ContinuousOn (τ i) (A.chart i).source := by
    intro i
    have h1 : ContinuousOn (τ i ∘ (A.chart i).symm) (A.chart i).target := by
      simpa using (h.1 i).continuousOn
    have h2 := h1.comp (A.chart i).continuousOn (A.chart i).mapsTo
    refine h2.congr ?_
    intro y hy
    simp [(A.chart i).left_inv hy]
  rw [isOpen_iff_mem_nhds]
  intro y hy
  have hs := (A.chart (A.pick y)).open_source.mem_nhds (A.mem_pick y)
  have hc : ContinuousAt (τ (A.pick y)) y := (cont _).continuousAt hs
  have hne : τ (A.pick y) y ≠ 0 := hy
  filter_upwards [hs, hc.eventually_ne hne] with x hx hx'
  exact (key _ x hx).2 hx'

end GlobalTheory.OTY
