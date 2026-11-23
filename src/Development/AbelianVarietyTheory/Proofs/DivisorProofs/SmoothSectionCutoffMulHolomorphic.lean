module

public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FamilyLeCoords
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
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem smooth_cutoff_mul_sec : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (W : Set Y) (χ : Y → ℝ) (h : ι → Y → ℂ), IsOpen W → A.SmoothFn χ → tsupport χ ⊆ W → A.IsSecOn la W h → A.IsSSec la (fun i y => (χ y : ℂ) * h i y) := by
  intro n Y _ _ _ _ _ ι La _ A la W χ h hW hχ hsupp hh
  have hzero : ∀ y, y ∉ W → χ y = 0 := fun y hy =>
    Function.notMem_support.1 (fun hs => hy (hsupp (subset_tsupport χ hs)))
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · intro v hv
    refine ContDiffAt.contDiffWithinAt ?_
    set e := A.chart i
    have hvn : e.target ∈ 𝓝 v := e.open_target.mem_nhds hv
    have hχv : ContDiffAt ℝ ∞ (fun v => ((χ (e.symm v) : ℝ) : ℂ)) v :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp v ((hχ i).contDiffAt hvn)
    by_cases hy : e.symm v ∈ W
    · have hU : IsOpen (e.target ∩ e.symm ⁻¹' W) := e.isOpen_inter_preimage_symm hW
      have hh' : ContDiffAt ℝ ∞ (h i ∘ e.symm) v :=
        hyq_contDiffAt_of_holo hU (hh.1 i) ⟨hv, hy⟩
      exact hχv.mul hh'
    · have hnt : e.symm v ∉ tsupport χ := fun ht => hy (hsupp ht)
      have hev : χ =ᶠ[𝓝 (e.symm v)] 0 := notMem_tsupport_iff_eventuallyEq.1 hnt
      have hev' : ∀ᶠ v' in 𝓝 v, χ (e.symm v') = 0 := (e.continuousAt_symm hv).eventually hev
      refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
      filter_upwards [hev'] with v' hv'
      simp [hv']
  · by_cases hy : y ∈ W
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      rw [hh.2 i j y hy hi hj]; ring
    · show (χ y : ℂ) * h i y = A.g la i j y * ((χ y : ℂ) * h j y)
      simp [hzero y hy]

end GlobalTheory
