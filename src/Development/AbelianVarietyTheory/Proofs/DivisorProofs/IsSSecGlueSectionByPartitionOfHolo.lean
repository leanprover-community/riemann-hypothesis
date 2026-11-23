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
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.ContDiffAtSectionFrameQuotient
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem glue_isSSec_of_holo : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type)
    [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (C : Cover A) (la : La)
    (u : Fin C.m → V n → ℂ), (∀ a, DifferentiableOn ℂ (u a) (ball (C.c a) (C.r a))) →
    A.IsSSec (A.kap + la) (glue C la u) := by
  intro n Y _ _ _ _ _ ι La _ A C la u hu
  refine ⟨fun i => ?_, fun i j y hi hj => ?_⟩
  · have key : ∀ a, ContDiffOn ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v))) (A.chart i).target := by
      intro a v hv
      apply ContDiffAt.contDiffWithinAt
      by_cases hy : (A.chart i).symm v ∈ tsupport (C.chi a)
      · have hs := C.supp a hy
        have hovo : IsOpen (ovl A.chart i (C.idx a)) :=
          (A.chart i).isOpen_inter_preimage_symm (A.chart (C.idx a)).open_source
        have hvov : v ∈ ovl A.chart i (C.idx a) := ⟨hv, hs.1⟩
        have hUo : IsOpen (ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a)) :=
          (A.holo_trans i (C.idx a)).continuousOn.isOpen_inter_preimage hovo isOpen_ball
        have hvU : v ∈ ovl A.chart i (C.idx a) ∩
            (A.chart (C.idx a) ∘ (A.chart i).symm) ⁻¹' ball (C.c a) (C.r a) := ⟨hvov, hs.2⟩
        have h1 : ContDiffAt ℝ ∞ (C.chi a ∘ (A.chart i).symm) v :=
          (C.smooth a i).contDiffAt ((A.chart i).open_target.mem_nhds hv)
        have h1' : ContDiffAt ℝ ∞ (fun v => (C.chi a ((A.chart i).symm v) : ℂ)) v :=
          Complex.ofRealCLM.contDiff.contDiffAt.comp v h1
        have h2 : ContDiffAt ℝ ∞ (A.g (A.kap + la) i (C.idx a) ∘ (A.chart i).symm) v :=
          hyq_contDiffAt_of_holo hovo (A.holo_g _ _ _) hvov
        have h3 : ContDiffAt ℝ ∞ (u a ∘ (A.chart (C.idx a) ∘ (A.chart i).symm)) v :=
          hyq_contDiffAt_of_holo hUo ((hu a).comp
            ((A.holo_trans i (C.idx a)).mono Set.inter_subset_left) (fun w hw => hw.2)) hvU
        exact (h1'.mul h2).mul h3
      · have hn : (tsupport (C.chi a))ᶜ ∈ 𝓝 ((A.chart i).symm v) :=
          (isClosed_tsupport _).isOpen_compl.mem_nhds hy
        have h2 : ∀ᶠ w in 𝓝 v, (A.chart i).symm w ∉ tsupport (C.chi a) :=
          ((A.chart i).continuousAt_symm hv).preimage_mem_nhds hn
        refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        filter_upwards [h2] with w hw
        simp [image_eq_zero_of_notMem_tsupport hw]
    have he : (glue C la u i ∘ (A.chart i).symm) = fun v => ∑ a, (C.chi a ((A.chart i).symm v) : ℂ) *
        A.g (A.kap + la) i (C.idx a) ((A.chart i).symm v) *
        u a (A.chart (C.idx a) ((A.chart i).symm v)) := by
      funext v; simp [glue]
    rw [he]
    exact ContDiffOn.sum fun a _ => key a
  · simp only [glue]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : C.chi a y = 0
    · simp [h]
    · have hk := (C.supp a (subset_tsupport _ h)).1
      rw [A.g_cocycle (A.kap + la) i j (C.idx a) y hi hj hk]
      ring

end GlobalTheory.OTY
