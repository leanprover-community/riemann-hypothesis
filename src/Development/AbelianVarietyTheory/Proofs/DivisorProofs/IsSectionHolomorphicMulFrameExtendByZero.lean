module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoloEtaleIffChartsStatement
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
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.isSecOn_frame_mul_ext0_and_measurable : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (la : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ) (F0 : U → ℂ), Etale A U z → A.IsFrameOn la U β → Holo n (fun y : U => z y) F0 → A.IsSecOn la U (fun i y => β i y * GlobalTheory.OTY.TwEst.ext0 U F0 y) ∧ Measurable (GlobalTheory.OTY.TwEst.ext0 U F0) := by
  intro n Y _ _ _ _ _ ι La _ A la U z β F0 hE hβ hF
  have hfun : (fun y : U => GlobalTheory.OTY.TwEst.ext0 U F0 y) = F0 :=
    funext fun y => GlobalTheory.OTY.TwEst.extendByZeroOnSubset_apply_coe U F0 y
  have hd := (GlobalTheory.T.holo_iff_differentiableOn_charts_of_etale n Y ι La A U z hE (GlobalTheory.OTY.TwEst.ext0 U F0)).1 (by rw [hfun]; exact hF)
  refine ⟨⟨fun i => (hβ.1.1 i).mul (hd i), fun i j y hy hi hj => ?_⟩, ?_⟩
  · show β i y * _ = _ * (β j y * _)
    rw [hβ.1.2 i j y hy hi hj, mul_assoc]
  · have hc : ContinuousOn (GlobalTheory.OTY.TwEst.ext0 U F0) U := by
      intro y hy
      have hs := A.mem_pick y
      set e := A.chart (A.pick y) with he
      have hop : IsOpen (e.target ∩ e.symm ⁻¹' U) := e.isOpen_inter_preimage_symm hE.isOpen
      have hm : e y ∈ e.target ∩ e.symm ⁻¹' U :=
        ⟨e.map_source hs, by simpa [e.left_inv hs] using hy⟩
      have h1 : ContinuousAt (GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) (e y) :=
        (hd (A.pick y)).continuousOn.continuousAt (hop.mem_nhds hm)
      have h2 : ContinuousAt ((GlobalTheory.OTY.TwEst.ext0 U F0 ∘ e.symm) ∘ e) y :=
        h1.comp (e.continuousAt hs)
      refine (h2.congr ?_).continuousWithinAt
      filter_upwards [e.open_source.mem_nhds hs] with x hx
      simp [e.left_inv hx]
    classical
    have hm := hc.measurable_piecewise (continuousOn_const (c := (0 : ℂ)) (s := Uᶜ))
      hE.isOpen.measurableSet
    convert hm using 1
    funext y
    by_cases hy : y ∈ U
    · simp [hy]
    · simp [hy, GlobalTheory.OTY.TwEst.ext0]
