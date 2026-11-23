module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroOnSubsetApplyCoe
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralAtlasMeasureEtalePullbackLebesgueStatement
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
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.APrimeI

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

theorem GlobalTheory.OTY.TwEst.lintegral_frame_transfer : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (E : La) (U : Set Y) (z : Y → V n) (β : ι → Y → ℂ), Etale A U z → A.IsFrameOn (A.kap + E) U β → ∀ (a : Y → ℂ) (w : Y → ℝ), Measurable a → Measurable w → (∀ y ∈ U, 0 ≤ w y) → ∫⁻ y in U, ENNReal.ofReal (A.nsq (A.kap + E) β y * ‖a y‖ ^ 2 * w y) ∂A.mu = ∫⁻ x : U, ENNReal.ofReal (‖a x‖ ^ 2 * (w x * Real.exp (-GlobalTheory.OTY.TwEst.wt A E β z x))) ∂vol n (fun y : U => z y) := by
  intro n Y _ _ _ _ _ ι La _ A E U z β hE hβ a w ha hw hw0
  classical
  have hUm : MeasurableSet U := hE.isOpen.measurableSet
  have hc := api_nsq_contOn A hE.isOpen hβ.1
  have hm := ContinuousOn.measurable_piecewise hc
    (continuousOn_const (c := (0 : ℝ)) (s := Uᶜ)) hUm
  set N : Y → ℝ := U.piecewise (A.nsq (A.kap + E) β) (fun _ => 0) with hN
  have hNU : ∀ y ∈ U, N y = A.nsq (A.kap + E) β y := fun y hy => by simp [hN, hy]
  have hΦ : Measurable fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y) :=
    ENNReal.measurable_ofReal.comp ((hm.mul (ha.norm.pow_const 2)).mul hw)
  rw [setLIntegral_congr_fun hUm
    (g := fun y => ENNReal.ofReal (N y * ‖a y‖ ^ 2 * w y)) (fun y hy => by simp only [hNU y hy]),
    GlobalTheory.T.lintegral_atlasMeasure_etale_pullback_lebesgue n Y ι La A U z hE _ hΦ]
  refine lintegral_congr fun x => ?_
  have hJ : 0 < A.nsq A.kap (jdet A z) x := by
    have := hE.det_ne (A.pick (x : Y)) x x.2 (A.mem_pick _)
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hB : 0 < A.nsq (A.kap + E) β x := by
    have : β (A.pick (x : Y)) x ≠ 0 := by
      exact hβ.2 _ x.2
    unfold WeightedAtlas.nsq
    exact mul_pos (pow_pos (norm_pos_iff.mpr this) 2) (Real.exp_pos _)
  have hwx := hw0 x x.2
  rw [hNU x x.2, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  unfold GlobalTheory.OTY.TwEst.wt
  rw [neg_add, neg_neg, Real.exp_add, Real.exp_neg, Real.exp_log hB, Real.exp_log hJ]
  ring
