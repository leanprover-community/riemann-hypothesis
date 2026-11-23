module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleIsLocalHomeomorphStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalInverseStatement
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
public import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.ChartSymmEventuallyEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FlatLocA
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical

@[expose] public section

open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory.OTY

theorem etale_leviNonneg : ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La] (A : WeightedAtlas n Y ι La), ∀ (U : Set Y) (z : Y → V n), Etale A U z → ∀ φ : Y → ℝ, (∀ x ∈ U, ∃ i, x ∈ (A.chart i).source ∧ ContDiffAt ℝ ∞ (φ ∘ (A.chart i).symm) (A.chart i x) ∧ ∀ ξ : Fin n → ℂ, 0 ≤ A.leviAt i φ x ξ) → LeviNonneg n (fun y : U => z y) (fun y : U => φ y) := by
  intro n Y _ _ _ _ _ ι La _ A U z hE φ hφ
  unfold LeviNonneg
  intro x ξ
  have hloc := GlobalTheory.T.etale_isLocalHomeomorph' n Y ι La A U z hE
  obtain ⟨e, he, hx⟩ := exists_chart n (fun y : U => z y) hloc x
  obtain ⟨i, hxi, hsm, hpos⟩ := hφ x.1 x.2
  have hzx : z x = e x := he hx
  have hv : e x ∈ e.target := e.map_source hx
  have hsx : e.symm (e x) = x := e.left_inv hx
  obtain ⟨hG, hev, -⟩ := GlobalTheory.T.contDiffAt_chart_inverse_of_etale n Y ι La A U z hE e he (e x) hv i (by rw [hsx]; exact hxi)
  rw [levi_eq_leviV n _ e he _ x hx ξ]
  show 0 ≤ (leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (z x) ξ).re
  rw [hzx]

  have heq : (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) =ᶠ[𝓝 (e x)]
      (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘ (fun v' => A.chart i (e.symm v' : Y)) := by
    filter_upwards [hev] with v' hv'
    simp only [Function.comp_apply, (A.chart i).left_inv hv']
  have hcongr : leviV n (fun y => ((φ (e.symm y : Y) : ℝ) : ℂ)) (e x) ξ =
      leviV n ((fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ)) ∘
        (fun v' => A.chart i (e.symm v' : Y))) (e x) ξ := by
    unfold leviV
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    congr 2
    apply wd_congr
    filter_upwards [heq.eventuallyEq_nhds] with y hy
    exact ReciprocityTheory.L2DbarEstimates.wdb_congr hy
  have hU : ContDiffAt ℝ 2 (fun w => ((φ ((A.chart i).symm w) : ℝ) : ℂ))
      ((fun v' => A.chart i (e.symm v' : Y)) (e x)) := by
    simp only [hsx]
    exact ((Complex.ofRealCLM.contDiff.contDiffAt).comp _ hsm).of_le (WithTop.coe_le_coe.mpr le_top)
  rw [hcongr, flA_leviV_comp hU (hG.of_le (WithTop.coe_le_coe.mpr le_top)) ξ]
  simp only [hsx]
  exact hpos _

end GlobalTheory.OTY
