module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartIntSumOffHyperplane
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartChangeSheetNull
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

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

theorem ChartIntSumOffHyperplane.proof (hFB : FibreBound.Statement)
    (hCN : ChartChangeSheetNull.Statement) : ChartIntSumOffHyperplane.Statement := by
  intro n d J A u m f F φ hJ hdim hA hu hf hint

  have hnull := hCN n d J J A A u u Set.univ Set.univ id id hJ hdim hJ hdim hu hu hA hA isOpen_univ
    isOpen_univ (Set.subset_univ _) (Set.subset_univ _) differentiableOn_id differentiableOn_id
    (fun x hx => hx) (fun x hx => hx) (fun x _ => rfl) (fun x _ => rfl)
  have hae : ∀ᵐ y ∂(volume : Measure (Fin d → ℂ)),
      chartDens J A f φ y = ∑ b, chartDens J A (F b) φ y := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with y hy
    have hfin : (fibre J A y).Finite := (hFB n d J A hJ hdim hA y).2.1
    simp only [chartDens, sheetSum]
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    simp_rw [finsum_mem_eq_finite_toFinset_sum _ hfin]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Set.Finite.mem_toFinset] at hx
    split_ifs with hs
    · have hux : linEval u x ≠ 0 := by
        by_contra h0
        exact hy ⟨x, ⟨hx.1, hs, fun h => h.1 h0⟩, hx.2⟩
      rw [hf x hx.1 hux, Finset.sum_mul]
    · simp
  calc chartInt J A f φ = ∫ y, ∑ b, chartDens J A (F b) φ y := integral_congr_ae hae
    _ = ∑ b, chartInt J A (F b) φ := integral_finsetSum _ fun b _ => hint b

end

end GroundTheory.Heights₂.Heights
