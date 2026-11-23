module

public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarMass
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTubeCollarCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompare
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffTube
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Topology.Sheaves.Init

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Matrix ComplexSets

noncomputable section

theorem TubeCollarMass.proof (hC : TubeCollarCompare.Statement) (hM : ChartMassCompare.Statement)
    (hF : MassFinite.Statement) : TubeCollarMass.Statement := by
  intro n d J A P R hJ hdim hA hP
  obtain ⟨C, hCle⟩ := hC n d J A P R hJ hdim hA hP
  have hψ : ∀ k : Fin (d + 1), SmoothNear (zeroSet J) ((fun _ => euclPot) k) :=
    fun _ => smoothNear_of_contDiff (contDiff_euclPot n)

  have hI : Integrable (chartAbsDens J A ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ))
      (fun _ : Fin (d + 1) => euclPot)) := by
    obtain ⟨K, hK, hle⟩ := hM n (d + 1) J A (fun _ => euclPot) R hJ hdim hA hψ
    have hmeas := (SheetSumMeasurable.proof n (d + 1) J A
      ((Metric.closedBall (0 : Fin n → ℂ) R).indicator fun _ => (1 : ℝ)) (fun _ => euclPot) hJ hdim hA
      (measurable_const.indicator Metric.isClosed_closedBall.measurableSet) hψ).2
    refine ⟨hmeas.aestronglyMeasurable, ?_⟩
    have hbd : Bornology.IsBounded
        (WithLp.ofLp ⁻¹' Metric.closedBall (0 : Fin n → ℂ) R : Set (EuclideanSpace ℂ (Fin n))) :=
      (PiLp.antilipschitzWith_ofLp 2 fun _ : Fin n => ℂ).isBounded_preimage Metric.isBounded_closedBall
    obtain ⟨R', hR'⟩ := (Metric.isBounded_iff_subset_ball 0).1 hbd
    have h1 := hle (fun _ => 1) measurable_const
    simp only [enorm_one, setLIntegral_one] at h1
    refine h1.trans_lt (ENNReal.mul_lt_top hK ?_)
    exact (measure_mono (Set.inter_subset_inter_right _ hR')).trans_lt (hF n (d + 1) J hJ hdim R')

  have hl : Measurable (logAbsSq P) :=
    Real.measurable_log.comp ((MvPolynomial.continuous_eval P).norm.pow 2).measurable
  refine (hI.const_mul C).mono'
    (((measurable_tubeDens hA P R _).indicator (measurableSet_le measurable_const hl)).aestronglyMeasurable)
    (Eventually.of_forall fun y => ?_)
  rw [Real.norm_of_nonneg (Set.indicator_nonneg (fun y _ => tubeDens_nonneg J A P R _ y) y)]
  exact hCle y

end

end GroundTheory.Heights₂.Heights
