module

public import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtNull
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout
public import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MvDivIntegrand
public import Mathlib.MeasureTheory.Integral.IntegrableOn

@[expose] public section

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory Metric Filter Topology
open scoped ENNReal

theorem ext (n : ℕ) : EXTStatement n := by
  intro c r F u hF hu hL
  have hset : Metric.ball c r \ {y | F y = 0} = Metric.ball c r ∩ F ⁻¹' {(0 : ℂ)}ᶜ := by
    apply Set.ext
    intro y
    simp
  have hZ : IsOpen (Metric.ball c r \ {y | F y = 0}) := by
    rw [hset]
    exact hF.continuousOn.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
  have hint : IntegrableOn (fun z => ‖u z‖ ^ 2) (Metric.ball c r \ {z | F z = 0}) := by
    refine ⟨((hu.continuousOn.norm).pow 2).aestronglyMeasurable hZ.measurableSet, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => by positivity)).2 hL
  exact C.ext n (Metric.ball c r) F u Metric.isOpen_ball hF hu hint

theorem extNull (n : ℕ) : EXTNullStatement n :=
  fun c r F hF h => C.extNull n c r F hF h

theorem mv (n : ℕ) : MVStatement n := by
  intro R u ρ hu hρ hR
  have h := C.mv n 0 R u ρ hu hρ
  simp only [sub_zero] at h
  have hc : ∀ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) = ‖x‖ₑ ^ 2 := fun x => by
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm_eq_enorm]
  have hz : ∀ y : V n, y ∉ Metric.ball (0 : V n) R → ρ ‖y‖ = 0 := by
    intro y hy
    apply hR
    simpa [Metric.mem_ball, dist_zero_right, not_lt] using hy
  have e1 : ∫⁻ y in Metric.ball (0 : V n) R, ρ ‖y‖ = ∫⁻ y : V n, ρ ‖y‖ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra hb
    exact hy (hz y hb)
  have e2 : ∫⁻ y in Metric.ball (0 : V n) R, ‖u y‖ₑ ^ 2 * ρ ‖y‖ =
      ∫⁻ y : V n, ‖u y‖ₑ ^ 2 * ρ ‖y‖ := by
    apply setLIntegral_eq_of_support_subset
    intro y hy
    by_contra hb
    exact hy (by simp [hz y hb])
  simp_rw [hc]
  rw [← e1, ← e2]
  exact h

theorem mvInt (n : ℕ) : MVIntStatement n := by
  intro hn s
  rw [← C.mvPow n s hn]
  have h0 : volume ({0} : Set (V n)) = 0 := by
    let i : Fin n := ⟨0, hn⟩
    have hF : DifferentiableOn ℂ (fun z : V n => z i) (Metric.ball 0 1) :=
      (EuclideanSpace.proj i : V n →L[ℂ] ℂ).differentiable.differentiableOn
    have hne : ∃ z ∈ Metric.ball (0 : V n) 1, (fun z : V n => z i) z ≠ 0 := by
      refine ⟨EuclideanSpace.single i (1 / 2 : ℂ), ?_, ?_⟩
      · norm_num [Metric.mem_ball, PiLp.norm_single]
      · norm_num [PiLp.single_apply]
    have hnull := C.extNull n 0 1 _ hF hne
    apply measure_mono_null _ hnull
    intro z hz
    simp only [Set.mem_singleton_iff] at hz
    subst hz
    simp
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : V n) 1)),
      ENNReal.ofReal ‖z‖ ^ (-2 * s) = ENNReal.ofReal (‖z‖ ^ (-2 * s)) := by
    refine ae_restrict_of_ae ?_
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz
    have hz' : z ≠ 0 := by simpa using hz
    exact ENNReal.ofReal_rpow_of_pos (norm_pos_iff.2 hz')
  rw [lintegral_congr_ae hae]
  have hm : AEStronglyMeasurable (fun z : V n => ‖z‖ ^ (-2 * s))
      (volume.restrict (Metric.ball (0 : V n) 1)) :=
    (continuous_norm.measurable.pow_const _).aestronglyMeasurable
  have hnn : 0 ≤ᵐ[volume.restrict (Metric.ball (0 : V n) 1)] fun z : V n => ‖z‖ ^ (-2 * s) :=
    Filter.Eventually.of_forall fun z => by positivity
  constructor
  · intro h
    exact ⟨hm, (hasFiniteIntegral_iff_ofReal hnn).2 h⟩
  · intro h
    exact (hasFiniteIntegral_iff_ofReal hnn).1 h.2

end ReciprocityTheory.L2DbarEstimates
