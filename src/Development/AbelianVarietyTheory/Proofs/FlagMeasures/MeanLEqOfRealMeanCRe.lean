module

public import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
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

@[expose] public section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace GlobalTheory

theorem meanL_eq_ofReal_meanC_re (G : Type) [MeasurableSpace G] (μ : Measure G) (𝓕 : Set G)
    (ι : Type) [Countable ι] (f : ι → G → ℝ) (hm : ∀ i, Measurable (f i))
    (h0 : ∀ i h, 0 ≤ f i h) (hF : μ 𝓕 < ⊤)
    (hI : ∫⁻ h in 𝓕, ∑' i, ‖((f i h : ℝ) : ℂ)‖ₑ ∂μ < ⊤) :
    meanL μ 𝓕 (fun h => ∑' i, ENNReal.ofReal (f i h)) =
      ENNReal.ofReal (meanC μ 𝓕 (fun h => ∑' i, ((f i h : ℝ) : ℂ))).re := by
  set S : G → ℝ≥0∞ := fun h => ∑' i, ENNReal.ofReal (f i h) with hSdef
  have hnorm : ∀ i h, ‖((f i h : ℝ) : ℂ)‖ₑ = ENNReal.ofReal (f i h) := by
    intro i h
    rw [← ofReal_norm_eq_enorm, Complex.norm_real, Real.norm_of_nonneg (h0 i h)]
  have hS : ∫⁻ h in 𝓕, S h ∂μ < ⊤ := by
    simpa only [hnorm] using hI
  have hSm : Measurable S := Measurable.tsum (fun i => (hm i).ennreal_ofReal)
  have hae : ∀ᵐ h ∂(μ.restrict 𝓕), S h < ⊤ := ae_lt_top hSm hS.ne
  have hint : ∫ h in 𝓕, (∑' i, ((f i h : ℝ) : ℂ)) ∂μ = (((∫⁻ h in 𝓕, S h ∂μ).toReal : ℝ) : ℂ) := by
    have hcongr : (fun h => ∑' i, ((f i h : ℝ) : ℂ)) =ᵐ[μ.restrict 𝓕]
        fun h => (((S h).toReal : ℝ) : ℂ) := by
      filter_upwards [hae] with h hh
      have hsum : Summable (fun i => f i h) := by
        convert ENNReal.summable_toReal hh.ne using 1
        funext i
        exact (ENNReal.toReal_ofReal (h0 i h)).symm
      show _ = (((∑' i, ENNReal.ofReal (f i h)).toReal : ℝ) : ℂ)
      rw [← Complex.ofReal_tsum, ← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i h) hsum,
        ENNReal.toReal_ofReal (tsum_nonneg (fun i => h0 i h))]
    rw [integral_congr_ae hcongr, integral_complex_ofReal, integral_toReal hSm.aemeasurable hae]
  unfold meanL meanC
  rw [hint, Complex.smul_re, Complex.ofReal_re, smul_eq_mul]
  by_cases hz : μ 𝓕 = 0
  · have hr : μ.restrict 𝓕 = 0 := Measure.restrict_eq_zero.mpr hz
    simp [hr, hz]
  · rw [ENNReal.ofReal_mul (inv_nonneg.2 ENNReal.toReal_nonneg), ENNReal.ofReal_toReal hS.ne,
      ← ENNReal.toReal_inv, ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hz)]

end GlobalTheory
