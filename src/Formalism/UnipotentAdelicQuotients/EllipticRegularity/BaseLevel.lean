module

public import Formalism.UnipotentAdelicQuotients.EllRegCut
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
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
import Mathlib.Tactic.Lemma
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

@[expose] public section

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma norm_fourier_le_integral_norm {d : ℕ} (g : E d → ℂ) (ξ : E d) : ‖𝓕 g ξ‖ ≤ ∫ x, ‖g x‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem sobolevOfCompactSupport : BaseLevel := by
  intro d g hg hgs
  unfold Hs nrm
  have hint : MeasureTheory.Integrable g := hg.integrable_of_hasCompactSupport hgs
  set B : ℝ := ∫ x, ‖g x‖ with hB
  have hBnn : 0 ≤ B := MeasureTheory.integral_nonneg fun x => norm_nonneg _
  have hI : MeasureTheory.Integrable
      (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    have : (Module.finrank ℝ (E d) : ℝ) = d := by simp
    rw [this]
    linarith
  have hI2 := (hI.const_mul (B ^ 2)).hasFiniteIntegral
  refine lt_of_le_of_lt (MeasureTheory.lintegral_mono fun ξ => ?_) hI2
  have ha : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
  have hom : om (-(d : ℝ) - 1) 0 0 ξ = (1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2) := by simp [om]
  have hsq : ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 =
      (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha.le]
    congr 1
    push_cast
    ring
  have h1 : ‖𝓕 g ξ‖ₑ ≤ ENNReal.ofReal B := by
    rw [← ofReal_norm_eq_enorm]
    exact ENNReal.ofReal_le_ofReal (norm_fourier_le_integral_norm g ξ)
  have h2 : ‖B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)‖ₑ =
      ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
    rw [← ofReal_norm_eq_enorm, Real.norm_of_nonneg (by positivity)]
  rw [h2, hom]
  calc ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2
      ≤ ENNReal.ofReal ((1 + ‖ξ‖ ^ 2) ^ ((-(d : ℝ) - 1) / 2)) ^ 2 * ENNReal.ofReal B ^ 2 := by
        gcongr
    _ = ENNReal.ofReal (B ^ 2 * (1 + ‖ξ‖ ^ 2) ^ (-(2 * ((d : ℝ) + 1)) / 2)) := by
        rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow hBnn,
          ← ENNReal.ofReal_mul (by positivity), hsq, mul_comm]

end ZetaZeros.D.EllReg
