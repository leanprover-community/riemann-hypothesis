module

public import GroundTheory.AutomorphicForms.PartialDifferential.Sobolev
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace GroundTheory.Automorphic.Sobolev

open TemperedDistribution MeasureTheory FourierTransform
open scoped SchwartzMap ENNReal ContDiff

noncomputable section

set_option linter.unusedSectionVars false

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]


variable {m : E → ℂ} {C s t : ℝ}


section Convolution



end Convolution

section Mollifier

theorem norm_fourier_le_integral (ψ : 𝓢(E, ℂ)) (ξ : E) :
    ‖(𝓕 ψ : 𝓢(E, ℂ)) ξ‖ ≤ ∫ x, ‖ψ x‖ := by
  rw [SchwartzMap.fourier_coe]
  exact VectorFourier.norm_fourierIntegral_le_integral_norm _ _ _ _ _

theorem exists_norm_le_weight (χ : 𝓢(E, ℂ)) (r : ℝ) :
    ∃ C, ∀ ξ : E, ‖χ ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
  set n : ℕ := ⌈-r / 2⌉₊
  refine ⟨2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ), fun ξ ↦ ?_⟩
  have h0 : ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ 0 0 χ := by
    have := SchwartzMap.le_seminorm ℂ 0 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have h1 : ‖ξ‖ ^ (2 * n) * ‖χ ξ‖ ≤ SchwartzMap.seminorm ℂ (2 * n) 0 χ := by
    have := SchwartzMap.le_seminorm ℂ (2 * n) 0 χ ξ
    simpa [norm_iteratedFDeriv_zero] using this
  have hb : (1 : ℝ) ≤ 1 + ‖ξ‖ ^ 2 := by nlinarith [sq_nonneg ‖ξ‖]
  have hpow : (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
    rcases le_total (‖ξ‖ ^ 2) 1 with h | h
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ 2 ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by
            have : 0 ≤ (‖ξ‖ ^ 2) ^ n := by positivity
            nlinarith [pow_pos (two_pos (α := ℝ)) n]
    · calc (1 + ‖ξ‖ ^ 2) ^ n ≤ (2 * ‖ξ‖ ^ 2) ^ n := by
            apply pow_le_pow_left₀ (by positivity); linarith
        _ = 2 ^ n * (‖ξ‖ ^ 2) ^ n := by rw [mul_pow]
        _ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) := by gcongr; linarith
  have key : (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤
      2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) := by
    calc (1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖ ≤ 2 ^ n * (1 + (‖ξ‖ ^ 2) ^ n) * ‖χ ξ‖ := by gcongr
      _ = 2 ^ n * (‖χ ξ‖ + ‖ξ‖ ^ (2 * n) * ‖χ ξ‖) := by rw [pow_mul]; ring
      _ ≤ _ := by gcongr
  have hpos : 0 < (1 + ‖ξ‖ ^ 2) ^ n := by positivity
  have hexp : (1 + ‖ξ‖ ^ 2) ^ (-(n : ℝ)) ≤ (1 + ‖ξ‖ ^ 2) ^ (r / 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hb
    have := Nat.le_ceil (-r / 2)
    linarith
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast] at hexp
  calc ‖χ ξ‖ = ((1 + ‖ξ‖ ^ 2) ^ n * ‖χ ξ‖) * ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by
        field_simp
    _ ≤ 2 ^ n * (SchwartzMap.seminorm ℂ 0 0 χ + SchwartzMap.seminorm ℂ (2 * n) 0 χ) *
        ((1 + ‖ξ‖ ^ 2) ^ n)⁻¹ := by gcongr
    _ ≤ _ := by
        gcongr

namespace SobolevSpace

variable {s : ℝ}

@[simp] theorem toDistribution_sub (u v : SobolevSpace E F s) :
    toDistribution (u - v) = toDistribution u - toDistribution v := rfl

end SobolevSpace

end Mollifier

end

end GroundTheory.Automorphic.Sobolev
