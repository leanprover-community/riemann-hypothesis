module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_cg {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {x y : ℤ}
    (h : x ≡ y [ZMOD M]) : ζ ^ x = ζ ^ y := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  obtain ⟨k, hk⟩ := h.dvd
  have : y = x + (M : ℤ) * k := by linarith
  rw [this, zpow_add₀ h0, zpow_mul, zpow_natCast, hζ, one_zpow, mul_one]

private theorem eisF_shift {K : Type} [Field K] [CharZero K] (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ) (hM : 0 < M)
    (hζ : ζ ^ M = 1) (n : ℕ) :
    eisF j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * eisF j M ζ a₁ a₂ n := by
  have h0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hM.ne'] at hζ
    exact zero_ne_one hζ
  unfold eisF
  split_ifs with hn
  · subst hn
    simp only [Nat.cast_zero, mul_zero, zpow_zero, one_mul]
    unfold const0
    by_cases hd : (M : ℤ) ∣ a₁
    · have : ζ ^ (a₂ + e * a₁) = ζ ^ a₂ :=
        zpow_cg hM hζ (Int.ModEq.symm ((Int.modEq_iff_dvd).2 (by simpa using hd.mul_left e)))
      rw [this]
    · simp only [if_neg hd]
  · unfold coefPos
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hnd : (n : ℤ) = ((n / d : ℕ) : ℤ) * d := by
      rw [← Nat.cast_mul, Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hd)]
    rw [mul_sub]
    congr 1
    · split_ifs with h
      · have : ζ ^ ((a₂ + e * a₁) * d) = ζ ^ (e * (n : ℤ)) * ζ ^ (a₂ * d) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := ((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)
          refine h2.trans ?_
          rw [show (a₂ + e * ((n / d : ℕ) : ℤ)) * d = e * (((n / d : ℕ) : ℤ) * d) + a₂ * d by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]
    · split_ifs with h
      · have : ζ ^ (-((a₂ + e * a₁) * d)) = ζ ^ (e * (n : ℤ)) * ζ ^ (-(a₂ * d)) := by
          rw [← zpow_add₀ h0]
          apply zpow_cg hM hζ
          have h2 := (((h.symm.mul_left e).add_left a₂).mul_right (d : ℤ)).neg
          refine h2.trans ?_
          rw [show -((a₂ + e * -((n / d : ℕ) : ℤ)) * d) = e * (((n / d : ℕ) : ℤ) * d) + -(a₂ * d) by ring, ← hnd]
        rw [this]; ring
      · rw [mul_zero]

theorem UpperTheory.smoothedEisensteinCoeff_shift_second_index :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ e : ℤ), 0 < M → ζ ^ M = 1 → ∀ n : ℕ, smF c j M ζ a₁ (a₂ + e * a₁) n = ζ ^ (e * (n : ℤ)) * smF c j M ζ a₁ a₂ n := by
  intro K _ _ c j M ζ a₁ a₂ e hM hζ n
  unfold smF
  rw [show c * (a₂ + e * a₁) = c * a₂ + e * (c * a₁) by ring, eisF_shift j M ζ a₁ a₂ e hM hζ,
    eisF_shift j M ζ (c * a₁) (c * a₂) e hM hζ]
  ring
