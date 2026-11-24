module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
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
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem zpow_congr_mod {K : Type} [Field K] {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1) {a b : ℤ}
    (h : a ≡ b [ZMOD M]) : ζ ^ a = ζ ^ b := by
  obtain ⟨k, hk⟩ := h.dvd
  have hz : ζ ^ (M : ℤ) = 1 := by
    rw [zpow_natCast, hζ]
  have hb : b = a + M * k := by
    omega
  rw [hb, zpow_add₀ (by rintro rfl; simp [zero_pow hM.ne'] at hζ), zpow_mul, hz, one_zpow, mul_one]

private theorem eisF_congr_mod {K : Type} [Field K] [CharZero K] (j : ℕ) {M : ℕ} {ζ : K} (hM : 0 < M) (hζ : ζ ^ M = 1)
    {a₁ b₁ a₂ b₂ : ℤ} (h₁ : a₁ ≡ b₁ [ZMOD M]) (h₂ : a₂ ≡ b₂ [ZMOD M]) (n : ℕ) :
    eisF j M ζ a₁ a₂ n = eisF j M ζ b₁ b₂ n := by
  unfold eisF
  split_ifs
  · unfold const0 frc
    have hd : ((M : ℤ) ∣ a₁ ↔ (M : ℤ) ∣ b₁) := by
      rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero, h₁]
    rw [zpow_congr_mod hM hζ h₂, show a₁ % (M : ℤ) = b₁ % M from h₁]
    simp only [hd]
  · unfold coefPos
    refine Finset.sum_congr rfl fun d _ => ?_
    have hc : ∀ x : ℤ, (x ≡ a₁ [ZMOD M] ↔ x ≡ b₁ [ZMOD M]) :=
      fun x => ⟨fun h => h.trans h₁, fun h => h.trans h₁.symm⟩
    simp only [hc, zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)),
      zpow_congr_mod hM hζ (h₂.mul_right (d : ℤ)).neg]

theorem UpperTheory.smoothedEisenstein_congr_of_modEq :
    ∀ {K : Type} [Field K] [CharZero K] (c : ℤ) (j M : ℕ) (ζ : K), 0 < M → ζ ^ M = 1 → ∀ {a₁ b₁ a₂ b₂ : ℤ}, a₁ ≡ b₁ [ZMOD M] → a₂ ≡ b₂ [ZMOD M] → smF c j M ζ a₁ a₂ = smF c j M ζ b₁ b₂ := by
  intro K _ _ c j M ζ hM hζ a₁ b₁ a₂ b₂ h₁ h₂
  funext n
  unfold smF
  rw [eisF_congr_mod j hM hζ h₁ h₂, eisF_congr_mod j hM hζ (h₁.mul_left c) (h₂.mul_left c)]
