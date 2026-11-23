module

public import Development.AbelianVarietyTheory.Definitions.Foundations.Integral
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
import Development.AbelianVarietyTheory.Definitions.Foundations.EeProd
import Development.AbelianVarietyTheory.Definitions.Foundations.ExpUpper
import Development.AbelianVarietyTheory.Definitions.Foundations.Mdl
import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.SiegelFixedPoints.IsThBIff

@[expose] public section

open scoped MatrixGroups Matrix
open GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.Glue GlobalTheory.KummerEisensteinGalois UpperTheory.Kd.L

private theorem UpperTheory.ring_hom_eisenstein_coeff {K : Type} [Field K] [CharZero K] (s : K →+* K) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ)
    (h : s (ζ ^ a₂) = ζ ^ b₂) (n : ℕ) : s (eisF j M ζ a₁ a₂ n) = eisF j M ζ a₁ b₂ n := by
  have hz : ∀ k : ℤ, s (ζ ^ (a₂ * k)) = ζ ^ (b₂ * k) := by
    intro k
    rw [zpow_mul, zpow_mul, map_zpow₀, h]
  have hz' : ∀ k : ℤ, s (ζ ^ (-(a₂ * k))) = ζ ^ (-(b₂ * k)) := by
    intro k
    rw [zpow_neg, zpow_neg, map_inv₀, hz]
  unfold eisF const0 coefPos
  split_ifs
  · simp only [map_div₀, map_mul, map_add (f := _), map_sub, map_one, map_ofNat, h]
  · simp only [map_ratCast]
  · simp only [map_neg, map_ratCast]
  · set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_sub]
    refine Finset.sum_congr rfl fun d _ => ?_
    congr 1
    · split_ifs
      · rw [map_mul, map_pow, map_div₀, map_natCast, map_natCast, hz]
      · exact map_zero s
    · split_ifs
      · rw [map_mul, map_pow, map_neg, map_div₀, map_natCast, map_natCast, hz']
      · exact map_zero s

theorem UpperTheory.ringHom_apply_smoothedEisensteinCoeff :
    ∀ {K : Type} [Field K] [CharZero K] (s : K →+* K) (c : ℤ) (j M : ℕ) (ζ : K) (a₁ a₂ b₂ : ℤ), ζ ≠ 0 → s (ζ ^ a₂) = ζ ^ b₂ → ∀ n : ℕ, s (smF c j M ζ a₁ a₂ n) = smF c j M ζ a₁ b₂ n := by
  intro K _ _ s c j M ζ a₁ a₂ b₂ _ h n
  have hc : s (ζ ^ (c * a₂)) = ζ ^ (c * b₂) := by
    rw [mul_comm c a₂, mul_comm c b₂, zpow_mul, zpow_mul, map_zpow₀, h]
  unfold smF
  rw [map_sub, map_mul, map_mul, UpperTheory.ring_hom_eisenstein_coeff s j M ζ a₁ a₂ b₂ h n,
    UpperTheory.ring_hom_eisenstein_coeff s j M ζ (c * a₁) (c * a₂) (c * b₂) hc n]
  simp only [map_pow, map_zpow₀, map_intCast]
