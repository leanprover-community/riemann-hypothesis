module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableRisingS
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeformedProductDerivativeTermNormLeUniform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdNormSq
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.WeightTwoSum
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory.WeightTwoSum.Bound

theorem eTerm_bound : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
    IsCMType φ → ∀ (m : I → ℕ) (σ : ℂ) (r : ℝ), 0 ≤ σ.re → r < 1 → ∃ C : ℝ, ∀ z : I → ℂ, (∀ i, ‖z i‖ ≤ r) →
      ∀ x : E, x ≠ 0 → ‖eTerm φ m σ z x‖ ≤ C * |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) := by
  intro E _ _ _ I _ φ hφ m σ r hσ hr
  have hr' : 0 < 1 - r := by linarith
  refine ⟨∏ i, (‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹) ^ (2 + m i) *
    (1 - r) ^ (-2 * σ.re)), fun z hz x hx => ?_⟩
  have hN : |(Algebra.norm ℚ x : ℝ)| ^ (-(1 + σ.re)) = ∏ i, (‖φ i x‖ ^ 2) ^ (-(1 + σ.re)) := by
    rw [← TermUnit.prod_norm_sq hφ x, Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  rw [hN, ← Finset.prod_mul_distrib, eTerm, norm_prod]
  refine Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) fun i _ => ?_
  have hp : 0 < ‖φ i x‖ := norm_pos_iff.2 ((map_ne_zero (φ i)).2 hx)
  have hl := GlobalTheory.DeformedSum.Bound.defCoord_lower φ z x i (hz i)
  have hd : 0 < ‖defCoord φ z x i‖ := lt_of_lt_of_le (mul_pos hr' hp) hl
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_conj, norm_inv,
    Complex.norm_cpow_eq_rpow_re_of_pos hd]
  set a := ‖φ i x‖ with ha
  set d := ‖defCoord φ z x i‖ with hdd
  have h1 : a ^ m i * d⁻¹ ^ (2 + m i) ≤ (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by
    have hinv : d⁻¹ ≤ (1 - r)⁻¹ * a⁻¹ := by
      rw [← mul_inv]; exact inv_anti₀ (mul_pos hr' hp) hl
    calc a ^ m i * d⁻¹ ^ (2 + m i) ≤ a ^ m i * ((1 - r)⁻¹ * a⁻¹) ^ (2 + m i) := by gcongr
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 * (a ^ m i * a⁻¹ ^ m i) := by rw [mul_pow, pow_add a⁻¹]; ring
      _ = (1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2 := by rw [← mul_pow, mul_inv_cancel₀ hp.ne', one_pow, mul_one]
  have h2 : d ^ ((-2 * σ).re) ≤ (1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re) := by
    rw [show (-2 * σ).re = -2 * σ.re by simp, ← Real.mul_rpow hr'.le hp.le]
    exact Real.rpow_le_rpow_of_nonpos (mul_pos hr' hp) hl (by linarith)
  have h3 : (a ^ 2) ^ (-(1 + σ.re)) = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by
    calc (a ^ 2) ^ (-(1 + σ.re)) = a ^ ((2 : ℝ) * (-(1 + σ.re))) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hp.le]; norm_num
      _ = a ^ (-(2 : ℝ)) * a ^ (-2 * σ.re) := by rw [← Real.rpow_add hp]; ring_nf
      _ = a⁻¹ ^ 2 * a ^ (-2 * σ.re) := by rw [Real.rpow_neg hp.le, inv_pow]; norm_num
  rw [h3]
  calc ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * a ^ m i * d⁻¹ ^ (2 + m i) * d ^ ((-2 * σ).re)
      = ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * (a ^ m i * d⁻¹ ^ (2 + m i)) * d ^ ((-2 * σ).re) := by
        ring
    _ ≤ ‖(-1 : ℂ) ^ m i * ∏ j ∈ Finset.range (m i), (2 + σ + j)‖ * ((1 - r)⁻¹ ^ (2 + m i) * a⁻¹ ^ 2) *
        ((1 - r) ^ (-2 * σ.re) * a ^ (-2 * σ.re)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left h1 (norm_nonneg _)) h2 (by positivity) (by positivity)
    _ = _ := by ring

end GlobalTheory.WeightTwoSum.Bound
