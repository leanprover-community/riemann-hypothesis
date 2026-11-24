module

public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EvenThetaTwoTorsionBasicPropertiesStatement
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

@[expose] public section

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators

namespace GlobalTheory.EvenTheta

theorem IsLat.evenTheta_translate_sq_eq_sigmaStar : ∀ Λ : AddSubgroup ℂ, IsLat Λ → ∀ t₀ : ℂ, t₀ ∉ Λ → 2 * t₀ ∈ Λ → ∀ t, t ∉ Λ → ∀ z, U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (GL3Theta.th0 Λ t₀) z ^ 2 = -(U1 Λ (2 * t) (sgStar Λ) z * sgStar Λ z) + (wpF Λ t - wpF Λ t₀) * U1 Λ t (sgStar Λ) 0 ^ 2 * U1 Λ t (sgStar Λ) z ^ 2 := by
  intro Λ h t₀ h0 h2 t ht z
  have hsq := (GlobalTheory.T.th0_zero_even_sq_zeros_and_periodicity Λ h t₀ h0 h2).2.2.2.1 (z + t)
  have hσ := (h.sg_eq_zero t).not.2 ht
  rw [h.sqTh_sub h0 ht] at hsq
  have hs : sqTh Λ t (z + t) * sgStar Λ t ^ 2 = -(sgStar Λ (z + 2 * t) * sgStar Λ z) := by
    rw [sqTh, div_mul_cancel₀ _ (pow_ne_zero 2 hσ), show t - (z + t) = -z by ring, h.sg_neg,
      show t + (z + t) = z + 2 * t by ring]
    ring
  simp only [U1, zero_add, mul_pow]
  rw [hsq]
  have he : Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) (2 * t) / ↑(area Λ) -
        ↑Real.pi * (2 * t) * (starRingEnd ℂ) (2 * t) / (2 * ↑(area Λ))) =
      Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 *
      Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
        ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) ^ 2 := by
    rw [← mul_pow, ← Complex.exp_add, sq, ← Complex.exp_add, map_mul, map_ofNat]
    congr 1
    ring
  rw [he]
  generalize Complex.exp (-↑Real.pi * 0 * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = a
  generalize Complex.exp (-↑Real.pi * z * (starRingEnd ℂ) t / ↑(area Λ) -
    ↑Real.pi * t * (starRingEnd ℂ) t / (2 * ↑(area Λ))) = b
  linear_combination a ^ 2 * b ^ 2 * hs

end GlobalTheory.EvenTheta
