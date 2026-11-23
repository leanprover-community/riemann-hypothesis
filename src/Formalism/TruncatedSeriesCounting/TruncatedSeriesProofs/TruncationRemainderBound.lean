module

public import Formalism.TruncatedSeriesCounting.StatementX
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
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

namespace Formalism.TruncatedSeriesCounting.X

theorem truncation_remainder_bound : TruncRem1 := by
  intro R _ ℓ hℓ π₀ y K c hc
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have hc0 : c = 0 := by push_cast at hc; omega
    subst hc0
    rw [pow_zero]
    exact Ideal.subset_span (Set.mem_insert _ _) |> fun h => by simpa using h
  · obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
    have e : (π₀ * (π₀ + (ℓ : R)) ^ (ℓ - 1)) ^ (y' + 1) =
        π₀ * ((π₀ + (ℓ : R)) + (-(ℓ : R))) ^ y' * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
      rw [show (π₀ + (ℓ : R)) + (-(ℓ : R)) = π₀ by ring, mul_pow, ← pow_mul, pow_succ]
      ring
    rw [e, add_pow (π₀ + (ℓ : R)) (-(ℓ : R)) y', Finset.mul_sum, Finset.sum_mul]
    refine Ideal.sum_mem _ fun m hm => ?_
    have hm' : m ≤ y' := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    by_cases hj : c ≤ y' - m
    · have h1 : (-(ℓ : R)) ^ (y' - m) = (ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) := by
        have hsplit : (ℓ : R) ^ (y' - m) = (ℓ : R) ^ c * (ℓ : R) ^ (y' - m - c) := by
          rw [← pow_add]
          congr 1
          omega
        rw [neg_pow, hsplit]
        ring
      have hmem : (ℓ : R) ^ c ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert _ _)
      rw [h1]
      have : π₀ * ((π₀ + ↑ℓ) ^ m * ((ℓ : R) ^ c * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c))) * ↑(y'.choose m)) *
          (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) = (ℓ : R) ^ c * (π₀ * (π₀ + ↑ℓ) ^ m * ((-1) ^ (y' - m) * (ℓ : R) ^ (y' - m - c)) *
          ↑(y'.choose m) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1))) := by ring
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem
    · have hK : K ≤ m + (ℓ - 1) * (y' + 1) := by
        push_neg at hj
        have h2 : (c : ℤ) ≤ (ℓ : ℤ) * ((y' + 1 : ℕ) : ℤ) - K := hc
        push_cast at h2
        have h3 : (c : ℤ) ≥ (y' : ℤ) - m + 1 := by omega
        zify [hℓ]
        nlinarith [h2, h3]
      have hmem : π₀ * (π₀ + (ℓ : R)) ^ K ∈ Ideal.span {(ℓ : R) ^ c, π₀ * (π₀ + (ℓ : R)) ^ K} :=
        Ideal.subset_span (Set.mem_insert_of_mem _ rfl)
      have : π₀ * ((π₀ + ↑ℓ) ^ m * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * (π₀ + ↑ℓ) ^ ((ℓ - 1) * (y' + 1)) =
          π₀ * (π₀ + (ℓ : R)) ^ K * ((π₀ + ↑ℓ) ^ (m + (ℓ - 1) * (y' + 1) - K) * (-(ℓ : R)) ^ (y' - m) *
            ↑(y'.choose m)) := by
        have e2 : (π₀ + (ℓ : R)) ^ K * (π₀ + (ℓ : R)) ^ (m + (ℓ - 1) * (y' + 1) - K) =
            (π₀ + (ℓ : R)) ^ m * (π₀ + (ℓ : R)) ^ ((ℓ - 1) * (y' + 1)) := by
          rw [← pow_add, ← pow_add, Nat.add_sub_cancel' hK]
        linear_combination (π₀ * (-(ℓ : R)) ^ (y' - m) * ↑(y'.choose m)) * e2.symm
      rw [this]
      exact Ideal.mul_mem_right _ _ hmem

end Formalism.TruncatedSeriesCounting.X
