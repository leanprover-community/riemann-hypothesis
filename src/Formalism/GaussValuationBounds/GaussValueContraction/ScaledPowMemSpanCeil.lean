module

public import Formalism.GaussValuationBounds.KapBound3
public import Formalism.GaussValuationBounds.GaussValueContraction.TruncationExponentBounds
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
import Mathlib.Tactic.Basify
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Topology.Sheaves.Init
import Std.Tactic.BVDecide.Normalize.Prop
public import Mathlib.RingTheory.Ideal.BigOperators

@[expose] public section

namespace Formalism.NOK

theorem scaledPowMemSpanCeil : Trunc := by
  intro A _ ℓ _ hℓ X u p y M j hj hq r
  have hnum := truncationExponentBounds ℓ hℓ y M j r hj
  set c := ⌈(r : ℝ) * ℓ / ((ℓ : ℝ) - 1)⌉₊ with hc
  set σ := sigNOK ℓ y M j with hσ
  have hL : (0 : ℝ) < (ℓ : ℝ) ^ (j - 1) := by positivity
  have hℓ1 : 1 ≤ ℓ := by omega
  by_cases hry : (ℓ - 1) * r < y
  · have h1 : (r : ℝ) * ℓ / ((ℓ : ℝ) - 1) ≤ σ := by
      have h2 := hnum.2
      have h3 : ((ℓ : ℝ) - 1) * r - y - (M : ℝ) / (ℓ : ℝ) ^ (j - 1) ≤ 0 := by
        have h4 : (((ℓ - 1) * r : ℕ) : ℝ) < y := by exact_mod_cast hry
        push_cast [Nat.cast_sub hℓ1] at h4
        have h5 : (0 : ℝ) ≤ M / (ℓ : ℝ) ^ (j - 1) := by positivity
        linarith
      rw [max_eq_left h3, sub_zero] at h2
      exact h2
    have hcs : c ≤ σ := Nat.ceil_le.mpr h1
    rw [← Nat.add_sub_cancel' hcs, pow_add, mul_assoc]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
  · push_neg at hry
    obtain ⟨m, hm⟩ : ∃ m, (ℓ - 1) * r = y + m := ⟨(ℓ - 1) * r - y, by omega⟩
    have hmR : ((ℓ : ℝ) - 1) * r - y = m := by
      have h6 := congrArg (Nat.cast : ℕ → ℝ) hm
      push_cast [Nat.cast_sub hℓ1] at h6
      linarith

    have key : (ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m ∈ Ideal.span {(ℓ : A) ^ c, X ^ M} := by
      obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hq
      rw [← hab, add_pow, Finset.mul_sum]
      refine Ideal.sum_mem _ fun k hk => ?_
      have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      by_cases hX : M ≤ r + ℓ ^ (j - 1) * (m - k)
      · have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            X ^ M * (X ^ (r + ℓ ^ (j - 1) * (m - k) - M) *
              ((ℓ : A) ^ σ * (a * ℓ) ^ k * b ^ (m - k) * (m.choose k : A))) := by
          rw [← mul_assoc (X ^ M), ← pow_add, Nat.add_sub_cancel' hX, pow_add, pow_mul]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · have hcs : c ≤ σ + k := by
          apply Nat.ceil_le.mpr
          have h2 := hnum.2
          have h5 : ((ℓ ^ (j - 1) * (m - k) : ℕ) : ℝ) < M := by
            exact_mod_cast (omega : ℓ ^ (j - 1) * (m - k) < M)
          push_cast [Nat.cast_sub hk'] at h5
          have h7 : (m : ℝ) - k ≤ M / (ℓ : ℝ) ^ (j - 1) := by
            rw [le_div_iff₀ hL]
            linarith [mul_comm ((ℓ : ℝ) ^ (j - 1)) ((m : ℝ) - k)]
          have hmax : max 0 (((ℓ : ℝ) - 1) * r - y - M / (ℓ : ℝ) ^ (j - 1)) ≤ k :=
            max_le (Nat.cast_nonneg _) (by rw [hmR]; linarith)
          push_cast
          linarith
        have e : (ℓ : A) ^ σ * X ^ r * ((a * ℓ) ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) * (m.choose k : A)) =
            (ℓ : A) ^ c * ((ℓ : A) ^ (σ + k - c) * (X ^ r * a ^ k * (b * X ^ (ℓ ^ (j - 1))) ^ (m - k) *
              (m.choose k : A))) := by
          rw [← mul_assoc ((ℓ : A) ^ c) ((ℓ : A) ^ (σ + k - c)), ← pow_add, Nat.add_sub_cancel' hcs]
          ring
        rw [e]
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
    have hj1 : j = (j - 1) + 1 := by omega
    have hprod : (∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        (∏ s ∈ Finset.range j, p s ^ y) * ((∏ s ∈ Finset.range (j - 1), p s ^ m) * p (j - 1) ^ m) := by
      rw [← Finset.prod_pow]
      have e1 : ∀ s, (p s ^ (ℓ - 1)) ^ r = p s ^ y * p s ^ m := fun s => by
        rw [← pow_mul, hm, pow_add]
      simp_rw [e1]
      rw [Finset.prod_mul_distrib]
      congr 1
      conv_lhs => rw [hj1]
      rw [Finset.prod_range_succ]
    have heq : (ℓ : A) ^ σ * (u * X * ∏ s ∈ Finset.range j, p s ^ (ℓ - 1)) ^ r =
        ((ℓ : A) ^ σ * X ^ r * p (j - 1) ^ m) * (∏ s ∈ Finset.range j, p s ^ y) *
          (u ^ r * ∏ s ∈ Finset.range (j - 1), p s ^ m) := by
      rw [mul_pow, mul_pow, hprod]
      ring
    rw [heq]
    refine Ideal.mul_mem_right _ _ ?_
    obtain ⟨α, β, hαβ⟩ := Ideal.mem_span_pair.mp key
    rw [← hαβ]
    exact Ideal.mem_span_pair.mpr ⟨α * ∏ s ∈ Finset.range j, p s ^ y, β, by ring⟩

end Formalism.NOK
