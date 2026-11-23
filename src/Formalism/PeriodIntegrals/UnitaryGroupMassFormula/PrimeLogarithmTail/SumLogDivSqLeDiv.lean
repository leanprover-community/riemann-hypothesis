module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.PrimeLogarithmTail.SumLogBlock
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

namespace PI.TailWork

open Finset

theorem log_three_le : Real.log 3 ≤ 1.11 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 := Real.exp_one_gt_d9
  have h2 := Real.add_one_le_exp (0.11 : ℝ)
  have he : Real.exp 1.11 = Real.exp 1 * Real.exp 0.11 := by
    rw [← Real.exp_add]; norm_num
  rw [he]
  have := mul_le_mul h1.le h2 (by norm_num) (Real.exp_pos 1).le
  linarith

theorem log_five_le : Real.log 5 ≤ 1.62 := by
  have h25 : Real.log 25 = 2 * Real.log 5 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h24 : Real.log 24 = 3 * Real.log 2 + Real.log 3 := by
    rw [show (24 : ℝ) = 2 ^ 3 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have hq : Real.log 25 - Real.log 24 ≤ 25 / 24 - 1 := by
    rw [← Real.log_div (by norm_num) (by norm_num)]
    exact Real.log_le_sub_one_of_pos (by norm_num)
  linarith [Real.log_two_lt_d9, log_three_le]

theorem small_split (a : ℕ) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ a < p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
        + 2.04 / 7 := by
  classical
  rw [← Finset.sum_filter_add_sum_filter_not Q (fun p => p ∈ ({2, 3, 5} : Finset ℕ))]
  apply add_le_add
  · apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp ⊢
      exact ⟨hp.2, (hQ p hp.1).2⟩
    · intro p _ _
      exact div_nonneg (Real.log_natCast_nonneg p) (by positivity)
  · have h := tail_odd 3 le_rfl
      (Q.filter (fun p => p ∉ ({2, 3, 5} : Finset ℕ))) (by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpQ, hpT⟩ := hp
        have hpr := (hQ p hpQ).1
        refine ⟨hpr, ?_⟩
        by_contra hlt
        replace hlt : p < 2 * 3 + 1 := not_le.mp hlt
        have h2 := hpr.two_le
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hpT
        obtain ⟨n2, n3, n5⟩ := hpT
        interval_cases p
        all_goals first
          | exact (n2 rfl).elim
          | exact (n3 rfl).elim
          | exact (n5 rfl).elim
          | exact absurd hpr (by norm_num))
    norm_num at h ⊢
    linarith

private theorem sum_small_primes_log_div_sq_add_le (a : ℕ) (ha : a < 5) :
    ∑ p ∈ ({2, 3, 5} : Finset ℕ).filter (fun p => a < p), Real.log (p : ℝ) / (p : ℝ) ^ 2
      + 2.04 / 7 ≤ 2.04 / ((a : ℝ) + 1) := by
  have l2 := Real.log_two_lt_d9
  have l3 := log_three_le
  have l5 := log_five_le
  interval_cases a <;> norm_num [Finset.sum_filter, Finset.sum_insert] <;> linarith

theorem sum_log_div_sq_le_div (X : ℝ) (hX : 0 < X) (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime ∧ X < (p : ℝ)) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / X := by
  classical
  obtain ⟨m, hm⟩ : ∃ m, ⌊X⌋₊ = m := ⟨_, rfl⟩
  have hXm : X < (m : ℝ) + 1 := hm ▸ Nat.lt_floor_add_one X
  have hmX : (m : ℝ) ≤ X := hm ▸ Nat.floor_le hX.le
  have hlt : ∀ p ∈ Q, m < p := fun p hp => hm ▸ (Nat.floor_lt hX.le).2 (hQ p hp).2
  rcases lt_or_ge X 5 with h5 | h5
  · have hm5 : m < 5 := by exact_mod_cast (lt_of_le_of_lt hmX h5)
    have h1 := small_split m Q (fun p hp => ⟨(hQ p hp).1, hlt p hp⟩)
    have h2 := sum_small_primes_log_div_sq_add_le m hm5
    have hinv : 1 / ((m : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hXm.le
    have h3 : 2.04 / ((m : ℝ) + 1) ≤ 2.04 / X := by
      calc 2.04 / ((m : ℝ) + 1) = 2.04 * (1 / ((m : ℝ) + 1)) := by ring
        _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
        _ = 2.04 / X := by ring
    linarith
  · have hm5 : 5 ≤ m := by
      rw [← hm]; exact Nat.le_floor (by exact_mod_cast h5)
    obtain ⟨k, hk⟩ : ∃ k, (m + 1) / 2 = k := ⟨_, rfl⟩
    have hk3 : 3 ≤ k := by omega
    have hQk : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p := by
      intro p hp
      have hpr := (hQ p hp).1
      have hmp := hlt p hp
      refine ⟨hpr, ?_⟩
      rcases hpr.eq_two_or_odd with h | h
      · omega
      · omega
    have h := tail_odd k hk3 Q hQk
    have hkX : X ≤ 2 * (k : ℝ) + 1 := by
      have hn : m + 1 ≤ 2 * k + 1 := by omega
      have : (m : ℝ) + 1 ≤ 2 * (k : ℝ) + 1 := by exact_mod_cast hn
      linarith
    have hinv : 1 / (2 * (k : ℝ) + 1) ≤ 1 / X := one_div_le_one_div_of_le hX hkX
    calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := h
      _ = 2.04 * (1 / (2 * (k : ℝ) + 1)) := by ring
      _ ≤ 2.04 * (1 / X) := mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 2.04 / X := by ring

end PI.TailWork
