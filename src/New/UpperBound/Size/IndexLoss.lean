module

import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Data.Rat.Cast.OfScientific
public import New.UpperBound.Size.Estimates
import New.Reduction.PrimeSums
import New.Reduction.Data.LevelAndTwists
import New.Reduction.Data.Sizes
import New.UpperBound.Objects.Rows

/-!
# The index cost of the local sublattices

The normalized Poincaré images use one sublattice at every prime. At a small exceptional
prime its colength is bounded using the number of a-places on one side of the marked pairs.
At the level prime it is bounded by the last-variable degree. The other primes have index one.

* `New.Data.indexLoss` is the local determinant exponent per source dimension.
* `New.Data.sum_indexLoss_mul_log_le` bounds its logarithmically weighted sum. A factorial
  estimate counts the exceptional primes, and the size of the source rank absorbs the level term.
-/

@[expose] public section

noncomputable section

open Nat Finset Real

namespace New

/-- For primes `p ≤ n` in a finite set, `∑ log p / p ≤ 2 log n`. The multiples of `p` in `n!`
provide the lower bound `⌊n / p⌋` for its multiplicity. -/
theorem sum_prime_log_div_le_two_mul_log (n : ℕ) (hn : 0 < n) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ n) : ∑ p ∈ s, Real.log p / p ≤ 2 * Real.log n := by
  have mult (p : ℕ) (hp : p.Prime) : n / p ≤ n.factorial.factorization p := by
    rw [Nat.factorization_factorial (b := Nat.log p n + 2) hp (by omega)]
    simpa using (Finset.single_le_sum (f := fun i ↦ n / p ^ i) (fun _ _ ↦ Nat.zero_le _)
      (show 1 ∈ Finset.Ico 1 (Nat.log p n + 2) by simp))
  -- Every selected prime occurs in the factorial.
  have support : s ⊆ n.factorial.factorization.support := by
    intro p hp
    obtain ⟨hprime, hle⟩ := hs p hp
    exact Finsupp.mem_support_iff.2 ((Nat.div_pos hle hprime.pos).trans_le (mult p hprime)).ne'
  -- For `p ≤ n`, the quotient is at least one and the remainder is smaller than `p`.
  have cover (p : ℕ) (hp : p ∈ s) : (n : ℝ) / p ≤ 2 * n.factorial.factorization p := by
    obtain ⟨hprime, hle⟩ := hs p hp
    have hmay : p ≤ p * (n / p) := Nat.le_mul_of_pos_right p (Nat.div_pos hle hprime.pos)
    have hnq : n ≤ 2 * (n / p) * p := by
      rw [show 2 * (n / p) * p = p * (n / p) + p * (n / p) by ring]
      have := Nat.mod_lt n hprime.pos
      have := Nat.mod_add_div n p
      omega
    apply (div_le_iff₀ (by exact_mod_cast hprime.pos)).2
    exact_mod_cast hnq.trans (by gcongr; exact mult p hprime)
  have hpos : (0 : ℝ) < n := by exact_mod_cast hn
  apply le_of_mul_le_mul_left (a := (n : ℝ)) _ hpos
  calc
    (n : ℝ) * ∑ p ∈ s, Real.log p / p = ∑ p ∈ s, (n / (p : ℝ)) * Real.log p := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring
    _ ≤ ∑ p ∈ s, 2 * (n.factorial.factorization p * Real.log p) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (cover p hp) (by positivity)
    _ ≤ 2 * Real.log n.factorial := by
      rw [← Finset.mul_sum, Real.log_nat_eq_sum_factorization, Finsupp.sum]
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum_of_subset_of_nonneg support fun _ _ _ ↦ by positivity) (by norm_num)
    _ ≤ n * (2 * Real.log n) := by
      have hlog : Real.log (n.factorial : ℝ) ≤ Real.log ((n : ℝ) ^ n) :=
        Real.log_le_log (by positivity) (by exact_mod_cast Nat.factorial_le_pow n)
      rw [Real.log_pow] at hlog
      linarith

end New

namespace New.Data

open Finset Real

variable {P : Parameters} (D : Data P)

open scoped Classical in
/-- The local index price. A marked exceptional prime uses the product of Hecke operators.
At the level prime the degree of the last variable bounds the index. -/
noncomputable def indexLoss (p : ℕ) : ℝ :=
  (if p ∈ D.smallNonsplitPrimes ∧ D.IsExceptional p then
    (7 : ℝ) * #D.aPlaces * D.a / p + (1 : ℝ) / D.m else 0) +
  if p = D.N then (D.ϱ + 1 + 1 : ℝ) * D.f * D.a / D.k else 0

/-- The local logarithmic index allowance is nonnegative at every prime. -/
lemma indexLoss_nonneg (p : ℕ) : 0 ≤ D.indexLoss p := by
  unfold indexLoss
  split_ifs <;> positivity

private lemma level_index_scale : (P.q₀.totient : ℝ) * (D.ϱ + 1 + 1) * Real.log D.N ≤ D.k := by
  have hφ : (P.q₀.totient : ℝ) ≤ P.constantBound := le_constantBound.2.2.2
  have hs : (D.ϱ + 1 + 1 : ℝ) ≤ D.m := by
    exact_mod_cast (show D.ϱ + 1 + 1 ≤ D.m by have := D.m_eq_two_mul_varrho_add_two; omega)
  have hN : 0 ≤ Real.log D.N := (HasLogBound.pos D).le
  calc _ ≤ P.constantBound * (D.m : ℝ) * Real.log D.N :=
         mul_le_mul_of_nonneg_right
           (mul_le_mul hφ hs (by positivity) (le_trans (by positivity) hφ)) hN
       _ ≤ _ := D.le_of_hasLogBound (by
         simp
         linarith [D.mul_log_logB_le_logX, D.constantBound_le, (le_constantBound (P := P)).1])

private lemma level_index_mul_log_le :
    ((D.ϱ + 1 + 1 : ℝ) * D.f * D.a / D.k) * Real.log D.N ≤ (#D.aPlaces : ℝ) * D.a := by
  have hk : 0 < (D.k : ℝ) := HasLogBound.pos D
  rw [div_mul_eq_mul_div, div_le_iff₀ hk, D.f_eq_card_aPlaces_mul, Nat.cast_mul]
  calc
    _ = ((#D.aPlaces : ℝ) * D.a) * ((P.q₀.totient : ℝ) * (D.ϱ + 1 + 1) * Real.log D.N) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left D.level_index_scale (by positivity)

/-- For the exceptional primes below the cutoff, the terms in `log p / p` cost at most
`14 · #aPlaces · a · log x₁`, and the ceiling terms together cost at most `#aPlaces · a`. -/
private lemma exceptional_index_sum_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p < D.natX₁) :
    ∑ p ∈ S, ((7 : ℝ) * #D.aPlaces * D.a / p + 1 / D.m) * Real.log p ≤
      14 * (#D.aPlaces : ℝ) * D.a * D.logX₁ + #D.aPlaces * D.a := by
  let Q : ℝ := #D.aPlaces * D.a
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hL : 0 ≤ D.logX₁ := (HasLogBound.pos D).le
  have hlog : Real.log (D.natX₁ : ℝ) = D.logX₁ := by rw [← D.exp_logX₁, Real.log_exp]
  have hcard : (#S : ℝ) ≤ D.x₁ := by
    have hs : S ⊆ range D.natX₁ := fun p hp ↦ mem_range.2 (hS p hp).2
    rw [show D.x₁ = D.natX₁ from D.exp_logX₁]
    exact_mod_cast (show #S ≤ D.natX₁ by simpa using card_le_card hs)
  -- The prime factorial estimate controls the first part of each exceptional cost.
  have hprimes : ∑ p ∈ S, Real.log p / p ≤ 2 * D.logX₁ := by
    have hn : 0 < D.natX₁ := by
      exact_mod_cast (D.exp_logX₁ ▸ Real.exp_pos D.logX₁)
    simpa only [hlog] using New.sum_prime_log_div_le_two_mul_log D.natX₁ hn S
      (fun p hp ↦ ⟨(hS p hp).1, (hS p hp).2.le⟩)
  have hlogs : ∑ p ∈ S, Real.log p ≤ #S * D.logX₁ := by
    calc _ ≤ ∑ _p ∈ S, D.logX₁ := by
          apply sum_le_sum
          intro p hp
          rw [← hlog]
          exact Real.log_le_log (by exact_mod_cast (hS p hp).1.pos)
            (by exact_mod_cast (hS p hp).2.le)
         _ = _ := by simp
  -- The ceiling in the collision exponent contributes at most `1 / m` per prime.
  have hextra : (1 / (D.m : ℝ)) * ∑ p ∈ S, Real.log p ≤ Q := by
    have hc : (1 : ℝ) ≤ #D.aPlaces := by
      exact_mod_cast (Finset.card_pos.2 (show D.aPlaces.Nonempty from ⟨1, by simp [aPlaces]⟩))
    calc _ ≤ (1 / (D.m : ℝ)) * (D.x₁ * D.logX₁) :=
          mul_le_mul_of_nonneg_left (hlogs.trans (mul_le_mul_of_nonneg_right hcard hL))
            (by positivity)
         _ ≤ D.a := D.le_of_hasLogBound (by
           simp
           linarith [D.logX₁_le_logB, D.log_logX₁_le_log_logB, D.mul_log_logB_le_logX,
             D.constantBound_le, (le_constantBound (P := P)).1])
         _ ≤ Q := le_mul_of_one_le_left (by positivity) hc
  calc
    _ = 7 * Q * (∑ p ∈ S, Real.log p / p) + (1 / (D.m : ℝ)) * ∑ p ∈ S, Real.log p := by
      rw [Finset.mul_sum, Finset.mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun p _ ↦ by dsimp [Q]; ring
    _ ≤ 7 * Q * (2 * D.logX₁) + Q :=
      add_le_add (mul_le_mul_of_nonneg_left hprimes (by positivity)) hextra
    _ = _ := by dsimp [Q]; ring

/-- The logarithmically weighted determinant costs over any finite set of natural numbers
sum to at most `16 · #aPlaces · a · log x₁`. -/
theorem sum_indexLoss_mul_log_le (U : Finset ℕ) :
    ∑ p ∈ U, D.indexLoss p * Real.log p ≤ 16 * (#D.aPlaces : ℝ) * D.a * D.logX₁ := by
  classical
  let S := U.filter fun p ↦ p ∈ D.smallNonsplitPrimes ∧ D.IsExceptional p
  let Q : ℝ := #D.aPlaces * D.a
  let cost (p : ℕ) : ℝ := (7 : ℝ) * #D.aPlaces * D.a / p + 1 / D.m
  let level : ℝ := (D.ϱ + 1 + 1 : ℝ) * D.f * D.a / D.k
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hL : 1 ≤ D.logX₁ := by
    linarith [(le_constantBound (P := P)).1, D.constantBound_le, D.mul_log_logB_le_logX,
      D.logX_le_logX₁]
  have hS (p : ℕ) (hp : p ∈ S) : p.Prime ∧ p < D.natX₁ := by
    have h : p < D.natX₁ ∧ p.Prime ∧ chiK P.d p ≠ 1 := by
      simpa [smallNonsplitPrimes, x₁, D.exp_logX₁] using (mem_filter.1 hp).2.1
    exact ⟨h.2.1, h.1⟩
  calc
    _ = (∑ p ∈ S, cost p * Real.log p) + (if D.N ∈ U then level * Real.log D.N else 0) := by
      change ∑ p ∈ U, ((if p ∈ D.smallNonsplitPrimes ∧ D.IsExceptional p then cost p else 0) +
        (if p = D.N then level else 0)) * Real.log p = _
      simp only [add_mul, ite_mul, zero_mul, sum_add_distrib, S, sum_filter]
      simp
    _ ≤ (14 * Q * D.logX₁ + Q) + Q := by
      refine _root_.add_le_add ?_ ?_
      · simpa only [Q, cost, mul_assoc] using D.exceptional_index_sum_le S hS
      · split_ifs
        · exact D.level_index_mul_log_le
        · exact hQ
    _ ≤ _ := by
      dsimp [Q] at *
      nlinarith only [mul_le_mul_of_nonneg_left hL hQ]

end New.Data

end
