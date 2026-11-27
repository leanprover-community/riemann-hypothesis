module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LevelCohomology.BernoulliFourierRows
public import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Dynamics.FixedPoints.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Extracting a Bernoulli Fourier row by iterated Frobenius -/

@[expose] public section

namespace UpperTheory.V.X

open Finset

variable {K : Type*} [Field K]

/-- Adding the two evaluations at opposite frequencies isolates the even coefficients. -/
private lemma even_part_zero (F : ℕ → K) (n : ℕ) (z : K) (σ : K →+* K)
    (hF : ∀ i, σ (F i) = F i) (hσ : σ z = -z) (h2 : (2 : K) ≠ 0)
    (hs : ∑ i ∈ range (2 * n), F i * z ^ i = 0) :
    ∑ j ∈ range n, F (2 * j) * (z ^ 2) ^ j = 0 := by
  have hs' := congrArg σ hs
  simp only [map_sum, map_mul, map_pow, hF, hσ, map_zero] at hs'
  have add_evals (m : ℕ) :
      (∑ i ∈ range (2 * m), F i * z ^ i) + (∑ i ∈ range (2 * m), F i * (-z) ^ i) =
        2 * ∑ j ∈ range m, F (2 * j) * (z ^ 2) ^ j := by
    induction m with
    | zero => simp
    | succ m ih =>
      simp only [Nat.mul_succ, sum_range_succ, pow_succ _ (2 * m), pow_mul, neg_sq]
      linear_combination ih
  exact (mul_eq_zero.mp (by simpa only [hs, hs', add_zero] using (add_evals n).symm)).resolve_left h2

/-- The Frobenius sending the frequency to its negative fixes every coefficient.
Repeating the even-part extraction isolates the exponents divisible by `2^r`. -/
private lemma isolate_row {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] {d b c : ℕ}
    (hQ : ℓ ^ d = 1 + 4 * b * c) (hc : Odd c) (h2 : (2 : K) ≠ 0) (r : ℕ)
    (F : ℕ → K) (hF : ∀ i, iterateFrobenius K ℓ d (F i) = F i)
    (z : K) (hz : z ^ (2 ^ r * (2 * b)) = -1)
    (hs : ∑ i ∈ range (2 ^ r * (2 * b)), F i * z ^ i = 0) :
    ∑ j ∈ range (2 * b), F (2 ^ r * j) * (z ^ (2 ^ r)) ^ j = 0 := by
  induction r generalizing F z with
  | zero => simpa using hs
  | succ r ih =>
    obtain ⟨t, ht, hp⟩ := pow_two_pow_stride hQ hc r
    let σ := iterateFrobenius K ℓ (d * 2 ^ r)
    have hσ : σ z = -z := by
      change z ^ (ℓ ^ (d * 2 ^ r)) = -z
      rw [pow_mul, hp, pow_add, pow_one, show 4 * b * 2 ^ r = 2 ^ (r + 1) * (2 * b) by ring,
        pow_mul, hz, ht.neg_one_pow, mul_neg_one]
    have hfix (i : ℕ) : σ (F i) = F i := by
      dsimp only [σ]
      rw [iterateFrobenius_mul_apply]
      exact Function.IsFixedPt.iterate (hF i) _
    have hn : 2 ^ (r + 1) * (2 * b) = 2 * (2 ^ r * (2 * b)) := by ring
    rw [hn] at hs hz
    have h := ih (fun j ↦ F (2 * j)) (fun j ↦ hF (2 * j)) (z ^ 2) (by rwa [← pow_mul])
      (even_part_zero F _ z σ hfix hσ h2 hs)
    simpa only [← pow_mul, pow_succ' 2 r, mul_assoc] using h

/-- For Frobenius-fixed coefficient values, vanishing of the signed sum starting at
`a` implies vanishing of the Fourier row with stride `5^(2^k)` and length `T`. -/
theorem bernoulliFourierRow_eq_zero_of_sum_eq_zero {ℓ f : ℕ} [Fact ℓ.Prime] [CharP K ℓ]
    (d t k c a : ℕ) (φ : ZMod f → K) (z : K) (hc : Odd c) (h2 : (2 : K) ≠ 0)
    (hφ : ∀ x, φ x ^ (ℓ ^ d) = φ x) :
    let T := 2 ^ (t + 1)
    let h := 4 * 2 ^ k
    let N := h * (2 * T)
    ℓ ^ d = 1 + 2 * T * c → z ^ (N / 8) = -1 →
      (∑ j ∈ range (N / 8), bernoulliSignedCoeff φ N (a * 5 ^ j % N) * z ^ j) = 0 →
      bernoulliFourierRow φ N a (5 ^ (2 ^ k)) T (z ^ (2 ^ k)) = 0 := by
  intro T h N hQ hz hs
  have hT : T = 2 * 2 ^ t := pow_succ' _ _
  have hlen : N / 8 = 2 ^ k * T := by
    rw [show N = (2 ^ k * T) * 8 by dsimp [N, h]; ring, Nat.mul_div_cancel _ (by decide)]
  have hQ' : ℓ ^ d = 1 + 4 * 2 ^ t * c := by rw [hQ, hT]; ring
  let F (i : ℕ) := bernoulliSignedCoeff φ N (a * 5 ^ i % N)
  let σ := iterateFrobenius K ℓ d
  have hfix (x : ZMod f) : σ (φ x) = φ x := hφ x
  have hF (i : ℕ) : σ (F i) = F i := by
    simp [F, bernoulliSignedCoeff, apply_ite σ, hfix]
  rw [hlen, hT] at hz hs
  have hrow := isolate_row hQ' hc h2 k F hF z hz hs
  rw [bernoulliFourierRow, Fin.sum_univ_eq_sum_range
    (fun i : ℕ ↦ bernoulliSignedCoeff φ N (a * (5 ^ (2 ^ k)) ^ i % N) * (z ^ (2 ^ k)) ^ i)]
  simpa only [F, hT, ← pow_mul] using hrow

end UpperTheory.V.X
