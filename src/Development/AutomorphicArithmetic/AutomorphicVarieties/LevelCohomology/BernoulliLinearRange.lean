module

public import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.Ring

/-! # Dyadic parameters for the linear Bernoulli conductor range -/

@[expose] public section

namespace UpperTheory.V.X

/-- Above the equality layer, the improved cutoff supplies Fourier parameters
`T = 2^(t+1)` and `h = 4 * 2^k` satisfying `T * f < h`. The exact power of two in
`ℓ^d - 1` is `2*T`, and the dyadic conductor factors as `h * (2*T)`. -/
theorem exists_bernoulli_linear_range {ℓ d f n : ℕ} [Fact ℓ.Prime] (hd : 0 < d)
    (hfour : 4 ∣ ℓ ^ d - 1) (hf : Odd f)
    (hbound : f * 4 ^ (ℓ ^ d - 1).factorization 2 < 2 * 2 ^ n) :
    ∃ t k c : ℕ, n = k + t + 4 ∧ ℓ ^ d = 1 + 2 * 2 ^ (t + 1) * c ∧ Odd c ∧
      2 * 2 ^ (t + 1) ∣ 4 * 2 ^ k ∧ 2 ^ (t + 1) * f < 4 * 2 ^ k ∧
      2 ^ n = (4 * 2 ^ k) * (2 * 2 ^ (t + 1)) := by
  let e := (ℓ ^ d - 1).factorization 2
  have hprime : ℓ.Prime := Fact.out
  have hpos := Nat.one_lt_pow hd.ne' hprime.one_lt
  have hne : ℓ ^ d - 1 ≠ 0 := by lia
  have he : 2 ≤ e := (Nat.prime_two.pow_dvd_iff_le_factorization hne).mp hfour
  let c := (ℓ ^ d - 1) / 2 ^ e
  have hc : Odd c := Nat.coprime_two_left.mp (Nat.coprime_ordCompl Nat.prime_two hne)
  have hfactor : 2 ^ e * c = ℓ ^ d - 1 := Nat.ordProj_mul_ordCompl_eq_self _ 2

  have hsize : 2 * e ≤ n := by
    have hs : 4 ^ e < 2 * 2 ^ n := (Nat.le_mul_of_pos_left _ hf.pos).trans_lt hbound
    rw [show 4 ^ e = 2 ^ (2 * e) by rw [pow_mul]; rfl, ← pow_succ',
      Nat.pow_lt_pow_iff_right Nat.one_lt_two] at hs
    lia

  obtain ⟨t, ht⟩ : ∃ t, e = t + 2 := ⟨e - 2, by lia⟩
  obtain ⟨k, hn⟩ : ∃ k, n = k + t + 4 := ⟨n - t - 4, by lia⟩
  have hstride : 2 ^ e = 2 * 2 ^ (t + 1) := by rw [ht, pow_succ']
  have hrow : 4 * 2 ^ k = 2 ^ (k + 2) := by rw [pow_add]; lia
  have hN : 2 ^ n = (4 * 2 ^ k) * (2 * 2 ^ (t + 1)) := by
    rw [hn, pow_add, pow_add, pow_succ]
    ring
  refine ⟨t, k, c, hn, ?_, hc, ?_, ?_, hN⟩
  · rw [← hstride]
    lia
  · rw [← hstride, hrow]
    exact pow_dvd_pow 2 (by lia)
  · have hsquare : 4 ^ e = (2 ^ e) ^ 2 := by rw [← pow_mul, Nat.mul_comm e 2, pow_mul]; rfl
    apply Nat.lt_of_mul_lt_mul_right (a := 4 * 2 ^ (t + 1))
    calc
      _ = f * 4 ^ e := by rw [hsquare, hstride]; ring
      _ < 2 * 2 ^ n := hbound
      _ = _ := by rw [hN]; ring

end UpperTheory.V.X
