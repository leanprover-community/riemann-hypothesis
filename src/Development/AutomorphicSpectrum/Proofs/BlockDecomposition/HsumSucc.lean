import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Mathlib

section
namespace GlobalTheory.CompanionTheory.HeckeMult

variable {R : Type*} [CommRing R]

theorem apply_prime_pow_mul (a c : ℕ → R) (h1 : a 1 = 1)
    (hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n)
    (hrec : ∀ p, p.Prime → ∀ n, 0 < n → a (p * (p * n)) = a p * a (p * n) - c p * a n)
    {p n : ℕ} (hp : p.Prime) (hn : 0 < n) (hpn : ¬ p ∣ n) (j : ℕ) :
    a (p ^ j * n) = a (p ^ j) * a n := by
  induction j using Nat.twoStepInduction with
  | zero => simp [h1]
  | one => simpa using hcop p hp n hn hpn
  | more j ih0 ih1 =>
    have hpj : 0 < p ^ j := pow_pos hp.pos j
    have e1 : p ^ (j + 2) * n = p * (p * (p ^ j * n)) := by ring
    have e2 : p ^ (j + 2) = p * (p * (p ^ j * 1)) := by ring
    have e3 : p ^ (j + 1) * n = p * (p ^ j * n) := by ring
    have e4 : p ^ (j + 1) = p * (p ^ j * 1) := by ring
    have r1 := hrec p hp (p ^ j * n) (Nat.mul_pos hpj hn)
    have r2 := hrec p hp (p ^ j * 1) (by simpa using hpj)
    rw [e3] at ih1
    rw [e1, r1, ih1, ih0]
    rw [e2, r2]
    rw [← e4, mul_one]
    rw [e4, mul_one]
    ring

theorem apply_mul_of_coprime (a c : ℕ → R) (h1 : a 1 = 1)
    (hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n)
    (hrec : ∀ p, p.Prime → ∀ n, 0 < n → a (p * (p * n)) = a p * a (p * n) - c p * a n)
    (m n : ℕ) (hmn : Nat.Coprime m n) : a (m * n) = a m * a n := by
  induction m using Nat.recOnPosPrimePosCoprime generalizing n with
  | prime_pow p k hp hk =>
    have hpn : ¬ p ∣ n := fun h =>
      hp.one_lt.ne' (Nat.eq_one_of_dvd_coprimes (Nat.Coprime.coprime_dvd_left (dvd_pow_self p hk.ne') hmn) dvd_rfl h)
    have hn : 0 < n := Nat.pos_of_ne_zero fun h => hpn (h ▸ dvd_zero p)
    exact apply_prime_pow_mul a c h1 hcop hrec hp hn hpn k
  | zero =>
    have : n = 1 := by simpa using hmn
    subst this
    simp [h1]
  | one => simp [h1]
  | coprime x y _ _ hxy ihx ihy =>
    have hx : Nat.Coprime x n := Nat.Coprime.coprime_dvd_left (dvd_mul_right x y) hmn
    have hy : Nat.Coprime y n := Nat.Coprime.coprime_dvd_left (dvd_mul_left y x) hmn
    rw [mul_assoc, ihx _ (Nat.Coprime.mul_right hxy hx), ihy _ hy, ihx _ hxy, mul_assoc]

end GlobalTheory.CompanionTheory.HeckeMult
end

section
open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HeckeEig

theorem hsum_succ (α β : ℂ) (j : ℕ) :
    ∑ i ∈ Finset.range (j + 1 + 1), α ^ i * β ^ (j + 1 - i) =
      α ^ (j + 1) + β * ∑ i ∈ Finset.range (j + 1), α ^ i * β ^ (j - i) := by
  rw [Finset.sum_range_succ, Finset.mul_sum, add_comm]
  congr 1
  · simp
  · apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [show j + 1 - i = (j - i) + 1 by omega, pow_succ]
    ring

theorem e2a : E2a := by
  intro k N χ a h
  obtain ⟨_, h1, hH⟩ := h
  have hcop : ∀ p, p.Prime → ∀ n, 0 < n → ¬ p ∣ n → a (p * n) = a p * a n := by
    intro p hp n _ hpn
    have := hH p n hp
    rw [if_neg hpn, add_zero] at this
    exact this.symm
  have hrec : ∀ p, p.Prime → ∀ n, 0 < n →
      a (p * (p * n)) = a p * a (p * n) - (χ p * (p : ℂ) ^ (k - 1)) * a n := by
    intro p hp n _
    have := hH p (p * n) hp
    rw [if_pos (dvd_mul_right p n), Nat.mul_div_cancel_left n hp.pos] at this
    rw [this]; ring
  refine ⟨fun m n hmn => GlobalTheory.CompanionTheory.HeckeMult.apply_mul_of_coprime a
      (fun p => χ p * (p : ℂ) ^ (k - 1)) h1 hcop hrec m n hmn, ?_⟩
  intro p hp α β hs hp' j
  induction j using Nat.twoStepInduction with
  | zero => simp [h1]
  | one =>
    simp [Finset.sum_range_succ]
    rw [← hs]
    ring
  | more j ih0 ih1 =>
    have r := hH p (p ^ (j + 1)) hp
    have hd : p ^ (j + 1) / p = p ^ j := by rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
    have hm : p * p ^ (j + 1) = p ^ (j + 2) := by ring
    rw [if_pos (dvd_pow_self p (Nat.succ_ne_zero j)), hd, hm] at r
    have e : a (p ^ (j + 2)) = a p * a (p ^ (j + 1)) - χ p * (p : ℂ) ^ (k - 1) * a (p ^ j) := by
      rw [r]; ring
    rw [e, ih1, ih0, ← hs, ← hp', show j + 2 = j + 1 + 1 by omega, hsum_succ α β (j + 1), hsum_succ α β j]
    ring

end GlobalTheory.CompanionTheory.HeckeEig
end
