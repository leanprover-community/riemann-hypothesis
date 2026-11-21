import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.ThetaDiff
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicPrimeIntervals.SmallLoop

section
namespace PI.PrimesDyadicRS.K

theorem run1 : run 32768 1612 32766 2 1 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

section
namespace PI.PrimesDyadicRS.K

theorem run2 : run 65536 3030 32768 32768 1612 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

section
namespace PI.PrimesDyadicRS.K

theorem run3 : run 98304 4388 32768 65536 3030 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

section
namespace PI.PrimesDyadicRS.K

theorem run4 : run 131072 5709 32768 98304 4388 = true := by decide +kernel

end PI.PrimesDyadicRS.K
end

section
namespace PI.PrimesDyadicRS.K

open Real

theorem gcd_fact_iff {m k : ℕ} (h2 : 2 ≤ m) (hk : k < m) (hm : m < (k + 1) ^ 2) :
    Nat.gcd m k.factorial = 1 ↔ m.Prime := by
  constructor
  · intro hg
    by_contra hp
    have hmf := Nat.minFac_sq_le_self (by omega) hp
    have hle : m.minFac ≤ k := by
      by_contra hc
      push Not at hc
      have : (k + 1) ^ 2 ≤ m.minFac ^ 2 := Nat.pow_le_pow_left hc 2
      omega
    have hd : m.minFac ∣ Nat.gcd m k.factorial :=
      Nat.dvd_gcd (Nat.minFac_dvd m) (Nat.dvd_factorial (Nat.minFac_pos m) hle)
    rw [hg, Nat.dvd_one, Nat.minFac_eq_one_iff] at hd
    omega
  · intro hp
    exact (Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => by
      have := (Nat.Prime.dvd_factorial hp).1 hd
      omega

theorem pr_eq {Q m : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ m) (hm : m < 131769) :
    pr Q m = if m.Prime then 1 else 0 := by
  by_cases h1 : m ≤ 362
  · have e := gcd_fact_iff (k := m - 1) h2 (by omega)
      (by rw [show m - 1 + 1 = m by omega]; nlinarith)
    simp only [pr, if_pos h1]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]
  · have e := gcd_fact_iff (k := 362) h2 (by omega) (by norm_num; omega)
    simp only [pr, if_neg h1, hQ]
    by_cases hp : m.Prime
    · rw [if_pos (e.2 hp), if_pos hp]
    · rw [if_neg (fun h => hp (e.1 h)), if_neg hp]

theorem pc_succ (n : ℕ) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + if (n + 1).Prime then 1 else 0 := by
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]

def D (h : ℕ) : ℕ := Nat.primeCounting h - Nat.primeCounting (h / 2)

theorem D_two : D 2 = 1 := by
  have h1 := pc_succ 1
  rw [Nat.primeCounting_one, if_pos Nat.prime_two] at h1
  simp only [D, show (2 : ℕ) / 2 = 1 by norm_num, Nat.primeCounting_one]
  omega

theorem nxt_eq {Q h : ℕ} (hQ : Q = Nat.factorial 362) (h2 : 2 ≤ h) (hh : h < 131072) :
    nxt Q h (D h) = D (h + 1) := by
  have hA := pr_eq (m := h + 1) hQ (by omega) (by omega)
  have hs := pc_succ h
  unfold nxt D
  rw [hA, hs]
  by_cases he : (h + 1) % 2 = 0
  · have hq : (h + 1) / 2 = h / 2 + 1 := by omega
    have hB := pr_eq (m := (h + 1) / 2) hQ (by omega) (by omega)
    have hs2 := pc_succ (h / 2)
    have hmono : Nat.primeCounting (h / 2 + 1) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_pos he, hB, hq, hs2]
    rw [hs2] at hmono
    split_ifs at hmono ⊢ <;> omega
  · have hq : (h + 1) / 2 = h / 2 := by omega
    have hmono : Nat.primeCounting (h / 2) ≤ Nat.primeCounting h :=
      Nat.monotone_primeCounting (by omega)
    rw [if_neg he, hq]
    split_ifs <;> omega

theorem loop_sound {Q hT dT : ℕ} (hQ : Q = Nat.factorial 362) :
    ∀ k h d : ℕ, loop Q hT dT k h d = true → 2 ≤ h → h + k ≤ 131072 → d = D h →
      (hT = h + k ∧ dT = D hT) ∧ ∀ m, h ≤ m → m < h + k → 41 ≤ m → tstR m (D m) = true := by
  intro k
  induction k with
  | zero =>
    intro h d hl _ _ hd
    simp only [loop, Bool.and_eq_true, beq_iff_eq] at hl
    obtain ⟨e1, e2⟩ := hl
    subst e1 e2 hd
    exact ⟨⟨rfl, rfl⟩, fun m h1 h2 _ => by omega⟩
  | succ k ih =>
    intro h d hl h2 hk hd
    rw [loop, force_eq, force_eq, Bool.and_eq_true] at hl
    obtain ⟨ht, hl⟩ := hl
    subst hd
    rw [nxt_eq hQ h2 (by omega)] at hl
    obtain ⟨⟨e1, e2⟩, hall⟩ := ih (h + 1) (D (h + 1)) hl (by omega) (by omega) rfl
    refine ⟨⟨by omega, e2⟩, fun m hm1 hm2 hm3 => ?_⟩
    rcases Nat.eq_or_lt_of_le hm1 with rfl | hlt
    · rw [Bool.or_eq_true, Nat.blt_eq] at ht
      rcases ht with ht | ht
      · omega
      · exact ht
    · exact hall m hlt (by omega) hm3


theorem tests : ∀ m, 41 ≤ m → m < 131072 → tstR m (D m) = true := by
  have r1 := run1
  have r2 := run2
  have r3 := run3
  have r4 := run4
  rw [run, force_eq] at r1 r2 r3 r4
  obtain ⟨⟨_, e1⟩, t1⟩ := loop_sound rfl _ _ _ r1 (by norm_num) (by norm_num) D_two.symm
  obtain ⟨⟨_, e2⟩, t2⟩ := loop_sound rfl _ _ _ r2 (by norm_num) (by norm_num) e1
  obtain ⟨⟨_, e3⟩, t3⟩ := loop_sound rfl _ _ _ r3 (by norm_num) (by norm_num) e2
  obtain ⟨_, t4⟩ := loop_sound rfl _ _ _ r4 (by norm_num) (by norm_num) e3
  intro m h1 h2
  by_cases a1 : m < 32768
  · exact t1 m (by omega) (by omega) h1
  by_cases a2 : m < 65536
  · exact t2 m (by omega) (by omega) h1
  by_cases a3 : m < 98304
  · exact t3 m (by omega) (by omega) h1
  · exact t4 m (by omega) (by omega) h1


end PI.PrimesDyadicRS.K
end
