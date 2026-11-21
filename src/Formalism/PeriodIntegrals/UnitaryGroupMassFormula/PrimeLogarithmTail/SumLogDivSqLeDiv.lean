import Mathlib

section
namespace PI.TailWork

open Finset

theorem sum_log_block (n : ℕ) :
    ∑ p ∈ (Ioc n (2 * n)).filter Nat.Prime, Real.log (p : ℝ) ≤ (n : ℝ) * Real.log 4 := by
  classical
  have hdvd : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ∣ Nat.centralBinom n := by
    apply Finset.prod_primes_dvd
    · intro p hp
      exact (Finset.mem_filter.1 hp).2.prime
    · intro p hp
      obtain ⟨hI, hpr⟩ := Finset.mem_filter.1 hp
      obtain ⟨h1, h2⟩ := Finset.mem_Ioc.1 hI
      rw [Nat.centralBinom_eq_two_mul_choose, two_mul]
      exact hpr.dvd_choose_add h1 h1 (by omega)
  have hle : (∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p) ≤ 4 ^ n :=
    (Nat.le_of_dvd (Nat.centralBinom_pos n) hdvd).trans (Nat.centralBinom_le_four_pow n)
  have hpos : ∀ p ∈ (Ioc n (2 * n)).filter Nat.Prime, ((p : ℕ) : ℝ) ≠ 0 := by
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.ne_zero
  rw [← Real.log_prod hpos, ← Real.log_pow]
  apply Real.log_le_log
  · apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Finset.mem_filter.1 hp).2.pos
  · have : ((∏ p ∈ (Ioc n (2 * n)).filter Nat.Prime, p : ℕ) : ℝ) ≤ ((4 ^ n : ℕ) : ℝ) := by
      exact_mod_cast hle
    push_cast at this
    exact this

noncomputable def g (n : ℕ) : ℝ := 1 / ((n : ℝ) * ((n : ℝ) - 1))

noncomputable def h (n : ℕ) : ℝ := 1 / ((n : ℝ) - 1) + 1 / (n : ℝ)

theorem sum_Ico_tele (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    ∑ n ∈ Ico a b, (f n - f (n + 1)) = f a - f b := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [Finset.sum_Ico_succ_top hab, ih]
    ring

theorem w_nonneg (n : ℕ) (hn : 2 ≤ n) : 0 ≤ g n - g (n + 1) := by
  unfold g
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  push_cast
  rw [sub_nonneg]
  apply one_div_le_one_div_of_le
  · nlinarith
  · nlinarith

theorem w_mul (n : ℕ) (hn : 2 ≤ n) : (g n - g (n + 1)) * (n : ℝ) = h n - h (n + 1) := by
  unfold g h
  have h1 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have h2 : (n : ℝ) - 1 ≠ 0 := by linarith
  have h3 : (n : ℝ) ≠ 0 := by linarith
  have h4 : (n : ℝ) + 1 ≠ 0 := by linarith
  push_cast
  simp only [add_sub_cancel_right]
  field_simp
  ring

theorem weighted (k : ℕ) (hk : 1 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) := by
  classical
  set N := k + 1 + Q.sup id + 1 with hN
  have hw : ∀ p ∈ Q, g ((p + 1) / 2) - g p = ∑ m ∈ Ico ((p + 1) / 2) p, (g m - g (m + 1)) := by
    intro p hp
    have := (hQ p hp).2
    rw [sum_Ico_tele g _ _ (by omega)]
  have hL : ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)
      = ∑ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
          ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ) := by
    rw [Finset.sum_congr rfl (fun p hp => by rw [hw p hp, Finset.mul_sum])]
    rw [Finset.sum_comm' (t' := Ico (k + 1) N)
      (s' := fun m => Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p))]
    · refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun p _ => mul_comm _ _)
    · intro p m
      simp only [Finset.mem_filter, Finset.mem_Ico]
      constructor
      · rintro ⟨hp, h1, h2⟩
        have := (hQ p hp).2
        have hs : p ≤ Q.sup id := Finset.le_sup (f := id) hp
        exact ⟨⟨hp, h1, h2⟩, by omega, by omega⟩
      · rintro ⟨⟨hp, h1, h2⟩, _, _⟩
        exact ⟨hp, h1, h2⟩
  rw [hL]
  have hb : ∀ m ∈ Ico (k + 1) N, (g m - g (m + 1)) *
      ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ Real.log 4 * (h m - h (m + 1)) := by
    intro m hm
    have hm2 : 2 ≤ m := by simp only [Finset.mem_Ico] at hm; omega
    have hin : ∑ p ∈ Q.filter (fun p => (p + 1) / 2 ≤ m ∧ m < p), Real.log (p : ℝ)
        ≤ (m : ℝ) * Real.log 4 := by
      refine le_trans ?_ (sum_log_block m)
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
        exact ⟨⟨hp.2.2, by omega⟩, (hQ p hp.1).1⟩
      · intro p _ _
        exact Real.log_natCast_nonneg p
    calc _ ≤ (g m - g (m + 1)) * ((m : ℝ) * Real.log 4) :=
          mul_le_mul_of_nonneg_left hin (w_nonneg m hm2)
      _ = Real.log 4 * ((g m - g (m + 1)) * m) := by ring
      _ = _ := by rw [w_mul m hm2]
  refine (Finset.sum_le_sum hb).trans ?_
  rw [← Finset.mul_sum, sum_Ico_tele h _ _ (by omega)]
  have hk1 : h (k + 1) = 1 / (k : ℝ) + 1 / ((k : ℝ) + 1) := by
    unfold h
    push_cast
    rw [add_sub_cancel_right]
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hN0 : 0 ≤ h N := by
    unfold h
    exact add_nonneg (one_div_nonneg.2 (by linarith)) (one_div_nonneg.2 (by linarith))
  have hl : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [hk1]
  exact mul_le_mul_of_nonneg_left (by linarith) hl

theorem log_four_lt : Real.log 4 < 1.3863 := by
  have h2 := Real.log_two_lt_d9
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h4]
  norm_num at h2 ⊢
  linarith

theorem weight_ge (k p : ℕ) (hk : 1 ≤ k) (hp : 2 * k + 1 ≤ p) (hodd : p % 2 = 1) :
    (3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2 ≤ g ((p + 1) / 2) - g p := by
  obtain ⟨j, rfl⟩ : ∃ j, p = 2 * j + 1 := ⟨p / 2, by omega⟩
  have hq : (2 * j + 1 + 1) / 2 = j + 1 := by omega
  rw [hq]
  have hjk : k ≤ j := by omega
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hj' : (k : ℝ) ≤ j := by exact_mod_cast hjk
  have hj1 : (1 : ℝ) ≤ j := le_trans hk' hj'
  unfold g
  push_cast
  simp only [add_sub_cancel_right]
  have hmid : 3 - 1 / (2 * (k : ℝ) + 1) ≤ 3 - 1 / (2 * (j : ℝ) + 1) := by
    have : 1 / (2 * (j : ℝ) + 1) ≤ 1 / (2 * (k : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity) (by linarith)
    linarith
  have key : 1 / (((j : ℝ) + 1) * j) - 1 / ((2 * (j : ℝ) + 1) * (2 * j))
      - (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      = (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by
    have : (j : ℝ) ≠ 0 := by linarith
    have : (j : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (j : ℝ) + 1 ≠ 0 := by linarith
    field_simp
    ring
  have hpos : 0 ≤ (6 * (j : ℝ) + 2) / ((2 * (j : ℝ) + 1) ^ 3 * (4 * j * (j + 1))) := by positivity
  have hstep : (3 - 1 / (2 * (k : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2
      ≤ (3 - 1 / (2 * (j : ℝ) + 1)) / (2 * (j : ℝ) + 1) ^ 2 :=
    div_le_div_of_nonneg_right hmid (by positivity)
  linarith

theorem tail_odd (k : ℕ) (hk : 3 ≤ k) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ 2 * k + 1 ≤ p) :
    ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2 ≤ 2.04 / (2 * (k : ℝ) + 1) := by
  have hk1 : 1 ≤ k := by omega
  have hW := weighted k hk1 Q hQ
  have hkR : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hcpos : 0 < 3 - 1 / (2 * (k : ℝ) + 1) := by
    have : 1 / (2 * (k : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hterm : ∀ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
    intro p hp
    obtain ⟨hpr, hpk⟩ := hQ p hp
    have hodd : p % 2 = 1 := by
      rcases hpr.eq_two_or_odd with h2 | h2
      · omega
      · exact h2
    have hwg := weight_ge k p hk1 hpk hodd
    have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
    rw [le_div_iff₀ hcpos]
    calc Real.log (p : ℝ) / (p : ℝ) ^ 2 * (3 - 1 / (2 * (k : ℝ) + 1))
        = Real.log (p : ℝ) * ((3 - 1 / (2 * (k : ℝ) + 1)) / (p : ℝ) ^ 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hwg hlog
  have hl := log_four_lt
  have hl0 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have e : Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1))
      = Real.log 4 * (2 * (k : ℝ) + 1) ^ 2 / ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    have : (k : ℝ) ≠ 0 := by linarith
    have : (k : ℝ) + 1 ≠ 0 := by linarith
    have : 2 * (k : ℝ) + 1 ≠ 0 := by linarith
    have : 6 * (k : ℝ) + 2 ≠ 0 := by linarith
    have hc : 3 - 1 / (2 * (k : ℝ) + 1) = (6 * (k : ℝ) + 2) / (2 * (k : ℝ) + 1) := by
      field_simp
      ring
    rw [hc]
    field_simp
    ring
  have A : Real.log 4 * (2 * (k : ℝ) + 1) ^ 3 ≤ 1.3863 * (2 * (k : ℝ) + 1) ^ 3 :=
    mul_le_mul_of_nonneg_right hl.le (by positivity)
  have hk3 : 0 ≤ (k : ℝ) - 3 := by linarith
  have B : 1.3863 * (2 * (k : ℝ) + 1) ^ 3 ≤ 2.04 * ((k : ℝ) * ((k : ℝ) + 1) * (6 * (k : ℝ) + 2)) := by
    nlinarith [mul_nonneg (mul_nonneg hk3 hk3) hk3, mul_nonneg hk3 hk3, hk3]
  calc ∑ p ∈ Q, Real.log (p : ℝ) / (p : ℝ) ^ 2
      ≤ ∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        Finset.sum_le_sum hterm
    _ = (∑ p ∈ Q, Real.log (p : ℝ) * (g ((p + 1) / 2) - g p)) / (3 - 1 / (2 * (k : ℝ) + 1)) := by
        rw [Finset.sum_div]
    _ ≤ Real.log 4 * (1 / (k : ℝ) + 1 / ((k : ℝ) + 1)) / (3 - 1 / (2 * (k : ℝ) + 1)) :=
        div_le_div_of_nonneg_right hW hcpos.le
    _ ≤ 2.04 / (2 * (k : ℝ) + 1) := by
        rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [A, B]

end PI.TailWork
end

section
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
end
