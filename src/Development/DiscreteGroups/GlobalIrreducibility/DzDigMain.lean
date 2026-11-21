import Development.DiscreteGroups.GlobalIrreducibility.DzDigDef
import Development.DiscreteGroups.GlobalIrreducibility.DzStickDigits
import Mathlib

section
namespace DiscreteGroups.sglob.DzDig

open Finset

def ee (p n : ℕ) : ℕ := ∑ j ∈ range n, p ^ j

def cnt (p n x c : ℕ) : ℕ := #((range n).filter (fun i => c ≤ p ^ i * x % (p ^ n - 1) / ee p n))

theorem N_eq {p n : ℕ} (hp : 2 ≤ p) : p ^ n - 1 = (p - 1) * ee p n :=
  (Stick.geom_sum_mul_pred p n hp).symm

theorem ee_eq {p n : ℕ} (hp : 2 ≤ p) : (p ^ n - 1) / (p - 1) = ee p n := by
  rw [N_eq hp, Nat.mul_div_cancel_left _ (by omega : 0 < p - 1)]

theorem ee_pos {p n : ℕ} (hn : 1 ≤ n) : 0 < ee p n := by
  unfold ee
  calc 0 < 1 := one_pos
    _ = p ^ 0 := (pow_zero p).symm
    _ ≤ ∑ j ∈ range n, p ^ j :=
        single_le_sum (f := fun j => p ^ j) (fun j _ => Nat.zero_le _) (by simp; omega)

theorem N_pos {p n : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : 0 < p ^ n - 1 := by
  rw [N_eq hp]; exact Nat.mul_pos (by omega) (ee_pos hn)

theorem e_mul_dsum {p n a : ℕ} (hp : 2 ≤ p) (ha : a < p ^ n - 1) :
    ee p n * Stick.dsum p a = ∑ i ∈ range n, p ^ i * a % (p ^ n - 1) := by
  have h := Stick.dsum_frac hp ha
  have hpos : 0 < p - 1 := by omega
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [h, N_eq hp]
  ring

theorem pow_mul_ee {p n : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    p ^ i * ee p n = ee p n + (p ^ n - 1) * ee p i := by
  have h2 : p ^ i - 1 = (p - 1) * ee p i := N_eq hp
  have h3 : 0 < p ^ i := pow_pos (by omega) i
  have h4 : p ^ i = (p - 1) * ee p i + 1 := by omega
  rw [N_eq (n := n) hp, h4]
  ring

theorem mod_shift {p n x b : ℕ} (hp : 2 ≤ p) (i : ℕ) :
    p ^ i * ((x + b * ee p n) % (p ^ n - 1)) % (p ^ n - 1)
      = (p ^ i * x % (p ^ n - 1) + b * ee p n) % (p ^ n - 1) := by
  rw [Nat.mul_mod_mod, Nat.mod_add_mod]
  have h : p ^ i * (x + b * ee p n) = p ^ i * x + b * ee p n + (p ^ n - 1) * (b * ee p i) := by
    calc p ^ i * (x + b * ee p n) = p ^ i * x + b * (p ^ i * ee p n) := by ring
      _ = _ := by rw [pow_mul_ee hp i]; ring
  rw [h, Nat.add_mul_mod_self_left]

theorem shift_mod {M e r b : ℕ} (he : 0 < e) (hr : r < M * e) :
    (r + b * e) % (M * e) = ((r / e + b) % M) * e + r % e := by
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · simp [h] at hr
    · exact h
  have h1 := Nat.div_add_mod r e
  have h2 := Nat.div_add_mod (r / e + b) M
  have h3 : (r / e + b) % M < M := Nat.mod_lt _ hM
  have h4 : r % e < e := Nat.mod_lt _ he
  have h5 : r + b * e = (((r / e + b) % M) * e + r % e) + (M * e) * ((r / e + b) / M) := by
    have h6 : r + b * e = (r / e + b) * e + r % e := by
      rw [add_mul]; linarith [h1]
    rw [h6]
    conv_lhs => rw [← h2]
    ring
  rw [h5, Nat.add_mul_mod_self_left]
  apply Nat.mod_eq_of_lt
  calc ((r / e + b) % M) * e + r % e < ((r / e + b) % M) * e + e := by omega
    _ = ((r / e + b) % M + 1) * e := by ring
    _ ≤ M * e := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt h3)

theorem point {M e r b : ℕ} (he : 0 < e) (hr : r < M * e) (hb : b < M) :
    (r + b * e) % (M * e) + M * e * (if M - b ≤ r / e then 1 else 0) = r + b * e := by
  rw [shift_mod he hr]
  have hq : r / e < M := Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hr)
  have h1 := Nat.div_add_mod r e
  split_ifs with h
  · obtain ⟨D, hD⟩ : ∃ D, r / e + b = D + M := ⟨r / e + b - M, by omega⟩
    have hm : (r / e + b) % M = D := by
      rw [hD, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hm]
    conv_rhs => rw [← h1]
    calc D * e + r % e + M * e * 1 = (D + M) * e + r % e := by ring
      _ = (r / e + b) * e + r % e := by rw [hD]
      _ = e * (r / e) + r % e + b * e := by ring
  · have hm : (r / e + b) % M = r / e + b := Nat.mod_eq_of_lt (by omega)
    rw [hm]
    conv_rhs => rw [← h1]
    ring

theorem count_shift {p n x b : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) (hx : x < p ^ n - 1) (hb : b < p - 1) :
    Stick.dsum p ((x + b * ee p n) % (p ^ n - 1)) + (p - 1) * cnt p n x (p - 1 - b)
      = Stick.dsum p x + n * b := by
  have he := ee_pos (p := p) hn
  have hN := N_eq (n := n) hp
  have hNpos := N_pos hp hn
  have h1 := e_mul_dsum hp (Nat.mod_lt (x + b * ee p n) hNpos)
  have h2 := e_mul_dsum hp hx
  have h3 : ∑ i ∈ range n, p ^ i * ((x + b * ee p n) % (p ^ n - 1)) % (p ^ n - 1)
      + (p - 1) * ee p n * cnt p n x (p - 1 - b)
      = ∑ i ∈ range n, p ^ i * x % (p ^ n - 1) + n * (b * ee p n) := by
    unfold cnt
    rw [card_filter, mul_sum, ← sum_add_distrib]
    have : n * (b * ee p n) = ∑ i ∈ range n, b * ee p n := by simp
    rw [this, ← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    rw [mod_shift hp i, hN]
    exact point he (Nat.mod_lt _ (by rw [← hN]; exact hNpos)) hb
  apply Nat.eq_of_mul_eq_mul_left he
  calc ee p n * (Stick.dsum p ((x + b * ee p n) % (p ^ n - 1)) + (p - 1) * cnt p n x (p - 1 - b))
      = ee p n * Stick.dsum p ((x + b * ee p n) % (p ^ n - 1))
          + (p - 1) * ee p n * cnt p n x (p - 1 - b) := by ring
    _ = ∑ i ∈ range n, p ^ i * x % (p ^ n - 1) + n * (b * ee p n) := by rw [h1, h3]
    _ = ee p n * Stick.dsum p x + n * (b * ee p n) := by rw [h2]
    _ = ee p n * (Stick.dsum p x + n * b) := by ring

theorem cnt_zero (p n y : ℕ) : cnt p n y 0 = n := by
  unfold cnt
  rw [filter_true_of_mem (fun i _ => Nat.zero_le _), card_range]

theorem cnt_top {p n y : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n) : cnt p n y (p - 1) = 0 := by
  unfold cnt
  have hNpos := N_pos hp hn
  rw [filter_false_of_mem, card_empty]
  intro i _ hle
  have hlt : p ^ i * y % (p ^ n - 1) < ee p n * (p - 1) := by
    rw [mul_comm (ee p n), ← N_eq hp]; exact Nat.mod_lt _ hNpos
  have := Nat.div_lt_of_lt_mul hlt
  omega

theorem exists_match {p n x x' : ℕ} (hx' : x' < p ^ n - 1)
    (h0 : cnt p n x (x' / ee p n) = cnt p n x' (x' / ee p n))
    (h1 : cnt p n x (x' / ee p n + 1) = cnt p n x' (x' / ee p n + 1)) (hn : 1 ≤ n) :
    ∃ j < n, p ^ j * x % (p ^ n - 1) / ee p n = x' / ee p n := by
  by_contra hne
  push_neg at hne
  have hA : (range n).filter (fun i => x' / ee p n ≤ p ^ i * x % (p ^ n - 1) / ee p n)
      = (range n).filter (fun i => x' / ee p n + 1 ≤ p ^ i * x % (p ^ n - 1) / ee p n) := by
    apply filter_congr
    intro i hi
    have := hne i (mem_range.mp hi)
    omega
  have hz : p ^ 0 * x' % (p ^ n - 1) = x' := by
    rw [pow_zero, one_mul, Nat.mod_eq_of_lt hx']
  have hB : (range n).filter (fun i => x' / ee p n + 1 ≤ p ^ i * x' % (p ^ n - 1) / ee p n)
      ⊆ ((range n).filter (fun i => x' / ee p n ≤ p ^ i * x' % (p ^ n - 1) / ee p n)).erase 0 := by
    intro i hi
    rw [mem_filter, mem_range] at hi
    rw [mem_erase, mem_filter, mem_range]
    refine ⟨?_, hi.1, by omega⟩
    rintro rfl
    have h2 := hi.2
    rw [hz] at h2
    omega
  have h0mem : 0 ∈ (range n).filter (fun i => x' / ee p n ≤ p ^ i * x' % (p ^ n - 1) / ee p n) := by
    rw [mem_filter, mem_range, hz]
    exact ⟨by omega, le_refl _⟩
  have hle := card_le_card hB
  rw [card_erase_of_mem h0mem] at hle
  have hpos := card_pos.mpr ⟨0, h0mem⟩
  unfold cnt at h0 h1
  rw [hA] at h0
  omega

theorem match_of_hyp {p n k k' u : ℕ} (hp : 2 ≤ p) (hn : 1 ≤ n)
    (H : ∀ b : ℕ, Stick.dsum p ((u * k + b * ee p n) % (p ^ n - 1)) + Stick.dsum p (u * k' % (p ^ n - 1))
        = Stick.dsum p ((u * k' + b * ee p n) % (p ^ n - 1)) + Stick.dsum p (u * k % (p ^ n - 1))) :
    ∃ j < n, p ^ j * (u * k % (p ^ n - 1)) % (p ^ n - 1) / ee p n = u * k' % (p ^ n - 1) / ee p n := by
  have hNpos := N_pos hp hn
  have hx : u * k % (p ^ n - 1) < p ^ n - 1 := Nat.mod_lt _ hNpos
  have hx' : u * k' % (p ^ n - 1) < p ^ n - 1 := Nat.mod_lt _ hNpos
  have hcnt : ∀ c, c ≤ p - 1 →
      cnt p n (u * k % (p ^ n - 1)) c = cnt p n (u * k' % (p ^ n - 1)) c := by
    intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [cnt_zero, cnt_zero]
    rcases Nat.eq_or_lt_of_le hc with rfl | hc1
    · rw [cnt_top hp hn, cnt_top hp hn]
    have hb : p - 1 - c < p - 1 := by omega
    have hcb : p - 1 - (p - 1 - c) = c := by omega
    have s1 := count_shift (b := p - 1 - c) hp hn hx hb
    have s2 := count_shift (b := p - 1 - c) hp hn hx' hb
    rw [hcb, Nat.mod_add_mod] at s1 s2
    have s3 := H (p - 1 - c)
    have key : (p - 1) * cnt p n (u * k % (p ^ n - 1)) c
        = (p - 1) * cnt p n (u * k' % (p ^ n - 1)) c := by omega
    exact Nat.eq_of_mul_eq_mul_left (by omega) key
  have hlt : u * k' % (p ^ n - 1) / ee p n < p - 1 := by
    apply Nat.div_lt_of_lt_mul
    rw [mul_comm (ee p n), ← N_eq hp]; exact hx'
  exact exists_match hx' (hcnt _ hlt.le) (hcnt _ hlt) hn

end DiscreteGroups.sglob.DzDig
end

section
namespace DiscreteGroups.sglob.DzDig

open Finset

theorem cover_bound (N e D : ℕ) :
    #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e)) ≤ e - 1 := by
  rcases Nat.eq_zero_or_pos D with hD | hD0
  · subst hD; simp
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; simp
  have hgpos : 0 < N.gcd D := Nat.gcd_pos_of_pos_right N hD0
  have hgN : N.gcd D ∣ N := Nat.gcd_dvd_left N D
  have hgD : N.gcd D ∣ D := Nat.gcd_dvd_right N D
  have hE : N / N.gcd D * N.gcd D = N := Nat.div_mul_cancel hgN
  have hEpos : 0 < N / N.gcd D := Nat.div_pos (Nat.le_of_dvd hNpos hgN) hgpos
  calc #((range N).filter (fun u => 0 < u * D % N ∧ u * D % N < e))
      ≤ #(((Ioc 0 (e - 1)).filter (fun a => N.gcd D ∣ a)) ×ˢ range (N.gcd D)) := by
        apply card_le_card_of_injOn (fun u => (u * D % N, u / (N / N.gcd D)))
        · intro u hu
          have hu' := mem_coe.mp hu
          rw [mem_filter, mem_range] at hu'
          simp only [mem_coe, mem_product, mem_filter, mem_Ioc, mem_range]
          refine ⟨⟨⟨hu'.2.1, by omega⟩, (Nat.dvd_mod_iff hgN).mpr (dvd_mul_of_dvd_right hgD u)⟩, ?_⟩
          rw [Nat.div_lt_iff_lt_mul hEpos, mul_comm, hE]
          exact hu'.1
        · intro u _ v _ huv
          simp only [Prod.mk.injEq] at huv
          have h1 : u * D ≡ v * D [MOD N] := huv.1
          have h2 : u % (N / N.gcd D) = v % (N / N.gcd D) := Nat.ModEq.cancel_right_div_gcd hNpos h1
          calc u = N / N.gcd D * (u / (N / N.gcd D)) + u % (N / N.gcd D) := (Nat.div_add_mod u _).symm
            _ = N / N.gcd D * (v / (N / N.gcd D)) + v % (N / N.gcd D) := by rw [huv.2, h2]
            _ = v := Nat.div_add_mod v _
    _ = (e - 1) / N.gcd D * N.gcd D := by
        rw [card_product, Nat.Ioc_filter_dvd_card_eq_div, card_range]
    _ ≤ e - 1 := Nat.div_mul_le_self _ _

theorem diff_mod {N a b u : ℕ} (hN : 0 < N) (hle : u * b % N ≤ u * a % N) :
    u * (a % N + (N - b % N)) % N = u * a % N - u * b % N := by
  have hb := Nat.mod_lt b hN
  have h1 : u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N) + N * u := by
    have h0 : a % N + (N - b % N) + b % N = a % N + N := by omega
    calc u * (a % N + (N - b % N)) + u * (b % N) = u * (a % N + (N - b % N) + b % N) := by ring
      _ = u * (a % N + N) := by rw [h0]
      _ = u * (a % N) + N * u := by ring
  have h3 : (u * (a % N + (N - b % N)) + u * (b % N)) % N = u * a % N := by
    rw [h1, Nat.add_mul_mod_self_left, Nat.mul_mod_mod]
  rw [Nat.add_mod, Nat.mul_mod_mod] at h3
  have hr := Nat.mod_lt (u * (a % N + (N - b % N))) hN
  have hx := Nat.mod_lt (u * a) hN
  rcases Nat.lt_or_ge (u * (a % N + (N - b % N)) % N + u * b % N) N with h | h
  · rw [Nat.mod_eq_of_lt h] at h3; omega
  · rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)] at h3; omega

theorem totient_le {N e n k k' p : ℕ} (hN : 0 < N) (he : 0 < e)
    (hno : ∀ j < n, ¬ k' ≡ k * p ^ j [MOD N])
    (hm : ∀ u < N, N.Coprime u → ∃ j < n, p ^ j * (u * k % N) % N / e = u * k' % N / e) :
    N.totient ≤ n * (2 * (e - 1)) := by
  have hsub : (range N).filter (fun a => N.Coprime a) ⊆ (range n).biUnion (fun j =>
      (range N).filter (fun u => 0 < u * (k' % N + (N - k * p ^ j % N)) % N
          ∧ u * (k' % N + (N - k * p ^ j % N)) % N < e)
      ∪ (range N).filter (fun u => 0 < u * (k * p ^ j % N + (N - k' % N)) % N
          ∧ u * (k * p ^ j % N + (N - k' % N)) % N < e)) := by
    intro u hu
    rw [mem_filter, mem_range] at hu
    obtain ⟨j, hj, hje⟩ := hm u hu.1 hu.2
    rw [mem_biUnion]
    refine ⟨j, mem_range.mpr hj, ?_⟩
    have hy : p ^ j * (u * k % N) % N = u * (k * p ^ j) % N := by
      rw [Nat.mul_mod_mod, show p ^ j * (u * k) = u * (k * p ^ j) by ring]
    rw [hy] at hje
    have hb1 := Nat.div_add_mod (u * k' % N) e
    have hb2 := Nat.div_add_mod (u * (k * p ^ j) % N) e
    have hm1 := Nat.mod_lt (u * k' % N) he
    have hm2 := Nat.mod_lt (u * (k * p ^ j) % N) he
    rw [hje] at hb2
    rw [mem_union, mem_filter, mem_filter, mem_range]
    rcases lt_trichotomy (u * (k * p ^ j) % N) (u * k' % N) with h | h | h
    · left
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
    · exfalso
      apply hno j hj
      have h' : u * k' ≡ u * (k * p ^ j) [MOD N] := h.symm
      exact Nat.ModEq.cancel_left_of_coprime hu.2 h'
    · right
      rw [diff_mod hN h.le]
      exact ⟨hu.1, by omega, by omega⟩
  calc N.totient = #((range N).filter (fun a => N.Coprime a)) := Nat.totient_eq_card_coprime N
    _ ≤ _ := card_le_card hsub
    _ ≤ _ := card_biUnion_le
    _ ≤ ∑ j ∈ range n, 2 * (e - 1) := by
        apply sum_le_sum
        intro j _
        calc _ ≤ _ := card_union_le _ _
          _ ≤ (e - 1) + (e - 1) := add_le_add (cover_bound _ _ _) (cover_bound _ _ _)
          _ = 2 * (e - 1) := by ring
    _ = n * (2 * (e - 1)) := by rw [sum_const, card_range, smul_eq_mul]

end DiscreteGroups.sglob.DzDig
end

section
namespace DiscreteGroups.sglob.DzDig

open Finset

theorem card_primes_le {s : Finset ℕ} {a : ℕ} (hs : ∀ q ∈ s, q.Prime) (ha : ∀ q ∈ s, q ≤ a)
    (h2 : 2 ≤ a) : 2 * #s ≤ a + 1 := by
  have h : #s ≤ #(range ((a - 1) / 2 + 1)) := by
    apply card_le_card_of_injOn (fun x => (x - 1) / 2)
    · intro x hx
      have := ha x (mem_coe.mp hx)
      simp only [mem_coe, mem_range]
      omega
    · intro x hx y hy hxy
      have hx2 := (hs x (mem_coe.mp hx)).two_le
      have hy2 := (hs y (mem_coe.mp hy)).two_le
      have ox := (hs x (mem_coe.mp hx)).eq_two_or_odd
      have oy := (hs y (mem_coe.mp hy)).eq_two_or_odd
      simp only at hxy
      omega
  rw [card_range] at h
  omega

theorem prod_sq_le : ∀ s : Finset ℕ, (∀ q ∈ s, q.Prime) → s.Nonempty →
    (∏ q ∈ s, q) ^ 2 ≤ 4 * (2 * #s - 1) * (∏ q ∈ s, (q - 1)) ^ 2 := by
  intro s
  induction s using Finset.induction_on_max
  · intro _ hne
    exact absurd hne (by simp)
  next a s hlt ih =>
    intro hs _
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have ha2 := (hs a (mem_insert_self a s)).two_le
    have hle : ∀ q ∈ insert a s, q ≤ a := by
      intro q hq
      rcases mem_insert.mp hq with h | h
      · omega
      · exact (hlt q h).le
    have hcard := card_primes_le hs hle ha2
    rw [prod_insert ha, prod_insert ha, card_insert_of_notMem ha]
    rw [card_insert_of_notMem ha] at hcard
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    rw [show b + 1 - 1 = b by omega]
    rcases s.eq_empty_or_nonempty with hs0 | hsne
    · subst hs0
      rw [prod_empty, prod_empty, card_empty]
      norm_num <;> nlinarith [ha2]
    · have hs' : ∀ q ∈ s, q.Prime := fun q hq => hs q (mem_insert_of_mem hq)
      have ih' := ih hs' hsne
      have hs1 : 1 ≤ #s := card_pos.mpr hsne
      obtain ⟨m, hm⟩ : ∃ m, #s = m + 1 := ⟨#s - 1, by omega⟩
      rw [hm] at ih' hcard
      rw [hm]
      rw [show 2 * (m + 1) - 1 = 2 * m + 1 by omega] at ih'
      rw [show 2 * (m + 1 + 1) - 1 = 2 * m + 3 by omega]
      have hb : 2 * m + 2 ≤ b := by omega
      have h2 : (b + 1) ^ 2 * (2 * m + 1) ≤ (2 * m + 3) * b ^ 2 := by
        have := Nat.mul_le_mul_right b hb
        nlinarith
      calc ((b + 1) * ∏ q ∈ s, q) ^ 2 = (b + 1) ^ 2 * (∏ q ∈ s, q) ^ 2 := by ring
        _ ≤ (b + 1) ^ 2 * (4 * (2 * m + 1) * (∏ q ∈ s, (q - 1)) ^ 2) := Nat.mul_le_mul_left _ ih'
        _ = 4 * ((b + 1) ^ 2 * (2 * m + 1)) * (∏ q ∈ s, (q - 1)) ^ 2 := by ring
        _ ≤ 4 * ((2 * m + 3) * b ^ 2) * (∏ q ∈ s, (q - 1)) ^ 2 :=
            Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h2)
        _ = 4 * (2 * m + 3) * (b * ∏ q ∈ s, (q - 1)) ^ 2 := by ring

theorem pow_bound : ∀ t, 4 ≤ t → (t + 1) * t ≤ 4 * 2 ^ t := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
    rw [pow_succ]
    nlinarith

theorem pow_le_two_pow {p n : ℕ} (hn : 1 ≤ n) (h16 : 16 * n ^ 2 < p) : p ^ (2 * n) ≤ 2 ^ p := by
  have hs : 0 < 2 * n := by omega
  have ht : 4 * (2 * n) ≤ p / (2 * n) := by
    rw [Nat.le_div_iff_mul_le hs]
    nlinarith
  have hp1 : p < (p / (2 * n) + 1) * (2 * n) := by
    nlinarith [Nat.div_add_mod p (2 * n), Nat.mod_lt p hs]
  have ht4 : 4 ≤ p / (2 * n) := by omega
  have hpt : p ≤ 2 ^ (p / (2 * n)) := by
    nlinarith [Nat.mul_le_mul_left (p / (2 * n) + 1) ht, pow_bound (p / (2 * n)) ht4]
  calc p ^ (2 * n) ≤ (2 ^ (p / (2 * n))) ^ (2 * n) := Nat.pow_le_pow_left hpt _
    _ = 2 ^ (p / (2 * n) * (2 * n)) := (pow_mul 2 _ _).symm
    _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self p (2 * n))

theorem sq_le_totient {N : ℕ} (hN : 2 ≤ N) :
    N ^ 2 ≤ 4 * (2 * #N.primeFactors - 1) * N.totient ^ 2 := by
  have hNpos : 0 < N := by omega
  have hSp : ∀ q ∈ N.primeFactors, q.Prime := fun q hq => Nat.prime_of_mem_primeFactors hq
  have hSne : N.primeFactors.Nonempty := by
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
    exact ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩
  have key := prod_sq_le N.primeFactors hSp hSne
  have htot := Nat.totient_mul_prod_primeFactors N
  have hQ : 0 < ∏ q ∈ N.primeFactors, (q - 1) :=
    prod_pos (fun q hq => by have := (hSp q hq).two_le; omega)
  have h1 : (N * ∏ q ∈ N.primeFactors, (q - 1)) ^ 2
      ≤ (4 * (2 * #N.primeFactors - 1) * N.totient ^ 2) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2 := by
    rw [← htot]
    calc (N.totient * ∏ q ∈ N.primeFactors, q) ^ 2
        = N.totient ^ 2 * (∏ q ∈ N.primeFactors, q) ^ 2 := by ring
      _ ≤ N.totient ^ 2 * (4 * (2 * #N.primeFactors - 1) * (∏ q ∈ N.primeFactors, (q - 1)) ^ 2) :=
          Nat.mul_le_mul_left _ key
      _ = _ := by ring
  rw [mul_pow] at h1
  exact Nat.le_of_mul_le_mul_right h1 (pow_pos hQ 2)

theorem card_primeFactors_pos {N : ℕ} (hN : 2 ≤ N) : 1 ≤ #N.primeFactors := by
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd (show N ≠ 1 by omega)
  exact card_pos.mpr ⟨q, Nat.mem_primeFactors.mpr ⟨hq, hqd, by omega⟩⟩

theorem two_pow_card_le {N : ℕ} (hN : 0 < N) : 2 ^ #N.primeFactors ≤ N :=
  (pow_card_le_prod N.primeFactors (fun q => q) 2
      (fun q hq => (Nat.prime_of_mem_primeFactors hq).two_le)).trans
    (Nat.le_of_dvd hN (Nat.prod_primeFactors_dvd N))

theorem two_n_N_lt {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) (h16 : 16 * n ^ 2 < p) :
    2 * n * (p ^ n - 1) < (p - 1) * (p ^ n - 1).totient := by
  have hp2 := hp.two_le
  have hpn : p ^ 2 ≤ p ^ n := Nat.pow_le_pow_right (by omega) hn
  have hp4 : 4 ≤ p ^ 2 := by nlinarith
  have hN2 : 2 ≤ p ^ n - 1 := by omega
  have hsq := sq_le_totient hN2
  have hw1 := card_primeFactors_pos hN2
  have hω := two_pow_card_le (show 0 < p ^ n - 1 by omega)
  have hφ : 0 < (p ^ n - 1).totient := Nat.totient_pos.mpr (by omega)
  have hwp : 2 * #(p ^ n - 1).primeFactors < p := by
    by_contra hc
    push_neg at hc
    have : 2 ^ p < 2 ^ p :=
      calc 2 ^ p ≤ 2 ^ (2 * #(p ^ n - 1).primeFactors) := Nat.pow_le_pow_right (by norm_num) hc
        _ = (2 ^ #(p ^ n - 1).primeFactors) ^ 2 := by ring
        _ ≤ (p ^ n - 1) ^ 2 := Nat.pow_le_pow_left hω 2
        _ < (p ^ n) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
        _ = p ^ (2 * n) := by ring
        _ ≤ 2 ^ p := pow_le_two_pow (by omega) h16
    exact lt_irrefl _ this
  have h16' : 16 * n ^ 2 ≤ p - 1 := by omega
  have hw2 : 2 * #(p ^ n - 1).primeFactors - 1 < p - 1 := by omega
  have hlt : 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1) < (p - 1) * (p - 1) :=
    calc 16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)
        ≤ (p - 1) * (2 * #(p ^ n - 1).primeFactors - 1) := Nat.mul_le_mul_right _ h16'
      _ < (p - 1) * (p - 1) := Nat.mul_lt_mul_of_pos_left hw2 (by omega)
  have hsq2 : (2 * n * (p ^ n - 1)) ^ 2 < ((p - 1) * (p ^ n - 1).totient) ^ 2 :=
    calc (2 * n * (p ^ n - 1)) ^ 2 = 4 * n ^ 2 * (p ^ n - 1) ^ 2 := by ring
      _ ≤ 4 * n ^ 2 * (4 * (2 * #(p ^ n - 1).primeFactors - 1) * (p ^ n - 1).totient ^ 2) :=
          Nat.mul_le_mul_left _ hsq
      _ = (16 * n ^ 2 * (2 * #(p ^ n - 1).primeFactors - 1)) * (p ^ n - 1).totient ^ 2 := by ring
      _ < ((p - 1) * (p - 1)) * (p ^ n - 1).totient ^ 2 :=
          Nat.mul_lt_mul_of_pos_right hlt (pow_pos hφ 2)
      _ = ((p - 1) * (p ^ n - 1).totient) ^ 2 := by ring
  by_contra hc
  push_neg at hc
  exact absurd hsq2 (not_lt.mpr (Nat.pow_le_pow_left hc 2))

end DiscreteGroups.sglob.DzDig
end

section
namespace DiscreteGroups.sglob.DzType

theorem dig : Dig := by
  intro p n hp hn h16 k k' _ _ H
  have hp2 := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hee := DzDig.ee_eq (n := n) hp2
  have hN := DzDig.N_eq (n := n) hp2
  have he := DzDig.ee_pos (p := p) hn1
  have hNpos := DzDig.N_pos hp2 hn1
  by_contra hno
  push_neg at hno
  have hm : ∀ u < p ^ n - 1, (p ^ n - 1).Coprime u → ∃ j < n,
      p ^ j * (u * k % (p ^ n - 1)) % (p ^ n - 1) / DzDig.ee p n
        = u * k' % (p ^ n - 1) / DzDig.ee p n := by
    intro u _ hu
    apply DzDig.match_of_hyp hp2 hn1
    intro b
    have := H u b (Nat.coprime_comm.mp hu)
    rw [hee] at this
    exact this
  have htot := DzDig.totient_le hNpos he (fun j _ => hno j) hm
  have hineq := DzDig.two_n_N_lt hp hn h16
  have h2 : (p - 1) * (2 * n * DzDig.ee p n) < (p - 1) * (p ^ n - 1).totient :=
    calc (p - 1) * (2 * n * DzDig.ee p n) = 2 * n * ((p - 1) * DzDig.ee p n) := by ring
      _ = 2 * n * (p ^ n - 1) := by rw [hN]
      _ < _ := hineq
  have h3 := (Nat.mul_lt_mul_left (by omega : 0 < p - 1)).mp h2
  have h5 : n * (2 * (DzDig.ee p n - 1)) ≤ 2 * n * DzDig.ee p n :=
    calc n * (2 * (DzDig.ee p n - 1)) ≤ n * (2 * DzDig.ee p n) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * n * DzDig.ee p n := by ring
  exact absurd (lt_of_lt_of_le h3 (htot.trans h5)) (lt_irrefl _)

end DiscreteGroups.sglob.DzType
end
