import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimePowerVonMangoldtSumBound
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_von_mangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) (hM : K ≤ M) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤
      (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 + 4 / (K : ℝ) - 4 / (M : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 K, Λ n) / (K : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (sq_nonneg _)
    simp only [Ioc_self, sum_empty]
    linarith
  | succ M hM ih =>
    rw [sum_Ioc_succ_top hM, sum_Icc_succ_top (by omega : 1 ≤ M + 1)]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have hψ := h M
    set ψ := ∑ n ∈ Icc 1 M, Λ n
    push_cast
    have key : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2 ≤ 4 / (M : ℝ) - 4 / ((M : ℝ) + 1) := by
      have e1 : ψ / (M : ℝ) ^ 2 - ψ / ((M : ℝ) + 1) ^ 2
          = ψ * ((2 * M + 1) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      have e2 : 4 / (M : ℝ) - 4 / ((M : ℝ) + 1)
          = 2 * M * ((2 * M + 2) / ((M : ℝ) ^ 2 * ((M : ℝ) + 1) ^ 2)) := by
        field_simp; ring
      rw [e1, e2]
      apply mul_le_mul hψ _ (by positivity) (by positivity)
      gcongr
      norm_num
    rw [add_div]
    linarith

theorem sum_vonMangoldt_div_sq_Ioc_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (K : ℕ) (hK : 1 ≤ K) (M : ℕ) :
    ∑ m ∈ Ioc K M, Λ m / (m : ℝ) ^ 2 ≤ 4 / (K : ℝ) := by
  rcases le_total K M with hM | hM
  · have h1 := sum_von_mangoldt_div_sq_Ioc_le h K hK M hM
    have hM0 : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
    have h2 : (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 ≤ 4 / (M : ℝ) := by
      rw [div_le_div_iff₀ (by positivity) hM0]
      have := h M
      nlinarith
    linarith
  · rw [Ioc_eq_empty (by omega), sum_empty]
    positivity

theorem sum_cn_isSquare_le
    (h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ)) (x : ℝ) (hx : 1 ≤ x) (N : ℕ) :
    ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n ≤ 10 * Real.sqrt x := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hcn : ∀ n : ℕ, 0 ≤ Formalism.HermitianLattices.GL2PrimeSums.cn x n := fun n =>
    mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
  set y := Real.sqrt x with hy
  have hy1 : 1 ≤ y := Real.one_le_sqrt.mpr hx
  have hyy : y * y = x := Real.mul_self_sqrt hx0
  set K : ℕ := ⌊y⌋₊ with hKdef
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy1)
  have hK1' : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hKy : (K : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyK : y < K + 1 := Nat.lt_floor_add_one y
  have hsub : (Icc 1 N).filter (fun n => IsSquare n) ⊆ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2) := by
    intro n hn
    simp only [mem_filter, mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, r, rfl⟩ := hn
    refine mem_image.mpr ⟨r, ?_, sq r⟩
    have hr : 1 ≤ r := Nat.pos_of_ne_zero (by rintro rfl; simp at h1)
    have hrN : r ≤ N := le_trans (Nat.le_mul_self r) h2
    simp only [mem_union, mem_Icc, mem_Ioc]
    omega
  have hdisj : Disjoint (Icc 1 K) (Ioc K N) := by
    rw [disjoint_left]
    intro a h1 h2
    simp only [mem_Icc, mem_Ioc] at h1 h2
    omega
  have hA : ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 2 * y := by
    calc ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Icc 1 K, Λ m := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          exact mul_le_of_le_one_right vonMangoldt_nonneg (min_le_left _ _)
      _ ≤ 2 * (K : ℝ) := h K
      _ ≤ 2 * y := by linarith
  have hB : ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ 8 * y := by
    calc ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) ≤ ∑ m ∈ Ioc K N, x * (Λ m / (m : ℝ) ^ 2) := by
          refine sum_le_sum fun m _ => ?_
          unfold Formalism.HermitianLattices.GL2PrimeSums.cn
          rw [vonMangoldt_apply_pow (by norm_num)]
          calc Λ m * min 1 (x / ((m ^ 2 : ℕ) : ℝ)) ≤ Λ m * (x / ((m ^ 2 : ℕ) : ℝ)) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
            _ = x * (Λ m / (m : ℝ) ^ 2) := by push_cast; ring
      _ = x * ∑ m ∈ Ioc K N, Λ m / (m : ℝ) ^ 2 := by rw [mul_sum]
      _ ≤ x * (4 / (K : ℝ)) :=
          mul_le_mul_of_nonneg_left (sum_vonMangoldt_div_sq_Ioc_le h K hK1 N) hx0
      _ ≤ 8 * y := by
          rw [← mul_div_assoc, div_le_iff₀ (by linarith), ← hyy]
          nlinarith
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsSquare n), Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ (Icc 1 K ∪ Ioc K N).image (fun m => m ^ 2), Formalism.HermitianLattices.GL2PrimeSums.cn x n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hcn n
    _ = ∑ m ∈ Icc 1 K ∪ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_image fun a _ b _ hab => Nat.pow_left_injective (by norm_num : 2 ≠ 0) hab
    _ = ∑ m ∈ Icc 1 K, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) + ∑ m ∈ Ioc K N, Formalism.HermitianLattices.GL2PrimeSums.cn x (m ^ 2) :=
        sum_union hdisj
    _ ≤ 10 * y := by linarith

theorem remainder_smooth_rough_bound : Formalism.HermitianLattices.GL2a2.SizeR := by
  intro hψ
  have h : ∀ M : ℕ, ∑ n ∈ Icc 1 M, Λ n ≤ 2 * (M : ℝ) := fun M => by
    simpa using hψ M (Nat.cast_nonneg M)
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  refine ⟨max C 10, fun ε hε _ x hx m₀ hm₀ hp => ?_⟩
  unfold Formalism.HermitianLattices.GL2a2.Rsum
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have h10 : (10 : ℝ) ≤ max C 10 := le_max_right _ _
  have hw : 0 ≤ x ^ (ε / 5) := Real.rpow_nonneg hx0.le _
  have h1 := sum_cn_isSquare_le h x (by linarith) ⌊x ^ (400 : ℝ)⌋₊
  rw [Real.sqrt_eq_rpow] at h1
  have hs : 0 ≤ x ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hx0.le _
  set S := m₀.primeFactors.filter (fun p => p ≤ ⌊x ^ (400 : ℝ)⌋₊) with hS
  have hsub : S ⊆ Icc 1 ⌊x ^ (ε / 5)⌋₊ := by
    intro p hpS
    simp only [hS, mem_filter, Nat.mem_primeFactors] at hpS
    obtain ⟨⟨hpp, hd, _⟩, hle⟩ := hpS
    refine mem_Icc.mpr ⟨hpp.one_le, Nat.le_floor ?_⟩
    rcases hp p hpp hd with h' | h'
    · exact h'
    · exfalso
      have : (p : ℝ) ≤ x ^ (400 : ℝ) :=
        (Nat.le_floor_iff (Real.rpow_nonneg hx0.le _)).mp hle
      linarith
  have hcard : (S.card : ℝ) ≤ x ^ (ε / 5) := by
    have := card_le_card hsub
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact le_trans (by exact_mod_cast this) (Nat.floor_le hw)
  have h2 : ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ max C 10 * (x ^ (ε / 5) * Real.log x) := by
    calc ∑ p ∈ S, Formalism.HermitianLattices.GL2a2.sP x p ≤ S.card • (max C 10 * Real.log x) := by
          refine sum_le_card_nsmul _ _ _ fun p hpS => ?_
          have hpp : p.Prime := Nat.prime_of_mem_primeFactors (mem_filter.mp hpS).1
          exact (hC x hx p hpp).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hlog)
      _ = (S.card : ℝ) * (max C 10 * Real.log x) := nsmul_eq_mul _ _
      _ ≤ x ^ (ε / 5) * (max C 10 * Real.log x) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hlog)
      _ = max C 10 * (x ^ (ε / 5) * Real.log x) := by ring
  have h3 : 10 * x ^ ((1 : ℝ) / 2) ≤ max C 10 * x ^ ((1 : ℝ) / 2) :=
    mul_le_mul_of_nonneg_right h10 hs
  rw [mul_add]
  linarith

end GlobalTheory
end

section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem geom_Icc_one_le_two_mul_sub (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r - 2 * r ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hp : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    have : r ^ (n + 1 + 1) = r ^ (n + 1) * r := pow_succ _ _
    nlinarith

theorem primePowerSum_le_two_mul_log_div (x : ℝ) (hx : 0 < x) (p : ℕ) (hp : p.Prime) :
    Formalism.HermitianLattices.GL2a2.sP x p ≤ 2 * x * Real.log p / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  unfold Formalism.HermitianLattices.GL2a2.sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  have hc : 0 ≤ x * Real.log p := by positivity
  calc ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i)
      ≤ ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), x * Real.log p * (1 / (p : ℝ)) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi1 : i ≠ 0 := by
          have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1
          omega
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        rw [vonMangoldt_apply_pow hi1, vonMangoldt_apply_prime hp]
        calc Real.log p * min 1 (x / ((p ^ i : ℕ) : ℝ))
            ≤ Real.log p * (x / ((p ^ i : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
          _ = x * Real.log p * (1 / (p : ℝ)) ^ i := by
              push_cast
              rw [one_div_pow]
              ring
    _ ≤ ∑ i ∈ Icc 1 N, x * Real.log p * (1 / (p : ℝ)) ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
    _ = x * Real.log p * ∑ i ∈ Icc 1 N, (1 / (p : ℝ)) ^ i := by rw [Finset.mul_sum]
    _ ≤ x * Real.log p * (2 * (1 / (p : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have h := geom_Icc_one_le_two_mul_sub _ hr0 hr1 N
        have : 0 ≤ (1 / (p : ℝ)) ^ (N + 1) := pow_nonneg hr0 _
        linarith
    _ = 2 * x * Real.log p / p := by ring

theorem large_prime_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSpLarge :=
  fun x hx p hp _ => primePowerSum_le_two_mul_log_div x hx p hp

end GlobalTheory
end

section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_von_mangoldt_div_sq_tail
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) (hN : M ≤ N) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 + 4 / M - 4 / N := by
  induction N, hN using Nat.le_induction with
  | base =>
    have : 0 ≤ (∑ n ∈ Icc 1 M, Λ n) / (M : ℝ) ^ 2 :=
      div_nonneg (sum_nonneg fun _ _ => vonMangoldt_nonneg) (by positivity)
    simpa using this
  | succ N hN ih =>
    rw [sum_Ioc_succ_top hN, sum_Icc_succ_top (by omega)]
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hA := hψ N
    set A := ∑ n ∈ Icc 1 N, Λ n
    push_cast
    have h1 : 0 ≤ 1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2 := by
      rw [sub_nonneg]
      exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
    have h2 := mul_le_mul_of_nonneg_right hA h1
    have h3 : 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) ≤ 4 / N - 4 / ((N : ℝ) + 1) := by
      have e : 4 / N - 4 / ((N : ℝ) + 1) - 2 * (N : ℝ) * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2)
          = 2 / (N * ((N : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      have : 0 ≤ 2 / (N * ((N : ℝ) + 1) ^ 2) := by positivity
      linarith
    have e1 : A * (1 / (N : ℝ) ^ 2 - 1 / ((N : ℝ) + 1) ^ 2) = A / (N : ℝ) ^ 2 - A / ((N : ℝ) + 1) ^ 2 := by
      ring
    rw [add_div]
    linarith

theorem sum_vonMangoldt_div_sq_tail
    (hψ : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ)) (M : ℕ) (hM : 1 ≤ M) (N : ℕ) :
    ∑ n ∈ Ioc M N, Λ n / (n : ℝ) ^ 2 ≤ 4 / M := by
  rcases le_or_gt M N with hN | hN
  · have h := sum_von_mangoldt_div_sq_tail hψ M hM N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have h2 : (∑ n ∈ Icc 1 N, Λ n) / (N : ℝ) ^ 2 ≤ 4 / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      nlinarith [hψ N, mul_le_mul_of_nonneg_right (hψ N) hN0.le]
    linarith
  · rw [Ioc_eq_empty (by omega)]
    simp only [sum_empty]
    positivity

theorem prime_sum_square_bound : Formalism.HermitianLattices.GL2a2.SizeSpSq := by
  intro hψ
  obtain ⟨C, hC⟩ := prime_power_von_mangoldt_sum_bound
  have hL : Formalism.HermitianLattices.GL2a2.SizeSpLarge := GlobalTheory.large_prime_sum_bound
  have hψ' : ∀ N : ℕ, ∑ n ∈ Icc 1 N, Λ n ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  refine ⟨6 * C ^ 2 + 12800, fun x hx => ?_⟩
  have hx0 : (0 : ℝ) < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  set N : ℕ := ⌊x ^ (400 : ℝ)⌋₊ with hN
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by positivity)
  set M : ℕ := ⌊x⌋₊ with hM
  have hM1 : 1 ≤ M := Nat.le_floor (by simpa using (by linarith : (1 : ℝ) ≤ x))
  have hMx : (M : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxM : x < M + 1 := Nat.lt_floor_add_one x
  have hM1' : (1 : ℝ) ≤ M := by exact_mod_cast hM1
  set K : ℕ := ⌊√x⌋₊ with hK
  have hKx : (K : ℝ) ≤ √x := Nat.floor_le (Real.sqrt_nonneg x)
  have hxK : √x < K + 1 := Nat.lt_floor_add_one _
  have hs0 : 0 < √x := Real.sqrt_pos.2 hx0
  have hlogs : Real.log √x = Real.log x / 2 := Real.log_sqrt hx0.le
  have hsP : ∀ p : ℕ, 0 ≤ Formalism.HermitianLattices.GL2a2.sP x p := fun p => by
    unfold Formalism.HermitianLattices.GL2a2.sP Formalism.HermitianLattices.GL2PrimeSums.cn
    exact sum_nonneg fun i _ => mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (by positivity))
  let f₁ : ℕ → ℝ := fun n => if n ∈ Icc 1 K then C ^ 2 * Real.log x ^ 2 else 0
  let f₂ : ℕ → ℝ := fun n => if n ∈ Icc 1 M then 2 * C ^ 2 * Real.log x * Λ n else 0
  let f₃ : ℕ → ℝ := fun n => if n ∈ Ioc M N then 1600 * x ^ 2 * Real.log x * (Λ n / (n : ℝ) ^ 2) else 0
  have hf₁ : ∀ n, 0 ≤ f₁ n := fun n => by simp only [f₁]; split_ifs <;> positivity
  have hf₂ : ∀ n, 0 ≤ f₂ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₂]; split_ifs <;> positivity
  have hf₃ : ∀ n, 0 ≤ f₃ n := fun n => by
    have : 0 ≤ Λ n := vonMangoldt_nonneg
    simp only [f₃]; split_ifs <;> positivity
  have hterm : ∀ p ∈ (Icc 1 N).filter (fun p => p.Prime),
      Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ f₁ p + f₂ p + f₃ p := by
    intro p hp
    simp only [mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp1, hpN⟩, hp⟩ := hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have hall : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ C ^ 2 * Real.log x ^ 2 := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (hsP p) (hC x hx p hp) 2
    by_cases h1 : p ≤ K
    · have : f₁ p = C ^ 2 * Real.log x ^ 2 := if_pos (mem_Icc.2 ⟨hp1, h1⟩)
      linarith [hf₂ p, hf₃ p]
    by_cases h2 : p ≤ M
    · have e : f₂ p = 2 * C ^ 2 * Real.log x * Λ p := if_pos (mem_Icc.2 ⟨hp1, h2⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hKp : (K : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : K + 1 ≤ p)
      have : Real.log √x ≤ Real.log p := Real.log_le_log hs0 (by linarith)
      have h3 : Real.log x ≤ 2 * Real.log p := by linarith
      have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
      nlinarith [hf₁ p, hf₃ p]
    · have e : f₃ p = 1600 * x ^ 2 * Real.log x * (Λ p / (p : ℝ) ^ 2) :=
        if_pos (mem_Ioc.2 ⟨by omega, hpN⟩)
      rw [vonMangoldt_apply_prime hp] at e
      have hMp : (M : ℝ) + 1 ≤ p := by exact_mod_cast (by omega : M + 1 ≤ p)
      have h3 : Formalism.HermitianLattices.GL2a2.sP x p ^ 2 ≤ (2 * x * Real.log p / p) ^ 2 :=
        pow_le_pow_left₀ (hsP p) (hL x hx0 p hp (by linarith)) 2
      have hpN' : (p : ℝ) ≤ N := by exact_mod_cast hpN
      have h4 : Real.log p ≤ 400 * Real.log x := by
        rw [← Real.log_rpow hx0]
        exact Real.log_le_log hp0 (hpN'.trans hNz)
      have h5 := mul_le_mul_of_nonneg_left h4
        (by positivity : 0 ≤ 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2))
      have e2 : (2 * x * Real.log p / p) ^ 2 = 4 * x ^ 2 * (Real.log p / (p : ℝ) ^ 2) * Real.log p := by
        ring
      nlinarith [hf₁ p, hf₂ p]
  have hsum : ∀ (S T : Finset ℕ) (g : ℕ → ℝ), (∀ n, 0 ≤ g n) →
      ∑ n ∈ S, (if n ∈ T then g n else 0) ≤ ∑ n ∈ T, g n := by
    intro S T g hg
    rw [sum_ite_mem]
    exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun n _ _ => hg n
  have s₁ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₁ p ≤ 2 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by positivity).trans ?_
    simp only [sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
    have h1 : Real.log √x ≤ √x - 1 := Real.log_le_sub_one_of_pos hs0
    have h2 : √x * √x = x := Real.mul_self_sqrt hx0.le
    have h3 : (K : ℝ) * Real.log x ≤ 2 * x := by
      have : (K : ℝ) * Real.log x ≤ √x * (2 * √x) :=
        mul_le_mul hKx (by linarith) hlx hs0.le
      linarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ C ^ 2 * Real.log x)
    nlinarith
  have s₂ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₂ p ≤ 4 * C ^ 2 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h4 := mul_le_mul_of_nonneg_left ((hψ' M).trans (by linarith : 2 * (M : ℝ) ≤ 2 * x))
      (by positivity : 0 ≤ 2 * C ^ 2 * Real.log x)
    linarith
  have s₃ : ∑ p ∈ (Icc 1 N).filter (fun p => p.Prime), f₃ p ≤ 12800 * x * Real.log x := by
    refine (hsum _ _ _ fun n => by
      have : 0 ≤ Λ n := vonMangoldt_nonneg
      positivity).trans ?_
    rw [← mul_sum]
    have h1 : 4 / (M : ℝ) ≤ 8 / x := by
      rw [div_le_div_iff₀ (by linarith) hx0]
      linarith
    have h4 := mul_le_mul_of_nonneg_left ((sum_vonMangoldt_div_sq_tail hψ' M hM1 N).trans h1)
      (by positivity : 0 ≤ 1600 * x ^ 2 * Real.log x)
    have e : 1600 * x ^ 2 * Real.log x * (8 / x) = 12800 * x * Real.log x := by
      field_simp
      ring
    linarith
  have := sum_le_sum hterm
  rw [sum_add_distrib, sum_add_distrib] at this
  linarith

end GlobalTheory
end

section
open Finset ArithmeticFunction

namespace GlobalTheory

theorem sum_div_sub_le_two_log_of_partial_sums (a : ℕ → ℝ)
    (h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, a n ≤ 2 * (N : ℝ)) (N : ℕ) :
    ∑ n ∈ Icc 1 N, a n / (n : ℝ) - (∑ n ∈ Icc 1 N, a n) / ((N : ℝ) + 1)
      ≤ 2 * Real.log ((N : ℝ) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hN := h (N + 1)
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)] at hN
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1),
      Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1)]
    push_cast at hN ⊢
    set P := ∑ n ∈ Icc 1 N, a n
    set S := ∑ n ∈ Icc 1 N, a n / (n : ℝ)
    have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
    have h2 : (0 : ℝ) < (N : ℝ) + 1 + 1 := by linarith
    have hlog : 1 / ((N : ℝ) + 1 + 1) ≤ Real.log ((N : ℝ) + 1 + 1) - Real.log ((N : ℝ) + 1) := by
      have := Real.log_le_sub_one_of_pos (div_pos h1 h2)
      rw [Real.log_div h1.ne' h2.ne'] at this
      have e : ((N : ℝ) + 1) / ((N : ℝ) + 1 + 1) - 1 = -(1 / ((N : ℝ) + 1 + 1)) := by
        field_simp; ring
      linarith
    have e : S + a (N + 1) / ((N : ℝ) + 1) - (P + a (N + 1)) / ((N : ℝ) + 1 + 1)
        = (S - P / ((N : ℝ) + 1)) + ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1)) := by
      field_simp; ring
    have h3 : (P + a (N + 1)) / ((N : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ h1]; linarith
    have h4 : ((P + a (N + 1)) / ((N : ℝ) + 1)) * (1 / ((N : ℝ) + 1 + 1))
        ≤ 2 * (1 / ((N : ℝ) + 1 + 1)) :=
      mul_le_mul_of_nonneg_right h3 (by positivity)
    rw [e]
    linarith

theorem chebyshev_coefficient_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSumC := by
  intro hψ
  refine ⟨806, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have h : ∀ N : ℕ, ∑ n ∈ Icc 1 N, (Λ n : ℝ) ≤ 2 * (N : ℝ) := fun N => by
    simpa using hψ N (Nat.cast_nonneg N)
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hNdef
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : (0 : ℝ) < (N : ℝ) + 1 := by linarith
  have hA := sum_div_sub_le_two_log_of_partial_sums (fun n => (Λ n : ℝ)) h N
  have hB : (∑ n ∈ Icc 1 N, (Λ n : ℝ)) / ((N : ℝ) + 1) ≤ 2 := by
    rw [div_le_iff₀ h1]; linarith [h N]
  have hz1 : 1 ≤ x ^ (400 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hNz : (N : ℝ) ≤ x ^ (400 : ℝ) := Nat.floor_le (by linarith)
  have hl2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2' := Real.log_two_gt_d9
  have hC : Real.log ((N : ℝ) + 1) ≤ Real.log 2 + 400 * Real.log x := by
    have : Real.log ((N : ℝ) + 1) ≤ Real.log (2 * x ^ (400 : ℝ)) :=
      Real.log_le_log h1 (by linarith)
    rw [Real.log_mul (by norm_num) (by linarith), Real.log_rpow hx0] at this
    exact this
  have hD : ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) ≤ 806 * Real.log x := by
    linarith
  calc ∑ n ∈ Icc 1 N, Formalism.HermitianLattices.GL2PrimeSums.cn x n
      ≤ ∑ n ∈ Icc 1 N, x * ((Λ n : ℝ) / (n : ℝ)) := by
        refine Finset.sum_le_sum fun n _ => ?_
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        calc (Λ n : ℝ) * min 1 (x / (n : ℝ)) ≤ (Λ n : ℝ) * (x / (n : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) vonMangoldt_nonneg
          _ = x * ((Λ n : ℝ) / (n : ℝ)) := by ring
    _ = x * ∑ n ∈ Icc 1 N, (Λ n : ℝ) / (n : ℝ) := by rw [Finset.mul_sum]
    _ ≤ x * (806 * Real.log x) := mul_le_mul_of_nonneg_left hD hx0.le
    _ = 806 * x * Real.log x := by ring

end GlobalTheory
end

section
open Finset ArithmeticFunction

namespace GlobalTheory

open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem meanSq_cn_nonneg {x : ℝ} (hx : 0 ≤ x) (n : ℕ) : 0 ≤ cn x n :=
  mul_nonneg vonMangoldt_nonneg (le_min zero_le_one (div_nonneg hx (Nat.cast_nonneg n)))

theorem meanSq_cn_eq_zero (x : ℝ) {n : ℕ} (hn : ¬ IsPrimePow n) : cn x n = 0 := by
  unfold cn
  rw [vonMangoldt_eq_zero_iff.2 hn, zero_mul]

theorem meanSq_fiber_le {x : ℝ} (hx : 0 ≤ x) {p : ℕ} (hp : p.Prime) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, (if n.minFac = p then cn x n else 0) ≤ sP x p := by
  classical
  unfold sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  rw [← Finset.sum_image (s := (Icc 1 N).filter (fun i => p ^ i ≤ N)) (g := fun i => p ^ i)
    (f := fun n => cn x n) (fun a _ b _ h => Nat.pow_right_injective hp.two_le h)]
  rw [← Finset.sum_filter]
  rw [← Finset.sum_filter_of_ne (p := fun n => IsPrimePow n)
    (fun n _ h => by by_contra h'; exact h (meanSq_cn_eq_zero x h'))]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun n _ _ => meanSq_cn_nonneg hx n)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hn
  obtain ⟨p', i, hp', hi, rfl⟩ := (isPrimePow_nat_iff _).1 h4
  rw [hp'.pow_minFac hi.ne'] at h3
  subst h3
  refine Finset.mem_image.2 ⟨i, ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hi, (Nat.lt_pow_self hp.one_lt).le.trans h2⟩, h2⟩

theorem meanSq_expand (I PPs : Finset ℕ) (c : ℕ → ℝ) (hc : ∀ n, 0 ≤ c n) (κ : ℕ → ℂ) (hκ : ∀ n, ‖κ n‖ ≤ 1) :
    (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2) / PPs.card ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' *
        |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card| := by
  have h1 : ((∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ I, ∑ n' ∈ I, ((c n * c n' : ℝ) : ℂ) * (κ n * (starRingEnd ℂ) (κ n')) *
        ((∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ) : ℝ) : ℂ) := by
    push_cast
    simp_rw [← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n' _ => ?_
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [jacobiSym.mul_left]
    simp only [map_mul, Complex.conj_ofReal, map_intCast]
    push_cast
    ring
  have h2 : (∑ q ∈ PPs, ‖∑ n ∈ I, (c n : ℂ) * κ n * (jacobiSym (n : ℤ) q : ℂ)‖ ^ 2 : ℝ) ≤
      ∑ n ∈ I, ∑ n' ∈ I, c n * c n' * |∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)| := by
    refine (le_abs_self _).trans ?_
    rw [← Real.norm_eq_abs, ← Complex.norm_real, h1]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n' _ => ?_)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hc n) (hc n'))]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    exact mul_le_of_le_one_right (mul_nonneg (hc n) (hc n'))
      (mul_le_one₀ (hκ n) (norm_nonneg _) (hκ n'))
  refine (div_le_div_of_nonneg_right h2 (Nat.cast_nonneg _)).trans (le_of_eq ?_)
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun n' _ => ?_
  rw [abs_div, Nat.abs_cast, mul_div_assoc]

theorem meanSq_abs_mean_le_one (PPs : Finset ℕ) (a : ℤ) :
    |(∑ q ∈ PPs, (jacobiSym a q : ℝ)) / PPs.card| ≤ 1 := by
  rw [abs_div, Nat.abs_cast]
  refine div_le_one_of_le₀ ?_ (Nat.cast_nonneg _)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have : ∀ q ∈ PPs, |(jacobiSym a q : ℝ)| ≤ 1 := by
    intro q _
    rcases jacobiSym.trichotomy a q with h | h | h <;> simp [h]
  simpa using Finset.sum_le_card_nsmul _ _ _ this

theorem meanSq_primeFactors_outPart (m₀ m : ℕ) :
    (outPart m₀ m).primeFactors = m.primeFactors.filter (fun p => ¬ p ∣ m₀ ∧ Odd (m.factorization p)) := by
  unfold outPart
  exact Nat.primeFactors_prod fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1

theorem meanSq_card_primeFactors_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n') :
    (outPart m₀ (n * n')).primeFactors.card ≤ 2 := by
  rw [meanSq_primeFactors_outPart]
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.primeFactors_mul hn.ne_zero hn'.ne_zero]
  refine (Finset.card_union_le _ _).trans ?_
  rw [isPrimePow_iff_card_primeFactors_eq_one.1 hn, isPrimePow_iff_card_primeFactors_eq_one.1 hn']

theorem meanSq_mem_outPart (m₀ : ℕ) {n n' : ℕ} (hn : IsPrimePow n) (hn' : IsPrimePow n')
    (hne : n.minFac ≠ n'.minFac) (hsq : ¬ IsSquare n) (hm : ¬ n.minFac ∣ m₀) :
    n.minFac ∈ (outPart m₀ (n * n')).primeFactors := by
  obtain ⟨p, i, hp, hi, rfl⟩ := (isPrimePow_nat_iff _).1 hn
  obtain ⟨p', j, hp', hj, rfl⟩ := (isPrimePow_nat_iff _).1 hn'
  rw [hp.pow_minFac hi.ne'] at hne hm ⊢
  rw [hp'.pow_minFac hj.ne'] at hne
  rw [meanSq_primeFactors_outPart, Finset.mem_filter]
  refine ⟨Nat.mem_primeFactors.2 ⟨hp, Dvd.dvd.mul_right (dvd_pow_self p hi.ne') _,
    mul_ne_zero hn.ne_zero hn'.ne_zero⟩, hm, ?_⟩
  rw [Nat.factorization_mul hn.ne_zero hn'.ne_zero, hp.factorization_pow, hp'.factorization_pow]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hne, add_zero]
  rw [← Nat.not_even_iff_odd]
  exact fun h => hsq (h.isSquare_pow p)

theorem meanSq_pairs {x : ℝ} (hx : 0 ≤ x) (m₀ : ℕ) (hm₀ : 0 < m₀) (nStar : ℕ) (A : ℕ → ℕ → ℝ) (η S : ℝ)
    (hη : 0 ≤ η) (hS0 : 0 ≤ S) (hS : ∀ p : ℕ, p.Prime → sP x p ≤ S) (hA1 : ∀ n n', A n n' ≤ 1)
    (hA : ∀ n n' : ℕ, n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ → n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊ →
      IsPrimePow n → IsPrimePow n' → outPart m₀ (n * n') ≠ 1 → outPart m₀ (n * n') ≠ nStar → A n n' ≤ η) :
    ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, ∑ n' ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n * cn x n' * A n n' ≤
      η * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 +
      ∑ p ∈ (Icc 1 ⌊x ^ (400 : ℝ)⌋₊).filter (fun p => p.Prime), sP x p ^ 2 +
      (Rsum x m₀ + 2 * S) ^ 2 := by
  classical
  have hfib := fun p hp => meanSq_fiber_le (p := p) hx hp
  have hc := meanSq_cn_nonneg hx
  unfold Rsum
  set N := ⌊x ^ (400 : ℝ)⌋₊ with hN
  set f : ℕ → ℕ → ℝ := fun p n => if n.minFac = p then cn x n else 0 with hf
  have hf0 : ∀ p n, 0 ≤ f p n := fun p n => by
    simp only [hf]; split_ifs
    exacts [hc n, le_rfl]
  set P := (Icc 1 N).filter (fun p => p.Prime) with hP
  set M := m₀.primeFactors.filter (fun p => p ≤ N) with hM
  set T : Finset ℕ := if nStar.primeFactors.card ≤ 2 then nStar.primeFactors else ∅ with hT
  have hTcard : T.card ≤ 2 := by
    simp only [hT]; split_ifs with h
    exacts [h, by simp]
  have hTprime : ∀ p ∈ T, p.Prime := by
    intro p hp
    simp only [hT] at hp; split_ifs at hp with h
    exacts [Nat.prime_of_mem_primeFactors hp, absurd hp (Finset.notMem_empty p)]
  set U : ℕ → ℝ := fun n => (if IsSquare n then cn x n else 0) + ∑ p ∈ M, f p n + ∑ p ∈ T, f p n with hU
  have hU1 : ∀ n, 0 ≤ (if IsSquare n then cn x n else 0) := fun n => by
    split_ifs
    exacts [hc n, le_rfl]
  have hU2 : ∀ (B : Finset ℕ) n, 0 ≤ ∑ p ∈ B, f p n := fun B n => Finset.sum_nonneg fun p _ => hf0 p n
  have hU0 : ∀ n, 0 ≤ U n := fun n => add_nonneg (add_nonneg (hU1 n) (hU2 M n)) (hU2 T n)
  have hsingle : ∀ (B : Finset ℕ) (n : ℕ), n.minFac ∈ B → cn x n ≤ ∑ p ∈ B, f p n := by
    intro B n h
    have := Finset.single_le_sum (f := fun p => f p n) (fun p _ => hf0 p n) h
    simpa [hf] using this
  have hUc : ∀ n n' : ℕ, n ∈ Icc 1 N → IsPrimePow n → IsPrimePow n' → n.minFac ≠ n'.minFac →
      (outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar) → cn x n ≤ U n := by
    intro n n' hn hpn hpn' hne ho
    have a1 := hU1 n
    have a2 := hU2 M n
    have a3 := hU2 T n
    simp only [hU]
    by_cases hsq : IsSquare n
    · rw [if_pos hsq]; linarith
    by_cases hm : n.minFac ∣ m₀
    · have : n.minFac ∈ M := Finset.mem_filter.2
        ⟨Nat.mem_primeFactors.2 ⟨Nat.minFac_prime hpn.ne_one, hm, hm₀.ne'⟩,
          (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩
      have := hsingle M n this
      linarith
    have h1 := meanSq_mem_outPart m₀ hpn hpn' hne hsq hm
    have h2 := meanSq_card_primeFactors_outPart m₀ hpn hpn'
    rcases ho with ho | ho
    · rw [ho] at h1; simp at h1
    · rw [ho] at h1 h2
      have : n.minFac ∈ T := by simp only [hT]; rw [if_pos h2]; exact h1
      have := hsingle T n this
      linarith
  have hpt : ∀ n ∈ Icc 1 N, ∀ n' ∈ Icc 1 N, cn x n * cn x n' * A n n' ≤
      η * (cn x n * cn x n') + ∑ p ∈ P, f p n * f p n' + U n * U n' := by
    intro n hn n' hn'
    have b1 : 0 ≤ η * (cn x n * cn x n') := mul_nonneg hη (mul_nonneg (hc n) (hc n'))
    have b2 : 0 ≤ ∑ p ∈ P, f p n * f p n' := Finset.sum_nonneg fun p _ => mul_nonneg (hf0 p n) (hf0 p n')
    have b3 : 0 ≤ U n * U n' := mul_nonneg (hU0 n) (hU0 n')
    have b4 : cn x n * cn x n' * A n n' ≤ cn x n * cn x n' :=
      mul_le_of_le_one_right (mul_nonneg (hc n) (hc n')) (hA1 n n')
    by_cases hpn : IsPrimePow n
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn]; ring
      linarith
    by_cases hpn' : IsPrimePow n'
    swap
    · have : cn x n * cn x n' * A n n' = 0 := by rw [meanSq_cn_eq_zero x hpn']; ring
      linarith
    by_cases hne : n.minFac = n'.minFac
    · have hmem : n.minFac ∈ P := Finset.mem_filter.2
        ⟨Finset.mem_Icc.2 ⟨Nat.minFac_pos n, (Nat.minFac_le hpn.pos).trans (Finset.mem_Icc.1 hn).2⟩,
          Nat.minFac_prime hpn.ne_one⟩
      have := Finset.single_le_sum (f := fun p => f p n * f p n')
        (fun p _ => mul_nonneg (hf0 p n) (hf0 p n')) hmem
      have e : f n.minFac n * f n.minFac n' = cn x n * cn x n' := by
        simp only [hf]; rw [if_pos trivial, if_pos hne.symm]
      simp only [e] at this
      linarith
    by_cases ho : outPart m₀ (n * n') = 1 ∨ outPart m₀ (n * n') = nStar
    · have c1 := hUc n n' hn hpn hpn' hne ho
      have c2 := hUc n' n hn' hpn' hpn (Ne.symm hne) (by rwa [mul_comm n' n])
      have := mul_le_mul c1 c2 (hc n') (hU0 n)
      linarith
    · rw [not_or] at ho
      have := mul_le_mul_of_nonneg_left (hA n n' hn hn' hpn hpn' ho.1 ho.2) (mul_nonneg (hc n) (hc n'))
      linarith
  refine (Finset.sum_le_sum fun n hn => Finset.sum_le_sum fun n' hn' => hpt n hn n' hn').trans ?_
  simp_rw [Finset.sum_add_distrib]
  refine add_le_add (add_le_add (le_of_eq ?_) ?_) ?_
  · rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
    simp_rw [Finset.mul_sum]
  · have : ∑ n ∈ Icc 1 N, ∑ n' ∈ Icc 1 N, ∑ p ∈ P, f p n * f p n' =
        ∑ p ∈ P, (∑ n ∈ Icc 1 N, f p n) ^ 2 := by
      simp_rw [sq, Finset.sum_mul_sum]
      rw [Finset.sum_comm (s := P)]
      exact Finset.sum_congr rfl fun n _ => Finset.sum_comm
    rw [this]
    refine Finset.sum_le_sum fun p hp => ?_
    exact pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hf0 p n) (hfib p (Finset.mem_filter.1 hp).2) 2
  · rw [← Finset.sum_mul_sum, ← sq]
    refine pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => hU0 n) ?_ 2
    simp only [hU]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_filter,
      Finset.sum_comm (t := M), Finset.sum_comm (t := T)]
    refine add_le_add (add_le_add le_rfl (Finset.sum_le_sum fun p hp =>
      hfib p (Nat.prime_of_mem_primeFactors (Finset.mem_filter.1 hp).1))) ?_
    have h1 : ∑ p ∈ T, ∑ n ∈ Icc 1 N, f p n ≤ T.card • S :=
      Finset.sum_le_card_nsmul _ _ _ fun p hp => (hfib p (hTprime p hp)).trans (hS p (hTprime p hp))
    rw [nsmul_eq_mul] at h1
    refine h1.trans (mul_le_mul_of_nonneg_right ?_ hS0)
    exact_mod_cast hTcard

theorem meanSq_core : Formalism.HermitianLattices.GL2PrimeSums.JacobiTwistedMeanSquareBound := by
  intro hψ ε hε hε1 C' c' hC' hc'
  obtain ⟨C₁, hC₁⟩ := GlobalTheory.chebyshev_coefficient_sum_bound hψ
  obtain ⟨C₂, hC₂⟩ := GlobalTheory.prime_sum_square_bound hψ
  obtain ⟨C₃, hC₃⟩ := GlobalTheory.remainder_smooth_rough_bound hψ
  obtain ⟨C₄, hC₄⟩ := GlobalTheory.prime_power_von_mangoldt_sum_bound
  refine ⟨max (Real.exp 1) (Real.exp (2 / c')), C' * C₁ ^ 2 + C₂ + (5 * |C₃| + 4 * |C₄|) ^ 2, ?_⟩
  intro x hx m₀ PPs κ nStar _ hm₀ hpr _ _ _ _ hκ hμ
  have hxe : Real.exp 1 ≤ x := (le_max_left _ _).trans hx
  have hx2 : 2 ≤ x := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hL1 : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hxe
  have hL2 : 2 / c' ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 ((le_max_right _ _).trans hx)
  have hL0 : 0 ≤ Real.log x := by linarith
  have h1 := meanSq_expand (Icc 1 ⌊x ^ (400 : ℝ)⌋₊) PPs (cn x) (meanSq_cn_nonneg hx0.le) κ hκ
  have h2 := meanSq_pairs hx0.le m₀ hm₀ nStar
    (fun n n' => |(∑ q ∈ PPs, (jacobiSym ((n * n' : ℕ) : ℤ) q : ℝ)) / PPs.card|)
    (C' * Real.exp (-c' * Real.log x ^ 2)) (|C₄| * Real.log x) (by positivity) (by positivity)
    (fun p hp => (hC₄ x hx2 p hp).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hL0))
    (fun n n' => meanSq_abs_mean_le_one PPs _) hμ
  unfold sqSum
  refine (h1.trans h2).trans ?_
  have e1 : C' * Real.exp (-c' * Real.log x ^ 2) * (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤
      C' * C₁ ^ 2 * x * Real.log x := by
    have s1 : (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, cn x n) ^ 2 ≤ (C₁ * x * Real.log x) ^ 2 :=
      pow_le_pow_left₀ (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n) (hC₁ x hx2) 2
    have s2 : Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x) ≤ 1 := by
      have t1 : Real.log x ≤ x := (Real.log_le_sub_one_of_pos hx0).trans (by linarith)
      have t2 : 2 ≤ c' * Real.log x := by rw [div_le_iff₀ hc'] at hL2; linarith
      have t3 : x * x = Real.exp (2 * Real.log x) := by
        rw [two_mul, Real.exp_add, Real.exp_log hx0]
      calc Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)
          ≤ Real.exp (-c' * Real.log x ^ 2) * (x * x) := by gcongr
        _ = Real.exp (-c' * Real.log x ^ 2 + 2 * Real.log x) := by rw [t3, Real.exp_add]
        _ ≤ 1 := by
          rw [Real.exp_le_one_iff]
          nlinarith [mul_le_mul_of_nonneg_right t2 hL0]
    calc _ ≤ C' * Real.exp (-c' * Real.log x ^ 2) * (C₁ * x * Real.log x) ^ 2 := by gcongr
      _ = (C' * C₁ ^ 2 * x * Real.log x) * (Real.exp (-c' * Real.log x ^ 2) * (x * Real.log x)) := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) s2
  have e2 := hC₂ x hx2
  have e3 : (Rsum x m₀ + 2 * (|C₄| * Real.log x)) ^ 2 ≤ (5 * |C₃| + 4 * |C₄|) ^ 2 * x * Real.log x := by
    have r0 : 0 ≤ Rsum x m₀ := by
      unfold Rsum sP
      exact add_nonneg (Finset.sum_nonneg fun n _ => meanSq_cn_nonneg hx0.le n)
        (Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun i _ => meanSq_cn_nonneg hx0.le _)
    have r1 := hC₃ ε hε hε1 x hx2 m₀ hm₀ hpr
    have r2 : Real.log x ≤ x ^ ((1 : ℝ) / 2) / (1 / 2) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r3 : Real.log x ≤ x ^ ((1 : ℝ) / 4) / (1 / 4) := Real.log_le_rpow_div hx0.le (by norm_num)
    have r4 : x ^ (ε / 5) ≤ x ^ ((1 : ℝ) / 4) := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
    have r5 : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    have r6 : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by
      rw [sq, ← Real.rpow_add hx0]; norm_num
    have r7 : x ^ (ε / 5) * Real.log x ≤ 4 * x ^ ((1 : ℝ) / 2) := by
      have := mul_le_mul r4 r3 hL0 (by positivity)
      rw [← r5]; linarith
    have r8 : Rsum x m₀ ≤ |C₃| * (5 * x ^ ((1 : ℝ) / 2)) := by
      refine r1.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)).trans ?_)
      exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    have r9 : |C₄| * Real.log x ≤ |C₄| * (2 * x ^ ((1 : ℝ) / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
    calc _ ≤ ((5 * |C₃| + 4 * |C₄|) * x ^ ((1 : ℝ) / 2)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by linarith) 2
      _ = (5 * |C₃| + 4 * |C₄|) ^ 2 * x := by rw [mul_pow, r6]
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hL1
  linarith

end GlobalTheory
end
