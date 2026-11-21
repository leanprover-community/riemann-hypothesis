import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MassDegTypeLeCycleType
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CentralBinomLePowCardPrimesBetween

section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Equiv Finset

theorem card_cycleType_cons_mul (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (m : Multiset ℕ)
    (hpm : p ∉ m) (hs : m.sum ≤ N - p) (h2 : ∀ a ∈ m, 2 ≤ a) :
    (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card * p * (N - p).factorial
      = N.factorial * (univ.filter fun σ : Perm (Fin (N - p)) => σ.cycleType = m).card := by
  have hA := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin N) (p ::ₘ m)
  have hB := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (N - p)) m
  rw [Fintype.card_fin] at hA hB
  have hcA : (p ::ₘ m).sum ≤ N ∧ ∀ a ∈ p ::ₘ m, 2 ≤ a := by
    refine ⟨by rw [Multiset.sum_cons]; omega, fun a ha => ?_⟩
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hp
    · exact h2 a ha
  rw [if_pos hcA] at hA
  rw [if_pos ⟨hs, h2⟩] at hB
  have hsum : N - (p ::ₘ m).sum = N - p - m.sum := by
    rw [Multiset.sum_cons, Nat.sub_sub]
  have hfac : ∏ n ∈ (p ::ₘ m).toFinset, ((p ::ₘ m).count n).factorial =
      ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hpm), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hpm, zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hne : n ≠ p := fun h => hpm (h ▸ Multiset.mem_toFinset.1 hn)
    rw [Multiset.count_cons_of_ne hne]
  rw [hsum, Multiset.prod_cons, hfac] at hA
  rw [← hB, ← hA]
  ring

theorem card_mem_cycleType_mul (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by
  have hTm : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
      m.sum ≤ N - p ∧ ∀ a ∈ m, 2 ≤ a := by
    intro m hm
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨?_, fun a ha => Perm.two_le_of_mem_cycleType ha⟩
    simpa using τ.sum_cycleType_le
  have hpT : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType, p ∉ m := by
    intro m hm hpm
    have h1 := Multiset.le_sum_of_mem hpm
    have h2 := (hTm m hm).1
    omega
  have hfib : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card =
      ∑ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
        (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => σ.cycleType.erase p)
      (t := (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rw [← h2, Multiset.cons_erase h1]
      · intro h
        rw [h]
        exact ⟨Multiset.mem_cons_self _ _, Multiset.erase_cons_head _ _⟩
    · intro σ hσ
      have hσ' : p ∈ σ.cycleType := by simpa using hσ
      have hsum := Multiset.sum_erase hσ'
      have hle := σ.sum_cycleType_le
      rw [Fintype.card_fin] at hle
      have hc : (σ.cycleType.erase p).sum ≤ Fintype.card (Fin (N - p)) ∧
          ∀ a ∈ σ.cycleType.erase p, 2 ≤ a := by
        refine ⟨by rw [Fintype.card_fin]; omega, fun a ha => ?_⟩
        exact Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)
      obtain ⟨τ, hτ⟩ := (Perm.exists_with_cycleType_iff (Fin (N - p))).2 hc
      exact Finset.mem_image.2 ⟨τ, Finset.mem_univ _, hτ⟩
  have hmain : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p * (N - p).factorial
      = N.factorial * (N - p).factorial := by
    rw [hfib, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_congr rfl fun m hm =>
        card_cycleType_cons_mul N p hp hpN m (hpT m hm) (hTm m hm).1 (hTm m hm).2,
      ← Finset.mul_sum]
    congr 1
    have hc := Finset.card_eq_sum_card_image Perm.cycleType (univ : Finset (Perm (Fin (N - p))))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc
    exact hc.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hmain

theorem card_perm_long_cycle : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by
  intro N p hN hpN
  rcases Nat.lt_or_ge p 2 with hp | hp
  · obtain rfl : p = 1 := by omega
    obtain rfl : N = 1 := by omega
    have hall : ∀ σ : Equiv.Perm (Fin 1), 1 ∈ σ.partition.parts := by
      intro σ
      have hs : σ.partition.parts.sum = 1 := σ.partition.parts_sum.trans (Fintype.card_fin 1)
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := σ.partition.parts)
        (fun h => by rw [h, Multiset.sum_zero] at hs; exact absurd hs (by norm_num))
      have h1 := σ.partition.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      obtain rfl : a = 1 := by omega
      exact ha
    rw [Finset.filter_true_of_mem (fun σ _ => hall σ), Finset.card_univ, Fintype.card_perm]
    simp
  · have hiff : ∀ σ : Equiv.Perm (Fin N), p ∈ σ.partition.parts ↔ p ∈ σ.cycleType := by
      intro σ
      rw [Equiv.Perm.parts_partition, Multiset.mem_add]
      constructor
      · rintro (h | h)
        · exact h
        · have := Multiset.eq_of_mem_replicate h
          omega
      · exact Or.inl
    simp_rw [hiff]
    exact card_mem_cycleType_mul N p hp hN hpN

end GlobalTheory.BadShare
end

section
open Polynomial Classical GlobalTheory.BadShare
namespace GlobalTheory.BadShare

theorem add_le_sum_of_mem_of_ne {s : Multiset ℕ} {p q : ℕ} (hp : p ∈ s) (hq : q ∈ s) (h : p ≠ q) : p + q ≤ s.sum := by
  obtain ⟨t, rfl⟩ := Multiset.exists_cons_of_mem hp
  have hq' : q ∈ t := (Multiset.mem_cons.mp hq).resolve_left (Ne.symm h)
  obtain ⟨u, rfl⟩ := Multiset.exists_cons_of_mem hq'
  rw [Multiset.sum_cons, Multiset.sum_cons, ← add_assoc]
  exact Nat.le_add_right _ _

theorem card_perm_no_long_cycle (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]

theorem mass_not_hasPrimeFactor_le : ∀ (g : ℕ) [Fact g.Prime], ∀ N : ℕ, 100000 ≤ N →
    (mass g N fun f => ¬ HasPrimeFactor g N f) ≤ 1 - 1 / (10 * Real.log N) := by
  intro g _ N hN
  set S := (Finset.range (N + 1)).filter (fun p => p.Prime ∧ N < 2 * p ∧ p + 3 ≤ N) with hSdef
  have hS : ∀ p ∈ S, N < 2 * p := fun p hp => (Finset.mem_filter.mp hp).2.2.1
  have hSN : ∀ p ∈ S, p ≤ N := fun p hp =>
    Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
  have hmono : (mass g N fun f => ¬ HasPrimeFactor g N f) ≤
      mass g N fun f => ∀ p ∈ S, p ∉ degType g f := by
    have hsub : (sqSet g N).filter (fun f => ¬ HasPrimeFactor g N f) ⊆
        (sqSet g N).filter (fun f => ∀ p ∈ S, p ∉ degType g f) := by
      intro f hf
      rw [Finset.mem_filter] at hf ⊢
      refine ⟨hf.1, ?_⟩
      intro p hp hpf
      apply hf.2
      unfold degType at hpf
      unfold HasPrimeFactor
      obtain ⟨h, hh, rfl⟩ := Multiset.mem_map.mp hpf
      obtain ⟨-, hpr, h2, h3⟩ := Finset.mem_filter.mp hp
      exact ⟨h, UniqueFactorizationMonoid.irreducible_of_normalized_factor h hh,
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hh, hpr, h2, h3⟩
    unfold mass
    convert Finset.sum_le_sum_of_subset_of_nonneg (f := fun f => ((torusCard g f : ℝ))⁻¹) hsub
      (fun f _ _ => by positivity)
    rfl
  have hT := GlobalTheory.T.mass_degType_le_card_cycleType_div g N (fun m : Multiset ℕ => ∀ p ∈ S, p ∉ m)
  have hcount := card_perm_no_long_cycle N S hS
  have hlong : ∀ p ∈ S, ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      p ∈ σ.partition.parts).card : ℝ) = N.factorial / p := by
    intro p hp
    have hp0 : 0 < p := by have := hS p hp; omega
    have hp0' : (p : ℝ) ≠ 0 := by exact_mod_cast hp0.ne'
    rw [eq_div_iff hp0']
    exact_mod_cast card_perm_long_cycle N p (hS p hp) (hSN p hp)
  have hfac : (N.factorial : ℝ) ≠ 0 := by positivity
  have hratio : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
      ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) / N.factorial = 1 - ∑ p ∈ S, (1 : ℝ) / p := by
    have hc : ((Finset.univ.filter fun σ : Equiv.Perm (Fin N) =>
        ∀ p ∈ S, p ∉ σ.partition.parts).card : ℝ) = N.factorial - ∑ p ∈ S, (N.factorial : ℝ) / p := by
      rw [← Finset.sum_congr rfl hlong]
      have := congrArg (fun n : ℕ => (n : ℝ)) hcount
      push_cast at this
      linarith
    rw [hc, sub_div, div_self hfac, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [div_right_comm, div_self hfac]
  have hprimes := inv_log_le_sum_inv_primes_between N hN
  calc _ ≤ _ := hmono
    _ ≤ _ := hT
    _ = 1 - ∑ p ∈ S, (1 : ℝ) / p := by convert hratio
    _ ≤ 1 - 1 / (10 * Real.log N) := by linarith

end GlobalTheory.BadShare
end
