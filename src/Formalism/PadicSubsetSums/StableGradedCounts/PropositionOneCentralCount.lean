import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Formalism.GaloisIrreducibility.NoSolvableTransitive

section
open Finset

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem bad_primes_cardinality : BBCard := by
  classical
  intro g N hg
  set T : ℕ → Finset ℕ := fun d => (Finset.range (g ^ N + 1)).filter (fun l =>
    l.Prime ∧ g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) with hT
  have hTd : ∀ d ∈ Finset.Icc 1 N, (T d).card ≤ 3 := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    apply Formalism.GaloisIrreducibility.bbAtMostThree g d (T d) hg hd.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      exact hl.2.1
    · intro l hl
      simp only [hT, Finset.mem_filter] at hl
      have h1 : g ^ d < (l ^ padicValNat l (g ^ d - 1)) ^ 4 := by
        rw [← pow_mul, mul_comm]; exact hl.2.2
      have h2 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 = (g : ℝ) ^ d := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        have : (d : ℝ) / 4 * ((4 : ℕ) : ℝ) = (d : ℝ) := by push_cast; ring
        rw [this, Real.rpow_natCast]
      have h3 : ((g : ℝ) ^ ((d : ℝ) / 4)) ^ 4 <
          (((l ^ padicValNat l (g ^ d - 1) : ℕ) : ℝ)) ^ 4 := by
        rw [h2]; exact_mod_cast h1
      exact lt_of_pow_lt_pow_left₀ 4 (by positivity) h3
  have hsub : (Finset.range (g ^ N + 1)).filter (fun l =>
      l.Prime ∧ ∃ d ∈ Finset.Icc 1 N, g ^ d < l ^ (4 * padicValNat l (g ^ d - 1))) ⊆
      (Finset.Icc 1 N).biUnion T := by
    intro l hl
    simp only [Finset.mem_filter] at hl
    obtain ⟨hr, hp, d, hd, hlt⟩ := hl
    rw [Finset.mem_biUnion]
    exact ⟨d, hd, by simp only [hT, Finset.mem_filter]; exact ⟨hr, hp, hlt⟩⟩
  have hcard : ((Finset.Icc 1 N).biUnion T).card ≤ 3 * N := by
    calc ((Finset.Icc 1 N).biUnion T).card ≤ ∑ d ∈ Finset.Icc 1 N, (T d).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ _d ∈ Finset.Icc 1 N, 3 := Finset.sum_le_sum hTd
      _ = 3 * N := by simp [mul_comm]
  unfold BB
  calc _ ≤ _ + 1 := Finset.card_insert_le _ _
    _ ≤ 3 * N + 1 := by
      have := (Finset.card_le_card hsub).trans hcard
      convert Nat.add_le_add_right this 1

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

open Formalism.GaloisIrreducibility (IsSubSum IsOrbit)

theorem bad_primes_divides : BBDivides := by
  intro l g d j Y hl hd hg hY h1 h2 h3
  have hj : j ≤ padicValNat l (g ^ d - 1) := by
    by_contra hlt
    push Not at hlt
    have h5 := h3 _ hlt
    have h4 : g ≤ g ^ d := Nat.le_self_pow (by omega) g
    have h6 : (l : ℝ) ^ (4 * padicValNat l (g ^ d - 1)) ≤ (g : ℝ) := h5.trans hY
    have h7 : l ^ (4 * padicValNat l (g ^ d - 1)) ≤ g := by exact_mod_cast h6
    omega
  exact (pow_dvd_pow l hj).trans pow_padicValNat_dvd

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem card_class_le (S : Finset ℕ) (Y : ℝ) (M r : ℕ) (hM : 0 < M) (hY : 0 ≤ Y)
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ g % M = r) :
    (S.card : ℝ) ≤ Y / M + 1 := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]; positivity
  set g0 := S.min' hne with hg0def
  have hg0 : g0 ∈ S := S.min'_mem hne
  have hdvd : ∀ a ∈ S, g0 ≤ a ∧ M ∣ a - g0 := by
    intro a ha
    have ha0 : g0 ≤ a := S.min'_le a ha
    refine ⟨ha0, (Nat.modEq_iff_dvd' ha0).mp ?_⟩
    unfold Nat.ModEq
    rw [(hS g0 hg0).2.2, (hS a ha).2.2]
  have hinj : Set.InjOn (fun g => (g - g0) / M) (S : Set ℕ) := by
    intro a ha b hb hab
    obtain ⟨ha0, s, hs⟩ := hdvd a ha
    obtain ⟨hb0, t, ht⟩ := hdvd b hb
    simp only at hab
    rw [hs, ht, Nat.mul_div_cancel_left _ hM, Nat.mul_div_cancel_left _ hM] at hab
    subst hab
    omega
  have himg : S.image (fun g => (g - g0) / M) ⊆ Finset.range (⌊Y / M⌋₊ + 1) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    apply Nat.le_floor
    have ha0 : g0 ≤ a := (hdvd a ha).1
    have h1 : (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := Nat.cast_div_le
    have h2 : ((a - g0 : ℕ) : ℝ) = (a : ℝ) - g0 := Nat.cast_sub ha0
    have h3 : (a : ℝ) - g0 ≤ Y := by linarith [(hS a ha).2.1, (hS g0 hg0).1]
    have hM' : (0 : ℝ) < M := by exact_mod_cast hM
    calc (((a - g0) / M : ℕ) : ℝ) ≤ ((a - g0 : ℕ) : ℝ) / M := h1
      _ ≤ Y / M := by rw [h2]; exact div_le_div_of_nonneg_right h3 hM'.le
  have hc : S.card ≤ ⌊Y / M⌋₊ + 1 := by
    rw [← Finset.card_image_of_injOn hinj]
    simpa using Finset.card_le_card himg
  have hfl : ((⌊Y / M⌋₊ : ℕ) : ℝ) ≤ Y / M := Nat.floor_le (by positivity)
  calc (S.card : ℝ) ≤ ((⌊Y / M⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hc
    _ ≤ Y / M + 1 := by push_cast; linarith

theorem div_le_rpow (Y M : ℝ) (hY : 1 ≤ Y) (hM : 0 < M) (h : Y < M ^ 4) :
    Y / M ≤ Y ^ ((3 : ℝ) / 4) := by
  have hY0 : 0 < Y := by linarith
  have h1 : Y ^ ((1 : ℝ) / 4) ≤ M := by
    by_contra hcon
    push Not at hcon
    have h4 := pow_le_pow_left₀ hM.le hcon.le 4
    have h5 : (Y ^ ((1 : ℝ) / 4)) ^ 4 = Y := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [h5] at h4
    linarith
  have h2 : Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hY0]; norm_num
  rw [div_le_iff₀ hM]
  calc Y = Y ^ ((3 : ℝ) / 4) * Y ^ ((1 : ℝ) / 4) := h2
    _ ≤ Y ^ ((3 : ℝ) / 4) * M := by
        exact mul_le_mul_of_nonneg_left h1 (Real.rpow_nonneg hY0.le _)

theorem card_pow_class_le (S : Finset ℕ) (Y : ℝ) (l j d : ℕ) (hl : l.Prime) (hd : 1 ≤ d)
    (hY : 1 ≤ Y) (hj : Y < (l : ℝ) ^ (4 * j))
    (hS : ∀ g ∈ S, Y ≤ (g : ℝ) ∧ (g : ℝ) ≤ 2 * Y ∧ l ^ j ∣ g ^ d - 1) :
    (S.card : ℝ) ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
  classical
  set M := l ^ j with hMdef
  have hM : 0 < M := pow_pos hl.pos j
  have hM' : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  set R := (Finset.range M).filter (fun x => x ^ d ≡ 1 [MOD M]) with hR
  have hRcard : R.card ≤ 2 * d := Formalism.GaloisIrreducibility.residuesLe l j d hl hd
  have hmaps : ∀ g ∈ S, g % M ∈ R := by
    intro g hg
    obtain ⟨h1, _, h3⟩ := hS g hg
    have hg1 : 1 ≤ g := by
      have : (1 : ℝ) ≤ (g : ℝ) := hY.trans h1
      exact_mod_cast this
    have hgd : 1 ≤ g ^ d := Nat.one_le_pow _ _ hg1
    have hmod : 1 ≡ g ^ d [MOD M] := (Nat.modEq_iff_dvd' hgd).mpr h3
    rw [hR, Finset.mem_filter, Finset.mem_range]
    refine ⟨Nat.mod_lt _ hM, ?_⟩
    exact ((Nat.mod_modEq g M).pow d).trans hmod.symm
  have hcard : S.card = ∑ r ∈ R, (S.filter (fun g => g % M = r)).card :=
    Finset.card_eq_sum_card_fiberwise hmaps
  have hfib : ∀ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    intro r _
    have h1 := card_class_le (S.filter (fun g => g % M = r)) Y M r hM (by linarith) (by
      intro g hg
      obtain ⟨hgS, hgr⟩ := Finset.mem_filter.mp hg
      exact ⟨(hS g hgS).1, (hS g hgS).2.1, hgr⟩)
    have h2 : Y / (M : ℝ) ≤ Y ^ ((3 : ℝ) / 4) := by
      apply div_le_rpow Y M hY hM'
      have : ((M : ℝ)) ^ 4 = (l : ℝ) ^ (4 * j) := by
        rw [hMdef]; push_cast; rw [← pow_mul, mul_comm]
      rw [this]; exact hj
    linarith
  have hc0 : (0 : ℝ) ≤ Y ^ ((3 : ℝ) / 4) + 1 := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  calc (S.card : ℝ) = ∑ r ∈ R, ((S.filter (fun g => g % M = r)).card : ℝ) := by
        rw [hcard]; push_cast; rfl
    _ ≤ ∑ _r ∈ R, (Y ^ ((3 : ℝ) / 4) + 1) := Finset.sum_le_sum hfib
    _ = (R.card : ℝ) * (Y ^ ((3 : ℝ) / 4) + 1) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 2 * d * (Y ^ ((3 : ℝ) / 4) + 1) := by
        apply mul_le_mul_of_nonneg_right _ hc0
        exact_mod_cast hRcard

theorem excluded_count_bound : ExcludedCount := by
  classical
  intro N g₁ Y S hN hY hg₁ hS
  set c : ℝ := Y ^ ((3 : ℝ) / 4) + 1 with hc
  have hc0 : (0 : ℝ) ≤ c := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    linarith
  have hcover : S ⊆ (BB g₁ N).biUnion (fun l => S.filter (fun g => l ∈ BB g N)) := by
    intro g hg
    obtain ⟨_, _, _, hnd⟩ := hS g hg
    rw [Finset.not_disjoint_iff] at hnd
    obtain ⟨l, h1, h2⟩ := hnd
    exact Finset.mem_biUnion.mpr ⟨l, h1, Finset.mem_filter.mpr ⟨hg, h2⟩⟩
  have hper : ∀ l ∈ BB g₁ N,
      ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by
    intro l hlB
    have hl : l.Prime := by
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlB
      rcases hlB with rfl | ⟨_, h2, _⟩
      · exact hg₁
      · exact h2
    have hex : ∃ j : ℕ, Y < (l : ℝ) ^ (4 * j) := by
      have h1 : (1 : ℝ) < (l : ℝ) ^ 4 := by
        have : (1 : ℝ) < (l : ℝ) := by exact_mod_cast hl.one_lt
        exact one_lt_pow₀ this (by norm_num)
      obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt Y h1
      exact ⟨n, by rw [pow_mul]; exact hn⟩
    set j := Nat.find hex with hjdef
    have hj : Y < (l : ℝ) ^ (4 * j) := Nat.find_spec hex
    have hmin : ∀ i < j, (l : ℝ) ^ (4 * i) ≤ Y := fun i hi => not_lt.mp (Nat.find_min hex hi)
    set F : ℕ → Finset ℕ := fun d => S.filter (fun g => l ^ j ∣ g ^ d - 1) with hF
    have hsub : S.filter (fun g => l ∈ BB g N) ⊆ insert l ((Finset.Icc 1 N).biUnion F) := by
      intro g hg
      obtain ⟨hgS, hlg⟩ := Finset.mem_filter.mp hg
      obtain ⟨hgp, hYg, _, _⟩ := hS g hgS
      simp only [BB, Finset.mem_insert, Finset.mem_filter] at hlg
      rcases hlg with rfl | ⟨_, _, d, hd, h3⟩
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨d, hd, ?_⟩)
        rw [hF]
        refine Finset.mem_filter.mpr ⟨hgS, ?_⟩
        exact bad_primes_divides l g d j Y hl (Finset.mem_Icc.mp hd).1 hgp.two_le hYg h3 hj hmin
    have hFd : ∀ d ∈ Finset.Icc 1 N, ((F d).card : ℝ) ≤ 2 * N * c := by
      intro d hd
      obtain ⟨hd1, hdN⟩ := Finset.mem_Icc.mp hd
      have h1 := card_pow_class_le (F d) Y l j d hl hd1 hY hj (by
        intro g hg
        obtain ⟨hgS, hdv⟩ := Finset.mem_filter.mp hg
        exact ⟨(hS g hgS).2.1, (hS g hgS).2.2.1, hdv⟩)
      have hdN' : (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast hdN
      calc ((F d).card : ℝ) ≤ 2 * d * c := h1
        _ ≤ 2 * N * c := by
            apply mul_le_mul_of_nonneg_right _ hc0
            linarith
    have h1 : (S.filter (fun g => l ∈ BB g N)).card ≤
        (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
      calc (S.filter (fun g => l ∈ BB g N)).card
          ≤ (insert l ((Finset.Icc 1 N).biUnion F)).card := Finset.card_le_card hsub
        _ ≤ ((Finset.Icc 1 N).biUnion F).card + 1 := Finset.card_insert_le _ _
        _ ≤ (∑ d ∈ Finset.Icc 1 N, (F d).card) + 1 :=
            Nat.add_le_add_right Finset.card_biUnion_le 1
    have h2 : ((S.filter (fun g => l ∈ BB g N)).card : ℝ) ≤
        (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) + 1 := by exact_mod_cast h1
    have h3 : (∑ d ∈ Finset.Icc 1 N, ((F d).card : ℝ)) ≤ ∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c :=
      Finset.sum_le_sum hFd
    have h4 : (∑ _d ∈ Finset.Icc 1 N, 2 * (N : ℝ) * c) = 2 * (N : ℝ) ^ 2 * c := by
      rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      simp only [Nat.add_sub_cancel]
      ring
    linarith
  have hB0 : (0 : ℝ) ≤ 1 + 2 * (N : ℝ) ^ 2 * c := by positivity
  have hBB : ((BB g₁ N).card : ℝ) ≤ 3 * N + 1 := by
    exact_mod_cast bad_primes_cardinality g₁ N hg₁.two_le
  have h1 : S.card ≤ ∑ l ∈ BB g₁ N, (S.filter (fun g => l ∈ BB g N)).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := by
    exact_mod_cast h1
  calc (S.card : ℝ) ≤ ∑ l ∈ BB g₁ N, ((S.filter (fun g => l ∈ BB g N)).card : ℝ) := h2
    _ ≤ ∑ _l ∈ BB g₁ N, (1 + 2 * (N : ℝ) ^ 2 * c) := Finset.sum_le_sum hper
    _ = ((BB g₁ N).card : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * c) := mul_le_mul_of_nonneg_right hBB hB0

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end

section
namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

theorem proposition_one_central_count : Prop1Core := by
  classical
  intro N Y P hN hY hP hcard
  have hb0 : (0 : ℝ) ≤ (3 * N + 1 : ℝ) * (1 + 2 * (N : ℝ) ^ 2 * (Y ^ ((3 : ℝ) / 4) + 1)) := by
    have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ Y) ((3 : ℝ) / 4)
    positivity
  have hne : P.Nonempty := by
    rw [← Finset.card_pos]
    have : (0 : ℝ) < P.card := lt_of_le_of_lt hb0 hcard
    exact_mod_cast this
  obtain ⟨g₁, hg₁⟩ := hne
  set S := P.filter (fun g => ¬ Disjoint (BB g₁ N) (BB g N)) with hSdef
  have hS := excluded_count_bound N g₁ Y S hN hY (hP g₁ hg₁).1 (by
    intro g hg
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hg
    exact ⟨(hP g h1).1, (hP g h1).2.1, (hP g h1).2.2, h2⟩)
  have hlt : S.card < P.card := by exact_mod_cast lt_of_le_of_lt hS hcard
  obtain ⟨g₂, hg₂, hn⟩ : ∃ g₂ ∈ P, g₂ ∉ S := by
    by_contra hcon
    push Not at hcon
    exact absurd (Finset.card_le_card (fun g hg => hcon g hg)) (not_le.mpr hlt)
  have hd : Disjoint (BB g₁ N) (BB g₂ N) := by
    by_contra h
    exact hn (Finset.mem_filter.mpr ⟨hg₂, h⟩)
  refine ⟨g₁, hg₁, g₂, hg₂, ?_, hd⟩
  rintro rfl
  have hmem : g₁ ∈ BB g₁ N := by simp [BB]
  exact Finset.disjoint_left.mp hd hmem hmem

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
end
