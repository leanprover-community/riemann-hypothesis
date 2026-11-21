import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLifted
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeltaCupProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTotalCochainOfDegreeSuccOfDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductVanishAboveDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierPropertyAtSignMulFactorialScaling
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExteriorAlgebraExtensionOfFrobeniusSemilin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAntisymmetrizedCupProductLeadingTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingProductIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtDAlgebraMapPowCharMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsGamma
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusDerivationFactorsThroughKaehler
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHOfIsFrob
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedFrobLogForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanFormsEqBotOfLtCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExteriorDerivativeIsDifferential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsGeneratedDlog
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularFunctionsPthPowerTwist

section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem Dtot_cup : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 →
    (∀ s, Dtot d (Φ (c s)) = 0) → Dtot d (cup Φ c) = cup Φ (delta c) := by
  intro ι _ E _ d Φ c hΦ hc hD
  funext u
  have key := delta_cup_eq Φ c hΦ hc u
  suffices hS : (∑ j ∈ u, ((-1 : ℤ) ^ ({x ∈ u | x < j}).card) • delta (Φ (c ({x ∈ u | x ≤ j}))) ({x ∈ u | j ≤ x}))
      + ((-1 : ℤ) ^ u.card) • d (cup Φ c u) = 0 by
    simp only [Dtot]
    rw [key, add_assoc, hS, add_zero]
  simp only [cup, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have h := congrFun (hD ({x ∈ u | x ≤ j})) ({x ∈ u | j ≤ x})
  simp only [Dtot, Pi.zero_apply] at h
  rw [eq_neg_of_add_eq_zero_left h]
  have hcard : ({x ∈ u | x < j}).card + ({x ∈ u | j ≤ x}).card = u.card := by
    have := Finset.card_filter_add_card_filter_not (s := u) (fun x => x < j)
    simpa only [not_lt] using this
  rw [smul_neg, smul_smul, ← pow_add, hcard, neg_add_cancel]

end GlobalTheory.DI
end

section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.FiltVanish

variable {ι : Type} {E : Type} [AddCommGroup E]

theorem inTot_zero (T : ℕ → Finset ι → AddSubgroup E) (m : ℕ) : InTot T m (0 : Finset ι → E) :=
  ⟨rfl, fun q s _ => (T q s).zero_mem, fun _ _ => rfl⟩

theorem inTot_add {T : ℕ → Finset ι → AddSubgroup E} {m : ℕ} {c c' : Finset ι → E}
    (h1 : InTot T m c) (h2 : InTot T m c') : InTot T m (c + c') := by
  refine ⟨?_, ?_, ?_⟩
  · simp [h1.1, h2.1]
  · intro q s hq; exact (T q s).add_mem (h1.2.1 q s hq) (h2.2.1 q s hq)
  · intro s hs; simp [h1.2.2 s hs, h2.2.2 s hs]

theorem inTot_sub {T : ℕ → Finset ι → AddSubgroup E} {m : ℕ} {c c' : Finset ι → E}
    (h1 : InTot T m c) (h2 : InTot T m c') : InTot T m (c - c') := by
  refine ⟨?_, ?_, ?_⟩
  · simp [h1.1, h2.1]
  · intro q s hq; exact (T q s).sub_mem (h1.2.1 q s hq) (h2.2.1 q s hq)
  · intro s hs; simp [h1.2.2 s hs, h2.2.2 s hs]

end GlobalTheory.DI.FiltVanish

private theorem delta_eq_zero_of_card_le_of_vanish_below {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (c : Finset ι → E) (p : ℕ) (hc : ∀ s : Finset ι, s.card < p → c s = 0)
    (t : Finset ι) (ht : t.card ≤ p) : delta c t = 0 := by
  unfold delta
  refine Finset.sum_eq_zero fun i hi => ?_
  have h1 : (t.erase i).card < p := by
    rw [Finset.card_erase_of_mem hi]
    have := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  rw [hc _ h1, smul_zero]

private theorem inTot_succ_delta_of_inTot {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (N : ℕ → Finset ι → AddSubgroup E) (hN : ∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t)
    (m : ℕ) (c : Finset ι → E) (hc : InTot N m c) : InTot N (m + 1) (delta c) := by
  obtain ⟨h0, hmem, hbig⟩ := hc
  refine ⟨?_, fun q s hq => ?_, fun s hs => ?_⟩
  · simp [delta]
  · unfold delta
    refine sum_mem fun i hi => ?_
    refine zsmul_mem ?_ _
    have hcard : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    by_cases he : (s.erase i).Nonempty
    · exact hN q _ _ he (Finset.erase_subset i s) (hmem q _ (by omega))
    · rw [Finset.not_nonempty_iff_eq_empty] at he
      rw [he, h0]
      exact zero_mem _
  · unfold delta
    refine Finset.sum_eq_zero fun i hi => ?_
    have hcard : (s.erase i).card + 1 = s.card := Finset.card_erase_add_one hi
    rw [hbig _ (by omega), smul_zero]

private theorem inTot_succ_Dtot_of_inTot {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E]
    (d : E →+ E) (T : ℕ → Finset ι → AddSubgroup E) (hT : ∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t)
    (hd : ∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s)
    (m : ℕ) (c : Finset ι → E) (hc : InTot T m c) : InTot T (m + 1) (Dtot d c) := by
  have hδ := inTot_succ_delta_of_inTot T hT m c hc
  obtain ⟨h0, hmem, hbig⟩ := hc
  refine ⟨?_, fun q s hq => ?_, fun s hs => ?_⟩
  · simp [Dtot, hδ.1, h0]
  · simp only [Dtot]
    refine add_mem (hδ.2.1 q s hq) (zsmul_mem ?_ _)
    rcases q with _ | q
    · rw [hbig s (by omega), map_zero]
      exact zero_mem _
    · exact hd q s _ (hmem q s (by omega))
  · simp only [Dtot]
    rw [hδ.2.2 s hs, hbig s (by omega), map_zero, smul_zero, add_zero]

open GlobalTheory.DI.FiltVanish in

theorem GlobalTheory.DI.cechZero_of_hypZero_filtered : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Ψ : (Finset ι → E) →+ (Finset ι → E)) (γ : Finset ι → E → E), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ m c, InTot N m c → Dtot d (Ψ c) = Ψ (delta c)) → (∀ m c, InTot N m c → InTot T m (Ψ c)) → (∀ s, s.Nonempty → CartierAt d (γ s) (fun a => N a s) (fun a => T a s)) → (∀ m c u, InTot N m c → u.Nonempty → (∀ s, s.card < u.card → c s = 0) → Ψ c u = γ u (c u)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro ι _ E _ d N T Ψ γ hdd hN hT hd hΨd hΨT hγ hlead a b hH
  have hγ0 : ∀ u : Finset ι, u.Nonempty → γ u 0 = 0 := by
    intro u hu
    have h := hlead 0 0 u (GlobalTheory.DI.FiltVanish.inTot_zero N 0) hu (fun _ _ => rfl)
    rw [map_zero] at h
    simpa using h.symm
  have key : ∀ (n k p : ℕ) (c y : Finset ι → E), p + k = n + 2 → InTot N (n + 1) c → delta c = 0 →
      (∀ s : Finset ι, s.card < p → c s = 0) → InTot T n y → (∀ s : Finset ι, s.card < p → y s = 0) →
      Dtot d y = Ψ c → ∃ y', InTot N n y' ∧ delta y' = c := by
    intro n k
    induction k with
    | zero =>
      intro p c y hpk hc hδc hclow hy hylow hDy
      refine ⟨0, GlobalTheory.DI.FiltVanish.inTot_zero N n, ?_⟩
      funext s
      have h0 : c s = 0 := by
        by_cases hs : s.card < p
        · exact hclow s hs
        · exact hc.2.2 s (by omega)
      rw [h0]
      simp [delta]
    | succ k ih =>
      intro p c y hpk hc hδc hclow hy hylow hDy
      rcases Nat.eq_zero_or_pos p with hp0 | hp0
      · subst hp0
        refine ih 1 c y (by omega) hc hδc ?_ hy ?_ hDy
        · intro s hs
          have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [he]
          exact hc.1
        · intro s hs
          have he : s = ∅ := Finset.card_eq_zero.mp (by omega)
          rw [he]
          exact hy.1
      have hA : ∀ t : Finset ι, t.card = p → c t = 0 ∧ d (y t) = 0 := by
        intro t ht
        have hne : t.Nonempty := Finset.card_pos.mp (by omega)
        have hlt : ∀ s : Finset ι, s.card < t.card → c s = 0 := fun s hs => hclow s (by omega)
        have hl := hlead (n + 1) c t hc hne hlt
        rw [← hDy] at hl
        simp only [Dtot] at hl
        rw [delta_eq_zero_of_card_le_of_vanish_below y p hylow t (le_of_eq ht), zero_add, ht] at hl
        have hc0 : c t = 0 := by
          by_cases hpn : p = n + 1
          · have hyt : y t = 0 := hy.2.2 t (by omega)
            rw [hyt, map_zero, smul_zero] at hl
            have hmem : c t ∈ N 0 t := hc.2.1 0 t (by omega)
            exact (hγ t hne).inj_zero (c t) hmem hl.symm
          · have hmem : c t ∈ N (n - p + 1) t := hc.2.1 _ t (by omega)
            have hymem : y t ∈ T (n - p) t := hy.2.1 _ t (by omega)
            refine (hγ t hne).inj_succ (n - p) (c t) hmem (((-1 : ℤ) ^ p) • y t) (zsmul_mem hymem _) ?_
            rw [map_zsmul]
            exact hl.symm
        refine ⟨hc0, ?_⟩
        rw [hc0, hγ0 t hne] at hl
        rcases neg_one_pow_eq_or ℤ p with h | h
        · rw [h, one_smul] at hl
          exact hl
        · rw [h, neg_one_smul, neg_eq_zero] at hl
          exact hl
      by_cases hpn1 : p = n + 1
      · refine ⟨0, GlobalTheory.DI.FiltVanish.inTot_zero N n, ?_⟩
        funext s
        have h0 : c s = 0 := by
          rcases lt_trichotomy s.card p with h | h | h
          · exact hclow s h
          · exact (hA s h).1
          · exact hc.2.2 s (by omega)
        rw [h0]
        simp [delta]
      have hpn : p ≤ n := by omega
      have hB : ∀ t : Finset ι, ∃ xz : E × E, t.card = p → (xz.1 ∈ N (n - p) t ∧ xz.2 ∈ T (n - p - 1) t ∧ (n ≤ p → xz.2 = 0) ∧ y t = γ t xz.1 + d xz.2) := by
        intro t
        by_cases ht : t.card = p
        · have hne : t.Nonempty := Finset.card_pos.mp (by omega)
          have hymem : y t ∈ T (n - p) t := hy.2.1 _ t (by omega)
          have hdy := (hA t ht).2
          by_cases h0 : n - p = 0
          · have hymem' : y t ∈ T 0 t := by rw [← h0]; exact hymem
            obtain ⟨x, hx, hxy⟩ := (hγ t hne).surj_zero (y t) hymem' hdy
            refine ⟨(x, 0), fun _ => ⟨by rw [h0]; exact hx, zero_mem _, fun _ => rfl, ?_⟩⟩
            simp [hxy]
          · obtain ⟨q, hq⟩ : ∃ q, n - p = q + 1 := ⟨n - p - 1, by omega⟩
            have hymem' : y t ∈ T (q + 1) t := by rw [← hq]; exact hymem
            obtain ⟨x, hx, z, hz, hxy⟩ := (hγ t hne).surj_succ q (y t) hymem' hdy
            refine ⟨(x, z), fun _ => ⟨by rw [hq]; exact hx, by rw [show n - p - 1 = q by omega]; exact hz, fun _ => by omega, hxy⟩⟩
        · exact ⟨(0, 0), fun h => absurd h ht⟩
      choose xz hxz using hB
      obtain ⟨X, hXp, hXo⟩ : ∃ X : Finset ι → E, (∀ s : Finset ι, s.card = p → X s = (xz s).1) ∧ (∀ s : Finset ι, s.card ≠ p → X s = 0) :=
        ⟨fun s => if s.card = p then (xz s).1 else 0, fun s hs => if_pos hs, fun s hs => if_neg hs⟩
      obtain ⟨Z, hZp, hZo⟩ : ∃ Z : Finset ι → E, (∀ s : Finset ι, s.card = p → Z s = ((-1 : ℤ) ^ p) • (xz s).2) ∧ (∀ s : Finset ι, s.card ≠ p → Z s = 0) :=
        ⟨fun s => if s.card = p then ((-1 : ℤ) ^ p) • (xz s).2 else 0, fun s hs => if_pos hs, fun s hs => if_neg hs⟩
      have hXN : InTot N n X := by
        refine ⟨hXo ∅ (by rw [Finset.card_empty]; omega), fun q s hq => ?_, fun s hs => hXo s (by omega)⟩
        by_cases hs : s.card = p
        · rw [hXp s hs]
          have hqe : q = n - p := by omega
          subst hqe
          exact (hxz s hs).1
        · rw [hXo s hs]
          exact zero_mem _
      have hZT : InTot T (n - 1) Z := by
        refine ⟨hZo ∅ (by rw [Finset.card_empty]; omega), fun q s hq => ?_, fun s hs => ?_⟩
        · by_cases hs : s.card = p
          · rw [hZp s hs]
            have hqe : q = n - p - 1 := by omega
            subst hqe
            exact zsmul_mem (hxz s hs).2.1 _
          · rw [hZo s hs]
            exact zero_mem _
        · by_cases hs' : s.card = p
          · rw [hZp s hs', (hxz s hs').2.2.1 (by omega), smul_zero]
          · exact hZo s hs'
      have hn1 : n - 1 + 1 = n := by omega
      have hDZ : InTot T n (Dtot d Z) := hn1 ▸ inTot_succ_Dtot_of_inTot d T hT hd (n - 1) Z hZT
      have hΨX : InTot T n (Ψ X) := hΨT n X hXN
      have hδX : InTot N (n + 1) (delta X) := inTot_succ_delta_of_inTot N hN n X hXN
      have hΨXs : ∀ s : Finset ι, s.Nonempty → s.card ≤ p → Ψ X s = γ s (X s) :=
        fun s hs hsp => hlead n X s hXN hs (fun s' hs' => hXo s' (by omega))
      have hDZs : ∀ s : Finset ι, s.card ≤ p → Dtot d Z s = ((-1 : ℤ) ^ s.card) • d (Z s) := by
        intro s hs
        simp only [Dtot]
        rw [delta_eq_zero_of_card_le_of_vanish_below Z p (fun s' hs' => hZo s' (by omega)) s hs, zero_add]
      have hsq : ((-1 : ℤ) ^ p) * (-1 : ℤ) ^ p = 1 := by
        rw [← mul_pow]
        norm_num
      have hδc' : delta (c - delta X) = 0 := by
        rw [delta_sub, hδc, delta_delta, sub_zero]
      have hclow' : ∀ s : Finset ι, s.card < p + 1 → (c - delta X) s = 0 := by
        intro s hs
        rw [Pi.sub_apply, delta_eq_zero_of_card_le_of_vanish_below X p (fun s' hs' => hXo s' (by omega)) s (by omega), sub_zero]
        rcases Nat.lt_or_ge s.card p with h | h
        · exact hclow s h
        · exact (hA s (by omega)).1
      have hylow' : ∀ s : Finset ι, s.card < p + 1 → (y - Ψ X - Dtot d Z) s = 0 := by
        intro s hs
        simp only [Pi.sub_apply]
        rw [hDZs s (by omega)]
        rcases Nat.lt_or_ge s.card p with h | h
        · rw [hylow s h, hZo s (by omega), map_zero, smul_zero, sub_zero, zero_sub, neg_eq_zero]
          by_cases hne : s.Nonempty
          · rw [hΨXs s hne (by omega), hXo s (by omega), hγ0 s hne]
          · rw [Finset.not_nonempty_iff_eq_empty] at hne
            subst hne
            exact hΨX.1
        · have hsp : s.card = p := by omega
          have hne : s.Nonempty := Finset.card_pos.mp (by omega)
          rw [hΨXs s hne (by omega), hXp s hsp, hZp s hsp, hsp, map_zsmul, smul_smul, hsq, one_smul,
            (hxz s hsp).2.2.2]
          abel
      have hDy' : Dtot d (y - Ψ X - Dtot d Z) = Ψ (c - delta X) := by
        rw [Dtot_sub, Dtot_sub, Dtot_Dtot d hdd, hDy, hΨd n X hXN, map_sub, sub_zero]
      obtain ⟨y'', hy''N, hy''δ⟩ := ih (p + 1) (c - delta X) (y - Ψ X - Dtot d Z) (by omega)
        (GlobalTheory.DI.FiltVanish.inTot_sub hc hδX) hδc' hclow'
        (GlobalTheory.DI.FiltVanish.inTot_sub (GlobalTheory.DI.FiltVanish.inTot_sub hy hΨX) hDZ) hylow' hDy'
      exact ⟨y'' + X, GlobalTheory.DI.FiltVanish.inTot_add hy''N hXN, by rw [delta_add, hy''δ, sub_add_cancel]⟩
  intro c hc hδc
  have hcN : InTot N (a + b + 1) c := by
    refine ⟨hc.1, fun q s hq => ?_, fun s hs => hc.2.2 s (by omega)⟩
    by_cases hs : s.card = b + 1
    · have hqa : q = a := by omega
      subst hqa
      exact hc.2.1 s
    · rw [hc.2.2 s hs]
      exact zero_mem _
  have hΨc := hΨT _ c hcN
  have hDΨ : Dtot d (Ψ c) = 0 := by rw [hΨd _ c hcN, hδc, map_zero]
  obtain ⟨y, hy, hDy⟩ := hH (Ψ c) hΨc hDΨ
  obtain ⟨y', hy'N, hy'δ⟩ := key (a + b) (a + b + 2) 0 c y (by omega) hcN hδc
    (fun s hs => absurd hs (Nat.not_lt_zero _)) hy (fun s hs => absurd hs (Nat.not_lt_zero _)) hDy
  refine ⟨fun s => if s.card = b then y' s else 0, ⟨?_, fun s => ?_, fun s hs => if_neg hs⟩, ?_⟩
  · by_cases hb : b = 0
    · simp [hb, hy'N.1]
    · simp [hb, Ne.symm hb]
  · dsimp only
    split_ifs with hs
    · exact hy'N.2.1 a s (by omega)
    · exact zero_mem _
  · funext t
    by_cases ht : t.card = b + 1
    · rw [← hy'δ]
      simp only [delta]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hcard : (t.erase i).card = b := by
        rw [Finset.card_erase_of_mem hi]
        omega
      rw [if_pos hcard]
    · rw [hc.2.2 t ht]
      simp only [delta]
      refine Finset.sum_eq_zero fun i hi => ?_
      have hcard : (t.erase i).card ≠ b := by
        rw [Finset.card_erase_of_mem hi]
        have := Finset.card_pos.mpr ⟨i, hi⟩
        omega
      rw [if_neg hcard, smul_zero]
end

section
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

private theorem card_filter_le_add_card_filter_ge {ι : Type} [LinearOrder ι] (u : Finset ι) (j : ι)
    (hj : j ∈ u) : ({x ∈ u | x ≤ j}).card + ({x ∈ u | j ≤ x}).card = u.card + 1 := by
  have hU : ({x ∈ u | x ≤ j}) ∪ ({x ∈ u | j ≤ x}) = u := by
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    · intro hx
      rcases le_total x j with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  have hI : ({x ∈ u | x ≤ j}) ∩ ({x ∈ u | j ≤ x}) = {j} := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨_, h1⟩, ⟨_, h2⟩⟩
      exact le_antisymm h1 h2
    · rintro rfl
      exact ⟨⟨hj, le_refl _⟩, ⟨hj, le_refl _⟩⟩
  have h := Finset.card_union_add_card_inter ({x ∈ u | x ≤ j}) ({x ∈ u | j ≤ x})
  rw [hU, hI, Finset.card_singleton] at h
  omega

theorem cechZero_of_hypZero_of_closed_map : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro ι _ E _ d N T Φ hdd hN hT hd hΦ0 hΦD hΦT hC a b hH
  let Ψ : (Finset ι → E) →+ (Finset ι → E) := AddMonoidHom.mk' (fun c => cup Φ c) (by
    intro c c'
    funext u
    simp only [cup, Pi.add_apply, map_add, Finset.sum_add_distrib])
  have hΨ : ∀ c, Ψ c = cup Φ c := fun c => rfl
  let γ : Finset ι → E → E := fun s x => if h : s.Nonempty then Φ x {s.max' h} else 0
  refine cechZero_of_hypZero_filtered d N T Ψ γ hdd hN hT hd ?_ ?_ ?_ ?_ a b hH
  · intro m c hc
    rw [hΨ, hΨ]
    exact Dtot_cup d Φ c hΦ0 hc.1 (fun s => hΦD _)
  · intro m c hc
    rw [hΨ]
    refine ⟨?_, fun q u hq => ?_, fun u hu => ?_⟩
    · simp [cup]
    · simp only [cup]
      refine sum_mem fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).1 q (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
        exact zero_mem _
    · simp only [cup]
      refine Finset.sum_eq_zero fun j hj => ?_
      have hsz := card_filter_le_add_card_filter_ge u j hj
      have hLne : ({x ∈ u | x ≤ j}).Nonempty := ⟨j, Finset.mem_filter.mpr ⟨hj, le_refl _⟩⟩
      have hune : u.Nonempty := ⟨j, hj⟩
      by_cases hLm : ({x ∈ u | x ≤ j}).card ≤ m
      · have hx : c ({x ∈ u | x ≤ j}) ∈ N (m - ({x ∈ u | x ≤ j}).card) u :=
          hN _ _ u hLne (Finset.filter_subset _ _) (hc.2.1 _ _ (by omega))
        exact (hΦT _ u _ _ hune (Finset.filter_subset _ _) hx).2 (by omega)
      · rw [hc.2.2 _ (by omega), map_zero, Pi.zero_apply]
  · intro s hs
    have hγs : γ s = fun x => Φ x {s.max' hs} := by
      funext x
      simp only [γ, dif_pos hs]
    rw [hγs]
    exact hC s (s.max' hs) (s.max'_mem hs)
  · intro m c u hc hu hlow
    rw [hΨ]
    simp only [cup]
    rw [Finset.sum_eq_single_of_mem (u.max' hu) (u.max'_mem hu)]
    · have hL : ({x ∈ u | x ≤ u.max' hu}) = u := by
        ext x
        simp only [Finset.mem_filter]
        constructor
        · exact fun h => h.1
        · intro hx
          exact ⟨hx, u.le_max' x hx⟩
      have hR : ({x ∈ u | u.max' hu ≤ x}) = {u.max' hu} := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_singleton]
        constructor
        · rintro ⟨hx, hle⟩
          exact le_antisymm (u.le_max' x hx) hle
        · rintro rfl
          exact ⟨u.max'_mem hu, le_refl _⟩
      rw [hL, hR]
      simp only [γ, dif_pos hu]
    · intro j hj hne
      have hlt : ({x ∈ u | x ≤ j}).card < u.card := by
        apply Finset.card_lt_card
        refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
        have hm := hsub (u.max'_mem hu)
        simp only [Finset.mem_filter] at hm
        exact hne (le_antisymm (u.le_max' j hj) hm.2)
      rw [hlow _ hlt, map_zero, Pi.zero_apply]

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.cechZero_of_hypZero_of_cartier : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E) (N T : ℕ → Finset ι → AddSubgroup E) (Φ : E →+ (Finset ι → E)), (∀ x, d (d x) = 0) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ x, Φ x ∅ = 0) → (∀ x, Dtot d (Φ x) = 0) → (∀ a u t x, u.Nonempty → t ⊆ u → x ∈ N a u → (∀ q, q + t.card = a + 1 → Φ x t ∈ T q u) ∧ (a + 1 < t.card → Φ x t = 0)) → (∀ s, ∀ j ∈ s, CartierAt d (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  atlas_forward_decl _root_.GlobalTheory.DI.cechZero_of_hypZero_of_closed_map
end

section
set_option autoImplicit false

open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.AltClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem dtot_add {E : Type} [AddCommGroup E] (d : E →+ E) (c c' : Finset ι → E) :
    Dtot d (c + c') = Dtot d c + Dtot d c' := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel

def dtotHom {E : Type} [AddCommGroup E] (d : E →+ E) : (Finset ι → E) →+ (Finset ι → E) :=
  AddMonoidHom.mk' (Dtot d) (dtot_add d)

omit [LinearOrder ι] in

theorem oneC_empty : (oneC : Finset ι → ExteriorAlgebra K V) ∅ = 0 := by
  simp [oneC]

theorem d_one (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) : d 1 = 0 := by
  have h1 := hd.mul 1 1
  simp only [mul_one, map_one, one_mul] at h1
  exact add_left_cancel (a := d 1) (by rw [add_zero]; exact h1.symm)

theorem delta_oneC_pair {x y : ι} (h : x < y) :
    delta (oneC : Finset ι → ExteriorAlgebra K V) {x, y} = 0 := by
  have hne : x ≠ y := ne_of_lt h
  simp only [delta]
  rw [Finset.sum_pair hne]
  have e1 : ({x, y} : Finset ι).erase x = {y} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact absurd hz' hz
      · exact hz'
    · rintro rfl
      exact ⟨hne.symm, Or.inr rfl⟩
  have e2 : ({x, y} : Finset ι).erase y = {x} := by
    ext z
    simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz, hz' | hz'⟩
      · exact hz'
      · exact absurd hz' hz
    · rintro rfl
      exact ⟨hne, Or.inl rfl⟩
  have s1 : GlobalTheory.cubeSign ({x, y} : Finset ι) x = 1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < x}) = ∅ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) hz
      · exact lt_irrefl _ hz
      · exact lt_asymm h hz
    rw [this]
    simp
  have s2 : GlobalTheory.cubeSign ({x, y} : Finset ι) y = -1 := by
    unfold GlobalTheory.cubeSign
    have : ({z ∈ ({x, y} : Finset ι) | z < y}) = {x} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (lt_irrefl _)
      · rintro rfl
        exact ⟨Or.inl rfl, h⟩
    rw [this]
    simp
  rw [e1, e2, s1, s2]
  simp [oneC]

theorem delta_oneC (t : Finset ι) : delta (oneC : Finset ι → ExteriorAlgebra K V) t = 0 := by
  by_cases h2 : t.card = 2
  · obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp h2
    rcases lt_or_gt_of_ne hxy with hlt | hlt
    · exact delta_oneC_pair hlt
    · rw [Finset.pair_comm]
      exact delta_oneC_pair hlt
  · simp only [delta]
    apply Finset.sum_eq_zero
    intro i hi
    have hpos := Finset.card_pos.mpr ⟨i, hi⟩
    have hc : ¬ (t.erase i).card = 1 := by
      rw [Finset.card_erase_of_mem hi]
      omega
    simp [oneC, hc]

theorem dtot_oneC (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) :
    Dtot d (oneC : Finset ι → ExteriorAlgebra K V) = 0 := by
  funext t
  simp only [Dtot, delta_oneC, zero_add, Pi.zero_apply]
  unfold oneC
  split_ifs <;> simp [d_one d hd]

private theorem cubeSign_min_eq_one (s : Finset ι) (hs : s.Nonempty) : GlobalTheory.cubeSign s (s.min' hs) = 1 := by
  unfold GlobalTheory.cubeSign
  have e : ({x ∈ s | x < s.min' hs}) = ∅ := by
    apply Finset.filter_false_of_mem
    intro x hx
    exact not_lt.mpr (s.min'_le x hx)
  rw [e]
  simp

private theorem cubeSign_eq_neg_cubeSign_erase_min (s : Finset ι) (hs : s.Nonempty) (i : ι) (hi : i ∈ s.erase (s.min' hs)) :
    GlobalTheory.cubeSign s i = -GlobalTheory.cubeSign (s.erase (s.min' hs)) i := by
  have hne : i ≠ s.min' hs := Finset.ne_of_mem_erase hi
  have his : i ∈ s := Finset.mem_of_mem_erase hi
  have hlt : s.min' hs < i := lt_of_le_of_ne (s.min'_le i his) hne.symm
  unfold GlobalTheory.cubeSign
  have hfil : ({x ∈ s | x < i}) = insert (s.min' hs) ({x ∈ s.erase (s.min' hs) | x < i}) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_erase]
    constructor
    · rintro ⟨hxs, hxi⟩
      by_cases hx : x = s.min' hs
      · exact Or.inl hx
      · exact Or.inr ⟨⟨hx, hxs⟩, hxi⟩
    · rintro (hx | ⟨⟨_, hxs⟩, hxi⟩)
      · rw [hx]
        exact ⟨s.min'_mem hs, hlt⟩
      · exact ⟨hxs, hxi⟩
  rw [hfil, Finset.card_insert_of_notMem (by simp), pow_succ]
  ring

private theorem delta_eq_erase_min_sub_sum_cubeSign {E : Type} [AddCommGroup E] (c : Finset ι → E) (s : Finset ι) (hs : s.Nonempty) :
    delta c s = c (s.erase (s.min' hs)) -
      ∑ i ∈ s.erase (s.min' hs), GlobalTheory.cubeSign (s.erase (s.min' hs)) i • c (s.erase i) := by
  unfold delta
  rw [← Finset.add_sum_erase s _ (s.min'_mem hs), cubeSign_min_eq_one s hs, one_smul, sub_eq_add_neg,
    ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [cubeSign_eq_neg_cubeSign_erase_min s hs i hi, neg_smul]

private theorem Lop_apply_of_min_eq (f : ι → V →+ V) (h : ι → ι → V →+ K) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (t : Finset ι) (m0 : ι) (ht : t.Nonempty) (hm : t.min' ht = m0) :
    Lop f h v y t = (-1 : ℤ) ^ t.card • (ExteriorAlgebra.ι K (f m0 v) * y t) +
      (if h2 : (t.erase m0).Nonempty then h m0 ((t.erase m0).min' h2) v • y (t.erase m0) else 0) := by
  subst hm
  unfold Lop
  rw [dif_pos ht]

private theorem neg_one_pow_card_erase_of_mem (t : Finset ι) (i : ι) (hi : i ∈ t) :
    (-1 : ℤ) ^ (t.erase i).card = -(-1) ^ t.card := by
  rw [Finset.card_erase_of_mem hi]
  obtain ⟨k, hk⟩ : ∃ k, t.card = k + 1 := ⟨t.card - 1, by have := Finset.card_pos.mpr ⟨i, hi⟩; omega⟩
  rw [hk, Nat.add_sub_cancel, pow_succ]
  ring

private theorem Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (v : V)
    (y : Finset ι → ExteriorAlgebra K V) (hy : Dtot d y = 0) (hy0 : y ∅ = 0) :
    Dtot d (Lop f h v y) = 0 := by
  have hys : ∀ s : Finset ι, d (y s) = -((-1 : ℤ) ^ s.card • delta y s) := by
    intro s
    have e0 := congrFun hy s
    simp only [Dtot, Pi.zero_apply] at e0
    have e2 : (-1 : ℤ) ^ s.card • d (y s) = -delta y s := by
      rw [eq_neg_iff_add_eq_zero, add_comm]
      exact e0
    have e1 : ((-1 : ℤ) ^ s.card * (-1) ^ s.card) = 1 := by
      rw [← mul_pow]
      simp
    calc d (y s) = ((-1 : ℤ) ^ s.card * (-1) ^ s.card) • d (y s) := by rw [e1, one_smul]
      _ = (-1 : ℤ) ^ s.card • ((-1 : ℤ) ^ s.card • d (y s)) := mul_smul _ _ _
      _ = -((-1 : ℤ) ^ s.card • delta y s) := by rw [e2, smul_neg]
  have dsm : ∀ (k : K) (x : ExteriorAlgebra K V), d (k • x) = d (algebraMap K _ k) * x + k • d x := by
    intro k x
    rw [Algebra.smul_def, hd.mul, AlgHom.commutes, ← Algebra.smul_def]
  have dω : ∀ (i : ι) (x : ExteriorAlgebra K V),
      d (ExteriorAlgebra.ι K (f i v) * x) = -(ExteriorAlgebra.ι K (f i v) * d x) := by
    intro i x
    rw [hd.mul, hD.closed, zero_mul, zero_add]
    rw [show CliffordAlgebra.involute (ExteriorAlgebra.ι K (f i v)) = -ExteriorAlgebra.ι K (f i v) from
      CliffordAlgebra.involute_ι _, neg_mul]
  have hε : ∀ (n : ℕ) (x : ExteriorAlgebra K V), (-1 : ℤ) ^ n • ((-1 : ℤ) ^ n • x) = x := by
    intro n x
    rw [← mul_smul, ← mul_pow]
    simp
  funext s
  simp only [Dtot, Pi.zero_apply]
  by_cases hs : s.Nonempty
  swap
  · rw [Finset.not_nonempty_iff_eq_empty.mp hs]
    simp [delta, Lop]
  · rw [delta_eq_erase_min_sub_sum_cubeSign _ s hs]
    have hdy := delta_eq_erase_min_sub_sum_cubeSign y s hs
    set m := s.min' hs
    set s' := s.erase m
    have hms : m ∈ s := s.min'_mem hs
    have hLs := Lop_apply_of_min_eq f h v y s m hs rfl
    have hLi : ∀ i ∈ s', Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y (s.erase i))) +
        (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      intro i hi
      have hne : i ≠ m := Finset.ne_of_mem_erase hi
      have his : i ∈ s := Finset.mem_of_mem_erase hi
      have hmi : m ∈ s.erase i := Finset.mem_erase.mpr ⟨hne.symm, hms⟩
      have hmin : (s.erase i).min' ⟨m, hmi⟩ = m :=
        le_antisymm ((s.erase i).min'_le m hmi)
          (Finset.le_min' _ _ _ (fun z hz => s.min'_le z (Finset.mem_of_mem_erase hz)))
      rw [Lop_apply_of_min_eq f h v y (s.erase i) m ⟨m, hmi⟩ hmin, neg_one_pow_card_erase_of_mem s i his, neg_smul,
        Finset.erase_right_comm]
    have hsum : ∑ i ∈ s', GlobalTheory.cubeSign s' i • Lop f h v y (s.erase i) =
        -((-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i))) +
        ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h2 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h2) v • y (s'.erase i) else 0) := by
      rw [Finset.mul_sum, Finset.smul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hLi i hi, smul_add, smul_neg, mul_smul_comm, smul_comm (GlobalTheory.cubeSign s' i)]
    have hX : ∑ i ∈ s', GlobalTheory.cubeSign s' i • y (s.erase i) = y s' - delta y s := by
      rw [hdy]
      abel
    have hLs2 : Lop f h v y s = (-1 : ℤ) ^ s.card • (ExteriorAlgebra.ι K (f m v) * y s) +
        (if h2 : s'.Nonempty then h m (s'.min' h2) v • y s' else 0) := hLs
    rw [hsum, hLs2, hX, map_add, map_zsmul, dω, hys s]
    by_cases h2 : s'.Nonempty
    · set n := s'.min' h2 with hn_eq
      have hns : n ∈ s' := s'.min'_mem h2
      have hLs' : Lop f h v y s' = (-1 : ℤ) ^ s'.card • (ExteriorAlgebra.ι K (f n v) * y s') +
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) :=
        Lop_apply_of_min_eq f h v y s' n h2 rfl
      have hc : (-1 : ℤ) ^ s'.card = -(-1) ^ s.card := neg_one_pow_card_erase_of_mem s m hms
      have hSh : ∑ i ∈ s', GlobalTheory.cubeSign s' i •
          (if h3 : (s'.erase i).Nonempty then h m ((s'.erase i).min' h3) v • y (s'.erase i) else 0) =
          (if h3 : (s'.erase n).Nonempty then h n ((s'.erase n).min' h3) v • y (s'.erase n) else 0) +
            h m n v • delta y s' := by
        rw [← sub_eq_iff_eq_add]
        unfold delta
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib, Finset.sum_eq_single n]
        · rw [show GlobalTheory.cubeSign s' n = 1 from cubeSign_min_eq_one s' h2]
          simp only [one_smul]
          by_cases h3 : (s'.erase n).Nonempty
          · rw [dif_pos h3, dif_pos h3, ← sub_smul]
            congr 1
            rw [← hD.cocycle m n ((s'.erase n).min' h3) v]
            ring
          · rw [dif_neg h3, dif_neg h3, Finset.not_nonempty_iff_eq_empty.mp h3, hy0]
            simp
        · intro b hb hbn
          have hnb : n ∈ s'.erase b := Finset.mem_erase.mpr ⟨fun e => hbn e.symm, hns⟩
          have hmin : (s'.erase b).min' ⟨n, hnb⟩ = n :=
            le_antisymm ((s'.erase b).min'_le n hnb)
              (Finset.le_min' _ _ _ (fun z hz => s'.min'_le z (Finset.mem_of_mem_erase hz)))
          rw [dif_pos ⟨n, hnb⟩, hmin, smul_comm (h m n v) (GlobalTheory.cubeSign s' b), sub_self]
        · intro hn
          exact absurd hns hn
      have hcomm : ∀ x : ExteriorAlgebra K V,
          h m n v • ((-1 : ℤ) ^ s.card • x) = (-1 : ℤ) ^ s.card • (h m n v • x) :=
        fun x => smul_comm _ _ _
      rw [dif_pos h2, ← hn_eq, hSh, hLs', dsm, hD.dh, hys s', hc]
      simp only [neg_smul, smul_neg, neg_neg, mul_neg, mul_sub, sub_mul, smul_add, smul_sub,
        mul_smul_comm, hε, hcomm]
      abel
    · have hs'e : s' = ∅ := Finset.not_nonempty_iff_eq_empty.mp h2
      have hdy0 : delta y s = 0 := by
        rw [hdy, hs'e]
        simp [hy0]
      rw [dif_neg h2, hdy0, hs'e]
      simp [Lop, hy0]

theorem prodL_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (vs : List V) :
    Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0 := by
  induction vs with
  | nil => exact ⟨dtot_oneC d hd, oneC_empty (ι := ι)⟩
  | cons v vs ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨?_, ?_⟩
    · exact Dtot_Lop_eq_zero_of_Dtot_eq_zero_of_empty_eq_zero p d f h hd hD v _ h1 h2
    · simp [prodL, Lop]

theorem alt_closed (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V)
    (h : ι → ι → V →+ K) (hd : IsOddDer d) (hD : IsDatum p d f h) (a : ℕ) (v : Fin a → V) :
    Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  have hp := fun vs => prodL_closed p d f h hd hD vs
  constructor
  · change dtotHom d (alt f h a v) = 0
    unfold alt
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro σ _
    rw [map_zsmul]
    change _ • Dtot d _ = 0
    rw [(hp _).1, smul_zero]
  · simp only [alt, Finset.sum_apply, Pi.smul_apply, (hp _).2, smul_zero, Finset.sum_const_zero]

end GlobalTheory.DI.AltClosed

theorem GlobalTheory.DI.prodL_alt_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsOddDer d → IsDatum p d f h → (∀ vs : List V, Dtot d (prodL f h vs) = 0 ∧ prodL f h vs ∅ = 0) ∧ ∀ (a : ℕ) (v : Fin a → V), Dtot d (alt f h a v) = 0 ∧ alt f h a v ∅ = 0 := by
  intro K _ V _ _ ι _ p d f h hd hD
  exact ⟨fun vs => AltClosed.prodL_closed p d f h hd hD vs,
    fun a v => AltClosed.alt_closed p d f h hd hD a v⟩
end

section
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI.PhiClosed

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι]

theorem d_alg_pow (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (hd : IsOddDer d) (c : K) (n : ℕ) :
    d (algebraMap K (ExteriorAlgebra K V) c ^ (n + 1)) =
      (n + 1) • (algebraMap K (ExteriorAlgebra K V) c ^ n * d (algebraMap K (ExteriorAlgebra K V) c)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ' _ (n + 1), hd.mul, ih, AlgHom.commutes]
    have hc : d (algebraMap K (ExteriorAlgebra K V) c) * algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) =
        algebraMap K (ExteriorAlgebra K V) c ^ (n + 1) * d (algebraMap K (ExteriorAlgebra K V) c) := by
      rw [← map_pow]
      exact (Algebra.commutes _ _).symm
    rw [hc, mul_smul_comm, ← mul_assoc, ← pow_succ', succ_nsmul' _ (n + 1)]

theorem d_alg_pow_char (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) : d (algebraMap K (ExteriorAlgebra K V) (c ^ p)) = 0 := by
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := (Fact.out : p.Prime).one_lt; omega⟩
  rw [map_pow, hk, d_alg_pow d hd c k, ← hk, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

theorem d_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (y : ExteriorAlgebra K V) : d (c ^ p • y) = c ^ p • d y := by
  rw [Algebra.smul_def, hd.mul, AlgHom.commutes, d_alg_pow_char p d hd c, zero_mul, zero_add,
    ← Algebra.smul_def]

theorem Dtot_add (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (a b : Finset ι → ExteriorAlgebra K V) :
    Dtot d (a + b) = Dtot d a + Dtot d b := by
  funext t
  simp only [Dtot, delta, Pi.add_apply, smul_add, Finset.sum_add_distrib, map_add]
  abel

theorem Dtot_smul_pow (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V)
    (hd : IsOddDer d) (c : K) (a : Finset ι → ExteriorAlgebra K V) :
    Dtot d (c ^ p • a) = c ^ p • Dtot d a := by
  funext t
  simp only [Dtot, delta, Pi.smul_apply, d_smul_pow p d hd, Finset.smul_sum, smul_add]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _
  · exact smul_comm _ _ _

end GlobalTheory.DI.PhiClosed

open GlobalTheory.DI.PhiClosed in
theorem GlobalTheory.DI.phi_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  intro K _ V _ _ ι _ p _ _ d f h Φ hd hD hΦ
  have hA := (prodL_alt_closed p d f h hd hD).2
  have hz0 : Dtot d (0 : Finset ι → ExteriorAlgebra K V) = 0 := by
    funext t
    simp [Dtot, delta]
  have key : ∀ x : ExteriorAlgebra K V, ∀ c : K, Φ (c • x) ∅ = 0 ∧ Dtot d (Φ (c • x)) = 0 := by
    intro x
    have hx : x ∈ Submodule.span K
        (Set.range fun x : (n : ℕ) × (Fin n → V) => ExteriorAlgebra.ιMulti K x.1 x.2) := by
      rw [ExteriorAlgebra.ιMulti_span]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨a, v⟩, rfl⟩ := hy
      intro c
      rw [hΦ c a v]
      exact ⟨by rw [Pi.smul_apply, (hA a v).2, smul_zero],
        by rw [PhiClosed.Dtot_smul_pow p d hd, (hA a v).1, smul_zero]⟩
    | zero =>
      intro c
      simp [hz0]
    | add y z _ _ hy hz =>
      intro c
      rw [smul_add, map_add]
      exact ⟨by rw [Pi.add_apply, (hy c).1, (hz c).1, add_zero],
        by rw [PhiClosed.Dtot_add, (hy c).2, (hz c).2, add_zero]⟩
    | smul a y _ hy =>
      intro c
      rw [smul_smul]
      exact hy (c * a)
  exact ⟨fun x => by simpa using (key x 1).1, fun x => by simpa using (key x 1).2⟩
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.frobenius_splitting_closed : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → IsPhi p f h Φ → (∀ x, Φ x ∅ = 0) ∧ ∀ x, Dtot d (Φ x) = 0 := by
  atlas_forward_decl _root_.GlobalTheory.DI.phi_closed
end

section
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem exists_isPhi : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  intro K _ V _ _ ι _ p _ _ d f h hD
  have lopAddV : ∀ (x x' : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (x + x') y = Lop f h x y + Lop f h x' y := by
    intro x x' y
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [map_add, add_mul, smul_add, add_smul, add_zero] <;> abel
  have lopAddY : ∀ (x : V) (y y' : Finset ι → ExteriorAlgebra K V),
      Lop f h x (y + y') = Lop f h x y + Lop f h x y' := by
    intro x y y'
    funext t
    simp only [Lop, Pi.add_apply]
    split_ifs <;> simp only [mul_add, smul_add, add_zero] <;> abel
  have lopSmulV : ∀ (c : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h (c • x) y = c ^ p • Lop f h x y := by
    intro c x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [hD.f_smul, hD.h_smul, map_smul, smul_mul_assoc, mul_smul, smul_add, smul_zero,
        smul_comm ((-1 : ℤ) ^ t.card) (c ^ p)]
  have lopSmulY : ∀ (k : K) (x : V) (y : Finset ι → ExteriorAlgebra K V),
      Lop f h x (k • y) = k • Lop f h x y := by
    intro k x y
    funext t
    simp only [Lop, Pi.smul_apply]
    split_ifs <;>
      simp only [mul_smul_comm, smul_add, smul_zero, smul_comm ((-1 : ℤ) ^ t.card) k, smul_comm _ k]
  have hcons : ∀ (x : V) (l : List V), prodL f h (x :: l) = Lop f h x (prodL f h l) := fun _ _ => rfl
  have hupd0 : ∀ {a : ℕ} (v : Fin (a + 1) → V) (z : V),
      (fun k : Fin a => Function.update v 0 z k.succ) = fun k => v k.succ := by
    intro a v z
    funext k
    exact Function.update_of_ne (Fin.succ_ne_zero k) _ _
  have hupds : ∀ {a : ℕ} (v : Fin (a + 1) → V) (j : Fin a) (z : V),
      (fun k : Fin a => Function.update v j.succ z k.succ) = Function.update (fun k => v k.succ) j z := by
    intro a v j z
    funext k
    by_cases hk : k = j
    · subst hk
      simp
    · rw [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]
  have hPadd : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (x x' : V),
      prodL f h (List.ofFn (Function.update v i (x + x'))) =
        prodL f h (List.ofFn (Function.update v i x)) + prodL f h (List.ofFn (Function.update v i x')) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i x x'
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopAddV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopAddY]
  have hPsmul : ∀ (a : ℕ) (v : Fin a → V) (i : Fin a) (c : K) (x : V),
      prodL f h (List.ofFn (Function.update v i (c • x))) =
        c ^ p • prodL f h (List.ofFn (Function.update v i x)) := by
    intro a
    induction a with
    | zero => intro v i; exact i.elim0
    | succ a ih =>
      intro v i c x
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
      · simp only [List.ofFn_succ, hcons, Function.update_self, hupd0]
        exact lopSmulV _ _ _
      · simp only [List.ofFn_succ, hcons, hupds,
          Function.update_of_ne (Fin.succ_ne_zero j).symm]
        rw [ih, lopSmulY]
  have key : ∃ Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V),
      (∀ (c : K) (x : ExteriorAlgebra K V), Φ (c • x) = c ^ p • Φ x) ∧
        ∀ (a : ℕ) (v : Fin a → V), Φ (ExteriorAlgebra.ιMulti K a v) = alt f h a v := by
    letI tw : Module K (Finset ι → ExteriorAlgebra K V) := Module.compHom _ (frobenius K p)
    let P : ∀ a : ℕ, MultilinearMap K (fun _ : Fin a => V) (Finset ι → ExteriorAlgebra K V) := fun a =>
      { toFun := fun v => prodL f h (List.ofFn v)
        map_update_add' := fun v i x x' => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPadd a v i x x'
        map_update_smul' := fun v i c x => by
          obtain rfl : ‹DecidableEq (Fin a)› = instDecidableEqFin a := Subsingleton.elim _ _
          exact hPsmul a v i c x }
    let A : ∀ a : ℕ, V [⋀^Fin a]→ₗ[K] (Finset ι → ExteriorAlgebra K V) := fun a =>
      MultilinearMap.alternatization (P a)
    let Φ0 := ExteriorAlgebra.liftAlternating (R := K) A
    refine ⟨Φ0.toAddMonoidHom, fun c x => ?_, fun a v => ?_⟩
    · exact Φ0.map_smul c x
    · show Φ0 (ExteriorAlgebra.ιMulti K a v) = _
      rw [ExteriorAlgebra.liftAlternating_apply_ιMulti]
      show (MultilinearMap.alternatization (P a)) v = alt f h a v
      rw [MultilinearMap.alternatization_apply]
      unfold alt
      apply Finset.sum_congr rfl
      intro σ _
      rw [Units.smul_def]
      rfl
  obtain ⟨Φ, h1, h2⟩ := key
  exact ⟨Φ, fun c a v => by rw [h1, h2]⟩

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.exists_frobenius_splitting_datum : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K), IsDatum p d f h → ∃ Φ, IsPhi p f h Φ := by
  atlas_forward_decl _root_.GlobalTheory.DI.exists_isPhi
end

section
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem pow_smul_mem_forms_powMul {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) (A B : Set K) (L : Set V) (q : ℕ) (b : K) (hb : b ∈ B) (y : ExteriorAlgebra K V)
    (hy : y ∈ forms A L q) : b ^ p • y ∈ forms {z | ∃ c ∈ B, ∃ a ∈ A, z = c ^ p * a} L q := by
  unfold forms at hy ⊢
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a', ha', v, hv, rfl⟩ := hx
    apply AddSubgroup.subset_closure
    exact ⟨b ^ p * a', ⟨b, hb, a', ha', rfl⟩, v, hv, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem phi_mem_forms : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  intro K _ V _ _ ι _ p f h Φ A B L s hΦ hf hh a q t hts hq x hx
  unfold forms at hx
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, v, hv, rfl⟩ := hx
    rw [show Φ (c • ExteriorAlgebra.ιMulti K a v) = c ^ p • alt f h a v from hΦ c a v, Pi.smul_apply]
    exact pow_smul_mem_forms_powMul p (A : Set K) B L q c hc _
      (GlobalTheory.T.alternating_product_integral f h A L s hf hh a v t hv hts q hq)
  | zero =>
    rw [map_zero, Pi.zero_apply]
    exact zero_mem _
  | add x y _ _ hx hy =>
    rw [map_add, Pi.add_apply]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [map_neg, Pi.neg_apply]
    exact neg_mem hx

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.splitting_integral_forms_bound : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) (f : ι → V →+ V) (h : ι → ι → V →+ K) (Φ : ExteriorAlgebra K V →+ (Finset ι → ExteriorAlgebra K V)) (A : Subring K) (B : Set K) (L : Set V) (s : Finset ι), IsPhi p f h Φ → (∀ i ∈ s, ∀ v ∈ L, ExteriorAlgebra.ι K (f i v) ∈ forms (A : Set K) L 1) → (∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L, h i j v ∈ A) → ∀ (a q : ℕ) (t : Finset ι), t ⊆ s → q + t.card = a + 1 → ∀ x ∈ forms B L a, Φ x t ∈ forms {z | ∃ c ∈ B, ∃ b ∈ A, z = c ^ p * b} L q := by
  atlas_forward_decl _root_.GlobalTheory.DI.phi_mem_forms
end

section
section
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

private theorem forms_mono' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    {B B' : Set K} {L L' : Set V} (hB : B ⊆ B') (hL : L ⊆ L') (q : ℕ) :
    forms B L q ≤ forms B' L' q := by
  unfold forms
  apply AddSubgroup.closure_mono
  rintro x ⟨b, hb, v, hv, rfl⟩
  exact ⟨b, hB hb, v, fun k => hL (hv k), rfl⟩

private theorem iota_mem_forms_one' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (A : Subring K) (w : V) : ExteriorAlgebra.ι K w ∈ forms (A : Set K) (Set.univ : Set V) 1 := by
  unfold forms
  apply AddSubgroup.subset_closure
  refine ⟨1, A.one_mem, fun _ => w, fun _ => trivial, ?_⟩
  rw [one_smul, ExteriorAlgebra.ιMulti_apply]
  simp

private theorem psmul_zero' {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
    (p : ℕ) [CharP K p] (x : ExteriorAlgebra K V) : p • x = 0 := by
  rw [nsmul_eq_mul, ← map_natCast (algebraMap K (ExteriorAlgebra K V)), CharP.cast_eq_zero, map_zero,
    zero_mul]

theorem decomp_pointwise : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  intro K _ V _ _ ι _ p _ _ d f h γ P U A B L N T hd hD hγ hNm hTm hTd hNu hNp hNU hT hfA hhA hC
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.exists_frobenius_splitting_datum p d f h hD
  obtain ⟨h0, hcl⟩ := GlobalTheory.T.frobenius_splitting_closed p d f h Φ hd hD hΦ
  have hvan := (GlobalTheory.T.cechAntisymmetrizedCupProduct_vanish_above_degree p f h).2 Φ hΦ
  apply GlobalTheory.T.cechZero_of_hypZero_of_cartier d N T Φ hd.sq hNm hTm hTd h0 hcl
  · intro a u t x hu htu hx
    have hxu : x ∈ forms (Set.univ : Set K) (Set.univ : Set V) a := hNu a u hu hx
    refine ⟨fun q hq => ?_, fun hlt => hvan a x hxu t hlt⟩
    apply hT q u _ hu
    · have := GlobalTheory.T.splitting_integral_forms_bound p f h Φ (⊤ : Subring K) Set.univ Set.univ t hΦ
        (fun i _ v _ => iota_mem_forms_one' ⊤ (f i v)) (fun _ _ _ _ _ _ => Subring.mem_top _) a q t
        subset_rfl hq x hxu
      exact forms_mono' (Set.subset_univ _) subset_rfl q this
    · intro y hy
      exact GlobalTheory.T.splitting_integral_forms_bound p f h Φ (A y) (B y) (L y) u hΦ (hfA u y hy) (hhA u y hy) a q t htu hq x
        (hNU a u hu y hy hx)
  · intro s j hj
    have hs : s.Nonempty := ⟨j, hj⟩
    exact GlobalTheory.T.cartierPropertyAt_sign_mul_factorial_scaling p d (γ j).toAddMonoidHom (fun x => Φ x {j}) (fun a => N a s) (fun a => T a s)
      (psmul_zero' p) (fun a ha => hNp a s hs ha)
      (fun a x hx => (GlobalTheory.T.cechAntisymmetrizedCupProduct_leading_term p f h).2 Φ j (γ j) hΦ (hγ j) a x (hNu a s hs hx)) (hC s j hj)

end GlobalTheory.DI
end

open GlobalTheory GlobalTheory.DI
theorem _root_.GlobalTheory.T.splitting_local_integrality : ∀ {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {ι : Type} [LinearOrder ι] (p : ℕ) [Fact p.Prime] [CharP K p] (d : ExteriorAlgebra K V →+ ExteriorAlgebra K V) (f : ι → V →+ V) (h : ι → ι → V →+ K) (γ : ι → ExteriorAlgebra K V →+* ExteriorAlgebra K V) {P : Type} (U : Finset ι → Set P) (A : P → Subring K) (B : P → Set K) (L : P → Set V) (N T : ℕ → Finset ι → AddSubgroup (ExteriorAlgebra K V)), IsOddDer d → IsDatum p d f h → (∀ i, IsGamma p (f i) (γ i)) → (∀ q s t, s.Nonempty → s ⊆ t → N q s ≤ N q t) → (∀ q s t, s.Nonempty → s ⊆ t → T q s ≤ T q t) → (∀ q s x, x ∈ T q s → d x ∈ T (q + 1) s) → (∀ a s, s.Nonempty → N a s ≤ forms (Set.univ : Set K) (Set.univ : Set V) a) → (∀ a s, s.Nonempty → p ≤ a → N a s = ⊥) → (∀ a s, s.Nonempty → ∀ y ∈ U s, N a s ≤ forms (B y) (L y) a) → (∀ q s x, s.Nonempty → x ∈ forms (Set.univ : Set K) (Set.univ : Set V) q → (∀ y ∈ U s, x ∈ forms {z | ∃ c ∈ B y, ∃ b ∈ A y, z = c ^ p * b} (L y) q) → x ∈ T q s) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ v ∈ L y, ExteriorAlgebra.ι K (f i v) ∈ forms (A y : Set K) (L y) 1) → (∀ s, ∀ y ∈ U s, ∀ i ∈ s, ∀ j ∈ s, ∀ v ∈ L y, h i j v ∈ A y) → (∀ s, ∀ j ∈ s, CartierAt d (γ j) (fun a => N a s) (fun a => T a s)) → ∀ a b, HypZero d T (a + b) → CechZero (N a) b := by
  atlas_forward_decl _root_.GlobalTheory.DI.decomp_pointwise
end

section
set_option autoImplicit false

noncomputable section

open MvPolynomial

namespace GlobalTheory.DI

section FrobDiff

variable {K : Type} [CommRing K]

theorem kaehlerD_aeval_fin_two (x : Fin 2 → K) (P : MvPolynomial (Fin 2) ℤ) :
    KaehlerDifferential.D ℤ K (aeval x P) =
      ∑ i, aeval x (pderiv i P) • KaehlerDifferential.D ℤ K (x i) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ, add_smul, Finset.sum_add_distrib]
  | mul_X P i hP =>
    simp only [map_mul, aeval_X, Derivation.leibniz, hP, Finset.smul_sum, smul_smul,
      Derivation.leibniz, pderiv_X, Fin.sum_univ_two]
    fin_cases i <;> simp [add_smul, mul_comm, smul_smul, Pi.single_apply] <;> abel

theorem ringHom_aeval_fin_two {Kt : Type} [CommRing Kt] (π : Kt →+* K) (x : Fin 2 → Kt)
    (P : MvPolynomial (Fin 2) ℤ) : π (aeval x P) = aeval (fun i => π (x i)) P := by
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P j hP => simp [hP]

variable {Kt : Type} [CommRing Kt] (p : ℕ) [hp : Fact p.Prime] [CharP K p] (π : Kt →+* K) (F : Kt →+* Kt)

theorem frobLift_exists_w (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    ∃ w, F z = z ^ p + p * w := by
  obtain ⟨w, hw⟩ := (hL.ker (F z - z ^ p)).1 (by rw [map_sub, hF, map_pow, sub_self])
  exact ⟨w, by rw [← hw]; ring⟩

theorem frobLift_w_unique (hL : IsFlatLift p π) {z w w' : Kt} (h : F z = z ^ p + p * w)
    (h' : F z = z ^ p + p * w') : π w = π w' := by
  have e : (p : Kt) * (w - w') = 0 := by
    have := h.symm.trans h'
    rw [mul_sub, sub_eq_zero]
    exact add_left_cancel this
  have e2 := (hL.ann _).mp e
  rwa [map_sub, sub_eq_zero] at e2

theorem kaehlerD_pow_char (x : K) : KaehlerDifferential.D ℤ K (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul K, CharP.cast_eq_zero, zero_smul]

def frobLiftPsi (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) : Ω[K⁄ℤ] :=
  π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
    KaehlerDifferential.D ℤ K (π (frobLift_exists_w p π F hL hF z).choose)

variable {p π F}

theorem frobLiftPsi_spec (hL : IsFlatLift p π) (hF : IsFrob p π F) {z w : Kt}
    (h : F z = z ^ p + p * w) :
    frobLiftPsi p π F hL hF z = π z ^ (p - 1) • KaehlerDifferential.D ℤ K (π z) +
      KaehlerDifferential.D ℤ K (π w) := by
  unfold frobLiftPsi
  rw [frobLift_w_unique p π F hL (frobLift_exists_w p π F hL hF z).choose_spec h]

theorem frobLiftPsi_add (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z + z') = frobLiftPsi p π F hL hF z + frobLiftPsi p π F hL hF z' := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (X 0 : MvPolynomial (Fin 2) ℤ) (X 1)
  have hp0 : (p : MvPolynomial (Fin 2) ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  obtain ⟨C, hC0⟩ : ∃ C : MvPolynomial (Fin 2) ℤ,
      (p : MvPolynomial (Fin 2) ℤ) * C = (X 0 + X 1) ^ p - X 0 ^ p - X 1 ^ p :=
    ⟨X 0 * X 1 * r, by rw [hr]; ring⟩
  have hpd0 : pderiv 0 C = (X 0 + X 1) ^ (p - 1) - X 0 ^ (p - 1) := by
    have := congrArg (pderiv 0) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hpd1 : pderiv 1 C = (X 0 + X 1) ^ (p - 1) - X 1 ^ (p - 1) := by
    have := congrArg (pderiv 1) hC0
    simp [Derivation.leibniz_pow] at this
    exact mul_left_cancel₀ hp0 (by rw [this]; ring)
  have hc : (z + z') ^ p = z ^ p + z' ^ p + p * aeval ![z, z'] C := by
    have := congrArg (aeval ![z, z']) hC0
    simp at this
    rw [this]
    ring
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w + w' - aeval ![z, z'] C) (by rw [map_add, hw, hw', hc]; ring)]
  have hD : KaehlerDifferential.D ℤ K (π (aeval ![z, z'] C)) =
      ((π z + π z') ^ (p - 1) - π z ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z) +
      ((π z + π z') ^ (p - 1) - π z' ^ (p - 1)) • KaehlerDifferential.D ℤ K (π z') := by
    rw [ringHom_aeval_fin_two, kaehlerD_aeval_fin_two, Fin.sum_univ_two, hpd0, hpd1]
    simp
  simp only [map_add, map_sub, hD, smul_add, sub_smul]
  abel

theorem frobLiftPsi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (z z' : Kt) :
    frobLiftPsi p π F hL hF (z * z') =
      π z ^ p • frobLiftPsi p π F hL hF z' + π z' ^ p • frobLiftPsi p π F hL hF z := by
  obtain ⟨w, hw⟩ := frobLift_exists_w p π F hL hF z
  obtain ⟨w', hw'⟩ := frobLift_exists_w p π F hL hF z'
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  rw [frobLiftPsi_spec hL hF hw, frobLiftPsi_spec hL hF hw',
    frobLiftPsi_spec hL hF (w := w * z' ^ p + z ^ p * w' + p * w * w')
      (by rw [map_mul, hw, hw']; ring)]
  simp only [map_add, map_mul, map_pow, map_natCast, hpK, zero_mul, add_zero, Derivation.leibniz,
    kaehlerD_pow_char p, smul_zero, zero_add]
  have e1 : (π z * π z') ^ (p - 1) * π z = π z ^ p * π z' ^ (p - 1) := by
    rw [mul_pow, mul_right_comm, ← pow_succ, Nat.sub_add_cancel hp1]
  have e2 : (π z * π z') ^ (p - 1) * π z' = π z' ^ p * π z ^ (p - 1) := by
    rw [mul_pow, mul_assoc, ← pow_succ, Nat.sub_add_cancel hp1, mul_comm]
  simp only [smul_add, smul_smul, e1, e2]
  abel

theorem frobLiftPsi_natCast_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (y : Kt) :
    frobLiftPsi p π F hL hF ((p : Kt) * y) = 0 := by
  have hp1 : 1 ≤ p := hp.out.one_lt.le
  have hp2 : p - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hpK : (p : K) = 0 := CharP.cast_eq_zero K p
  have e : (p : Kt) * (p : Kt) ^ (p - 1) = (p : Kt) ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp1]
  rw [frobLiftPsi_spec hL hF (w := F y - (p : Kt) ^ (p - 1) * y ^ p)
    (by rw [map_mul, map_natCast, mul_pow]; linear_combination (y ^ p) * e)]
  simp [hpK, hF y, kaehlerD_pow_char p, zero_pow hp2]

theorem frobLiftPsi_congr (hL : IsFlatLift p π) (hF : IsFrob p π F) {z z' : Kt} (h : π z = π z') :
    frobLiftPsi p π F hL hF z = frobLiftPsi p π F hL hF z' := by
  obtain ⟨y, hy⟩ := (hL.ker (z - z')).1 (by rw [map_sub, h, sub_self])
  rw [show z = z' + (p : Kt) * y by rw [← hy]; ring, frobLiftPsi_add, frobLiftPsi_natCast_mul, add_zero]

def frobLiftPhi (hL : IsFlatLift p π) (hF : IsFrob p π F) : K →+ Ω[K⁄ℤ] where
  toFun a := frobLiftPsi p π F hL hF (Function.surjInv hL.surj a)
  map_zero' := by
    have h0 : frobLiftPsi p π F hL hF 0 = 0 := by
      have := frobLiftPsi_add hL hF (0 : Kt) 0
      rw [add_zero] at this
      exact left_eq_add.mp this
    rw [frobLiftPsi_congr hL hF (z' := 0) (by rw [Function.surjInv_eq hL.surj, map_zero]), h0]
  map_add' a b := by
    rw [← frobLiftPsi_add, frobLiftPsi_congr hL hF (z' := Function.surjInv hL.surj a + Function.surjInv hL.surj b)
      (by rw [map_add, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj, Function.surjInv_eq hL.surj])]

theorem frobLiftPhi_apply (hL : IsFlatLift p π) (hF : IsFrob p π F) (z : Kt) :
    frobLiftPhi hL hF (π z) = frobLiftPsi p π F hL hF z :=
  frobLiftPsi_congr hL hF (Function.surjInv_eq hL.surj _)

theorem frobLiftPhi_mul (hL : IsFlatLift p π) (hF : IsFrob p π F) (a b : K) :
    frobLiftPhi hL hF (a * b) = a ^ p • frobLiftPhi hL hF b + b ^ p • frobLiftPhi hL hF a := by
  obtain ⟨z, rfl⟩ := hL.surj a
  obtain ⟨z', rfl⟩ := hL.surj b
  rw [← map_mul, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPhi_apply, frobLiftPsi_mul]

theorem exists_isF_of_flatLift : ∀ {K Kt : Type} [CommRing K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt), IsFlatLift p π → IsFrob p π F → ∃ f, IsF p π F f := by
  intro K Kt _ _ p _ _ π F hL hF
  have univ : ∀ (M : Type) [AddCommGroup M] [Module K M] (D' : K →+ M),
      (∀ a b, D' (a * b) = a • D' b + b • D' a) →
      ∃ g : Ω[K⁄ℤ] →+ M, (∀ a, g (KaehlerDifferential.D ℤ K a) = D' a) ∧
        ∀ (c : K) (v : Ω[K⁄ℤ]), g (c • v) = c • g v := by
    intro M _ _ D' hD'
    let Dv : Derivation ℤ K M := Derivation.mk' D'.toIntLinearMap hD'
    exact ⟨Dv.liftKaehlerDifferential.toAddMonoidHom,
      fun a => Dv.liftKaehlerDifferential_comp_D a,
      fun c v => Dv.liftKaehlerDifferential.map_smul c v⟩
  have hmul : ∀ a b : K, frobLiftPhi hL hF (a * b) =
      frobenius K p a • frobLiftPhi hL hF b + frobenius K p b • frobLiftPhi hL hF a := by
    intro a b
    rw [frobenius_def p a, frobenius_def p b]
    exact frobLiftPhi_mul hL hF a b
  obtain ⟨g, hg, hsm⟩ :=
    @univ (Ω[K⁄ℤ]) _ (Module.compHom _ (frobenius K p)) (frobLiftPhi hL hF) hmul
  refine ⟨g, ?_, ?_⟩
  · intro c v
    have h0 : g (c • v) = frobenius K p c • g v := hsm c v
    rw [frobenius_def p c] at h0
    exact h0
  · intro z w hzw
    have := hg (π z)
    rw [frobLiftPhi_apply, frobLiftPsi_spec hL hF hzw] at this
    exact this

end FrobDiff

end GlobalTheory.DI
end
end

section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DI

theorem mem_latSec_iff {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) (U : X.Opens)
    (v : V) : v ∈ latSec M U ↔ ∀ y ∈ U, v ∈ M y := by
  simp only [latSec, AddSubgroup.mem_iInf]

theorem latSec_anti {X : Scheme.{0}} {V : Type} [AddCommGroup V] (M : X → AddSubgroup V) {U U' : X.Opens}
    (h : U' ≤ U) : latSec M U ≤ latSec M U' := fun v hv =>
  (mem_latSec_iff M U' v).2 fun y hy => (mem_latSec_iff M U v).1 hv y (h hy)

theorem forms_le_of_subset_of_subset {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V] {B B' : Set K}
    {L L' : Set V} (q : ℕ) (hB : B ⊆ B') (hL : L ⊆ L') : forms B L q ≤ forms B' L' q :=
  AddSubgroup.closure_mono fun _ ⟨b, hb, v, hv, e⟩ => ⟨b, hB hb, v, fun k => hL (hv k), e⟩

theorem f_dlog_of_frob {K Kt : Type} [Field K] [CommRing Kt] (p : ℕ) [Fact p.Prime] [CharP K p]
    (π : Kt →+* K) (F : Kt →+* Kt) (f : Ω[K⁄ℤ] →+ Ω[K⁄ℤ]) (hf : IsF p π F f) (g : Kˣ) (z : Kt)
    (hz : π z = g) (hF : F z = z ^ p) : f (dlog g) = dlog g := by
  have key := hf.2 z 0 (by rw [hF]; ring)
  rw [map_zero, map_zero, add_zero, hz] at key
  have hp := (Fact.out : p.Prime)
  have e1 : ((g : K)⁻¹) ^ p * (g : K) ^ (p - 1) = (g : K)⁻¹ := by
    have hg : (g : K) ≠ 0 := g.ne_zero
    obtain ⟨n, hn⟩ : ∃ n, p = n + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
    rw [hn, Nat.add_sub_cancel, pow_succ, mul_comm ((g : K)⁻¹ ^ n), mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hg, one_pow, mul_one]
  simp only [dlog, dK, Units.val_inv_eq_inv_val]
  rw [hf.1, key, smul_smul, e1]

end GlobalTheory.DI

namespace GlobalTheory.DI

theorem decomp_of_isLifted : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  intro p _ X _ _ Z ι _ U n x W G H hnp hgen hcoord hW hlift hEff hdT hCart a b hHyp
  obtain ⟨Kt, _, π, F, hπ, hF, hz, hlog⟩ := hlift
  choose f hf using fun i => exists_isF_of_flatLift p π (F i) hπ (hF i)
  choose h hh using fun i j => exists_isH_of_isFrob p π (F i) (F j) hπ (hF i) (hF j)
  have hd := GlobalTheory.T.exterior_derivative_is_differential X.functionField
  have hdat := isDatum_of_frobenius_lifts p π F (extD X.functionField) f h hπ hF hd hf hh
  choose γ hγ using fun i => exists_isGamma p (f i) (hf i).1

  have hWmono : ∀ s t : Finset ι, s.Nonempty → s ⊆ t → W t ≤ W s := by
    intro s t hs hst y hy
    exact (hW s hs y).2 fun i hi => (hW t (hs.mono hst) y).1 hy i (hst hi)
  have hgenW : ∀ s : Finset ι, s.Nonempty → genericPoint X ∈ W s := fun s hs =>
    (hW s hs _).2 fun i _ => hgen i
  have hNuniv : ∀ a' (s : Finset ι), s.Nonempty →
      logSec Z G a' (W s) ≤ forms (Set.univ : Set X.functionField) (Set.univ : Set Ω[X.functionField⁄ℤ]) a' := by
    intro a' s hs v hv
    have := (mem_latSec_iff _ _ v).1 hv _ (hgenW s hs)
    exact forms_le_of_subset_of_subset a' (Set.subset_univ _) (Set.subset_univ _) this
  refine GlobalTheory.T.splitting_local_integrality (K := X.functionField) (V := Ω[X.functionField⁄ℤ]) p (extD X.functionField) f h γ
    (P := X) (fun s => {y | ∀ i ∈ s, y ∈ U i}) (fun y => locRing y) (fun y => {c | G.RegularAt y c})
    (fun y => dlog '' {g | LogUnit Z y g}) (fun q s => logSec Z G q (W s)) (fun q s => logSec Z H q (W s))
    hd.toIsOddDer hdat hγ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ a b hHyp
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s t hs hst
    exact latSec_anti _ (hWmono s t hs hst)
  · intro q s v hv
    exact hdT q s v hv
  · intro a' s hs
    exact hNuniv a' s hs
  · intro a' s hs hpa
    obtain ⟨i, -⟩ := id hs
    rw [eq_bot_iff]
    refine (hNuniv a' s hs).trans (le_of_eq ?_)
    exact spanForms_eq_bot_of_lt_card X.functionField n (x i) _ _ a' (hcoord i) (by omega)
  · intro a' s hs y hy v hv
    exact (mem_latSec_iff _ _ v).1 hv y ((hW s hs y).2 hy)
  · intro q s v hs _ hv
    refine (mem_latSec_iff _ _ v).2 fun y hy => ?_
    exact forms_le_of_subset_of_subset q (GlobalTheory.T.regular_functions_pth_power_twist p G H y hEff) subset_rfl (hv y ((hW s hs y).1 hy))
  · rintro s y hy i hi _ ⟨g, hg, rfl⟩
    obtain ⟨hfi, -⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    obtain ⟨w, hwA, hw⟩ := hfi i hi
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e, hw g.ne_zero, map_add, ← e]
    exact AddSubgroup.add_mem _ ((GlobalTheory.T.log_forms_generated_dlog Z y).2 g hg) ((GlobalTheory.T.log_forms_generated_dlog Z y).1 w hwA)
  · rintro s y hy i hi j hj _ ⟨g, hg, rfl⟩
    obtain ⟨-, hhij⟩ := divided_frob_logForm p π F f h s (locRing y) (g : X.functionField) hf hh
      (hlog y s hy g hg)
    have e : dlog g = ((g : X.functionField))⁻¹ • KaehlerDifferential.D ℤ X.functionField g := by
      simp only [dlog, dK, Units.val_inv_eq_inv_val]
    rw [e]
    exact hhij i hi j hj
  · intro s j hj
    refine hCart s j hj (γ j) ⟨(hγ j).1, fun l => ?_⟩
    obtain ⟨z, hzx, hzF⟩ := hz j l
    rw [(hγ j).2, f_dlog_of_frob p π (F j) (f j) (hf j) (x j l) z hzx hzF]

end GlobalTheory.DI
end
end

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.GlobalTheory.T.cech_log_forms_frobenius_lift : ∀ (p : ℕ) [Fact p.Prime] {X : Scheme.{0}} [IsIntegral X] [CharP X.functionField p] (Z : Set X) {ι : Type} [LinearOrder ι] (U : ι → X.Opens) {n : ℕ} (x : ι → Fin n → X.functionFieldˣ) (W : Finset ι → X.Opens) (G H : CartierDiv X), n < p → (∀ i, genericPoint X ∈ U i) → (∀ i, IsCoord (x i)) → (∀ s : Finset ι, s.Nonempty → ∀ y, y ∈ W s ↔ ∀ i ∈ s, y ∈ U i) → IsLifted p Z U x → (H - p • G).Eff → (∀ q (s : Finset ι) η, η ∈ logSec Z H q (W s) → extD _ η ∈ logSec Z H (q + 1) (W s)) → (∀ (s : Finset ι), ∀ j ∈ s, ∀ γ, IsCartierMap p (x j) γ → CartierAt (extD _) γ (fun a => logSec Z G a (W s)) (fun a => logSec Z H a (W s))) → ∀ a b, HypZero (extD _) (fun q s => logSec Z H q (W s)) (a + b) → CechZero (fun s => logSec Z G a (W s)) b := by
  atlas_forward_decl _root_.GlobalTheory.DI.decomp_of_isLifted
end
