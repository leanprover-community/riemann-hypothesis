import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ExistsHostDataWild
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.HostDegree
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Places
import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.ResDeg
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.InertiaRamification.Average

section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}

private theorem natCard_sup_mul_natCard_inf {G : Type*} [CommGroup G] (H K : Subgroup G) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) K (H ⊔ K) bot_le le_sup_right
  have h2 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup G) (K ⊓ H) H bot_le inf_le_right
  rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left] at h1 h2
  rw [Subgroup.relIndex_sup_right] at h1
  rw [Subgroup.inf_relIndex_right, inf_comm] at h2
  rw [← h1, ← h2]
  ring

private theorem mem_closure_pair_of_order_two {G : Type*} [CommGroup G] {a b x : G} (ha : a ^ 2 = 1)
    (hb : b ^ 2 = 1) :
    x ∈ Subgroup.closure ({a, b} : Set G) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hA : a ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  have hB : b ∈ Subgroup.closure ({a, b} : Set G) := Subgroup.subset_closure (by simp)
  constructor
  · intro hx
    obtain ⟨i, j, rfl⟩ := Subgroup.mem_closure_pair.1 hx
    have key : ∀ (c : G), c ^ 2 = 1 → ∀ i : ℤ, c ^ i = 1 ∨ c ^ i = c := by
      intro c hc i
      have hc' : c ^ (2 : ℤ) = 1 := by exact_mod_cast hc
      rcases Int.even_or_odd' i with ⟨k, rfl | rfl⟩
      · left; rw [zpow_mul, hc', one_zpow]
      · right; rw [zpow_add, zpow_mul, hc', one_zpow, one_mul, zpow_one]
    rcases key a ha i with h1 | h1 <;> rcases key b hb j with h2 | h2 <;> simp [h1, h2]
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact hA
    · exact hB
    · exact mul_mem hA hB

private theorem conductor_dvd_fieldConductor_of_mem {ψ : DirichletCharacter ℂ N} (hψ : ψ ∈ Y) :
    ψ.conductor ∣ fieldCond Y :=
  (mem_condDvd_iff _ ψ).1.1 (((fieldCond_sup Y ⊥ 1).2.2 _).1 dvd_rfl hψ)

private theorem fieldConductor_dvd_level : fieldCond Y ∣ N :=
  ((fieldCond_sup Y ⊥ 1).2.2 _).2 fun ψ _ => (mem_condDvd_iff _ ψ).1.2 ψ.conductor_dvd_level

private theorem fieldConductor_ne_zero_of_level : fieldCond Y ≠ 0 :=
  ne_zero_of_dvd_ne_zero (NeZero.ne N) fieldConductor_dvd_level

private theorem exists_char_prime_dvd_conductor {p : ℕ} (hp : p.Prime) (h : p ∣ fieldCond Y) :
    ∃ ψ ∈ Y, p ∣ ψ.conductor := by
  have h1 : fieldCond Y ∣
      ∏ ψ ∈ (Set.toFinite (Y : Set (DirichletCharacter ℂ N))).toFinset, ψ.conductor :=
    Finset.lcm_dvd fun ψ hψ => Finset.dvd_prod_of_mem _ hψ
  obtain ⟨ψ, hψ, h2⟩ := hp.prime.exists_mem_finset_dvd (h.trans h1)
  exact ⟨ψ, by simpa using hψ, h2⟩

private theorem host_primes_not_dvd_conductor (h : HostDataOf n d q₁ ch ps Y) :
    d ≠ q₁ ∧ ¬ d ∣ Nat.lcm (4 * n) (fieldCond Y) ∧ ¬ q₁ ∣ Nat.lcm (4 * n) (fieldCond Y) := by
  obtain ⟨⟨e, he, rfl⟩, -, hd, hd16, hq, hq8, -, -, hY⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have key : ∀ p : ℕ, p.Prime → p % 2 = 1 → (∀ ψ ∈ Y, ¬ p ∣ ψ.conductor) →
      ¬ p ∣ Nat.lcm (4 * 2 ^ e) (fieldCond Y) := by
    intro p hp hp2 hpχ hdiv
    rcases (hp.dvd_mul).1 (hdiv.trans (Nat.lcm_dvd_mul _ _)) with h1 | h1
    · rw [h4] at h1
      have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
      omega
    · obtain ⟨ψ, hψ, h2⟩ := exists_char_prime_dvd_conductor hp h1
      exact hpχ ψ hψ h2
  exact ⟨by omega, key d hd (by omega) fun ψ hψ => (hY ψ hψ).1,
    key q₁ hq (by omega) fun ψ hψ => (hY ψ hψ).2⟩

private theorem fieldConductor_real_cyclotomic_sup (h : HostDataOf n d q₁ ch ps Y) :
    fieldCond (realCycSup n Y) = Nat.lcm (4 * n) (fieldCond Y) := by
  obtain ⟨⟨e, he, rfl⟩, hN, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  rw [realCycSup, (fieldCond_sup _ _ 1).1]
  rw [h4] at hN ⊢
  rw [(fieldCond_evenPart_condDvd_two_pow hN (by omega)).1]

private theorem card_character_pair_disjoint_real (h : HostDataOf n d q₁ ch ps Y) :
    Nat.card (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N))) = 4 ∧
      Disjoint (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
        (realCycSup n Y) := by
  obtain ⟨hne, hdL, hqL⟩ := host_primes_not_dvd_conductor h
  have hrest := fieldConductor_real_cyclotomic_sup h
  obtain ⟨-, -, hd, -, hq, -, ⟨hch2, -, hchc⟩, ⟨hps2, -, hpsc⟩, -⟩ := h
  have hprod : d ∣ (ch * ps).conductor := by
    have h1 : ch * ps * ps = ch := by rw [mul_assoc, ← sq, hps2, mul_one]
    have h2 := conductor_mul_dvd_lcm_conductor (ch * ps) ps
    rw [h1, hchc, hpsc] at h2
    rcases (hd.dvd_mul).1 (h2.trans (Nat.lcm_dvd_mul _ _)) with h3 | h3
    · exact h3
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hd hq).1 h3) hne
  have hch1 : ch ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hchc
    exact hd.one_lt.ne hchc
  have hps1 : ps ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hpsc
    exact hq.one_lt.ne hpsc
  have hcp : ch ≠ ps := by
    intro h1
    rw [h1, hpsc] at hchc
    exact hne hchc.symm
  have hcp1 : ch * ps ≠ 1 := by
    intro h1
    rw [h1, conductor_one] at hprod
    exact hd.one_lt.ne' (Nat.dvd_one.1 hprod)
  constructor
  · have hset : ((Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)) :
        Subgroup (DirichletCharacter ℂ N)) : Set (DirichletCharacter ℂ N)) =
        {1, ch, ps, ch * ps} := by
      ext x
      simp only [SetLike.mem_coe, mem_closure_pair_of_order_two hch2 hps2, Set.mem_insert_iff,
        Set.mem_singleton_iff]
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hset, Set.ncard_eq_four]
    refine ⟨1, ch, ps, ch * ps, hch1.symm, hps1.symm, hcp1.symm, hcp, ?_, ?_, rfl⟩
    · intro h1
      exact hps1 (left_eq_mul.1 h1)
    · intro h1
      exact hch1 (right_eq_mul.1 h1)
  · rw [Subgroup.disjoint_def]
    intro x hx hx'
    have hle := ((fieldCond_sup (realCycSup n Y) ⊥ 1).2.2
      (Nat.lcm (4 * n) (fieldCond Y))).1 (by rw [hrest])
    have hxc := (mem_condDvd_iff _ x).1.1 (hle hx')
    rcases (mem_closure_pair_of_order_two hch2 hps2).1 hx with rfl | rfl | rfl | rfl
    · rfl
    · exact absurd (hchc ▸ hxc) hdL
    · exact absurd (hpsc ▸ hxc) hqL
    · exact absurd (hprod.trans hxc) hdL

theorem HostDataOf.card (h : HostDataOf n d q₁ ch ps Y) :
    Disjoint (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N))) (realCycSup n Y) ∧
      ∃ s o : ℕ, Nat.card ↥(evenPart (condDvd N (4 * n)) ⊓ Y) = 2 ^ s ∧
        s ≤ (fieldCond Y).factorization 2 - 2 ∧ Nat.card Y = 2 ^ s * o ∧
        (evenPart (condDvd N (4 * n))).relIndex (realCycSup n Y) = o ∧
        Nat.card (realCycSup n Y) = n * o ∧
        Nat.card (hostCharsOf n ch ps Y) = 4 * n * o ∧
        Nat.card (evenPart (hostCharsOf n ch ps Y)) = 2 * n * o ∧
        8 ∣ Nat.card (evenPart (hostCharsOf n ch ps Y)) ∧
        o ≤ Nat.card Y ∧ Nat.card Y ≤ Nat.totient (fieldCond Y) := by
  obtain ⟨hA, hdisj⟩ := card_character_pair_disjoint_real h
  refine ⟨hdisj, ?_⟩
  obtain ⟨⟨e, he, rfl⟩, hN, -, -, -, -, ⟨-, hodd, -⟩, -⟩ := h
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hB : Nat.card (evenPart (condDvd N (4 * 2 ^ e))) = 2 ^ e := by
    rw [h4] at hN ⊢
    rw [card_evenPart_condDvd_two_pow hN, Nat.add_sub_cancel]
  have haN : 2 ^ (fieldCond Y).factorization 2 ∣ N :=
    (Nat.ordProj_dvd _ 2).trans fieldConductor_dvd_level
  have hle : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Y ≤
      evenPart (condDvd N (2 ^ (fieldCond Y).factorization 2)) := by
    rintro ψ ⟨h1, h2⟩
    obtain ⟨h3, h5⟩ := ((card_evenPart _).1 ψ).1 h1
    refine ((card_evenPart _).1 ψ).2 ⟨(mem_condDvd_iff _ ψ).1.2 ?_, h5⟩
    have h6 := (mem_condDvd_iff _ ψ).1.1 h3
    rw [h4] at h6
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h6
    have h7 : ψ.conductor ∣ fieldCond Y := conductor_dvd_fieldConductor_of_mem h2
    rw [hj] at h7 ⊢
    exact pow_dvd_pow 2
      ((Nat.prime_two.pow_dvd_iff_le_factorization fieldConductor_ne_zero_of_level).1 h7)
  have hdv := Subgroup.card_dvd_of_le hle
  rw [card_evenPart_condDvd_two_pow haN] at hdv
  obtain ⟨s, hs, hcard⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdv
  have hdv2 := Subgroup.card_dvd_of_le
    (inf_le_right : evenPart (condDvd N (4 * 2 ^ e)) ⊓ Y ≤ _)
  rw [hcard] at hdv2
  obtain ⟨o, ho⟩ := hdv2
  have hC : Nat.card ↥(realCycSup (2 ^ e) Y) = 2 ^ e * o := by
    have h1 := natCard_sup_mul_natCard_inf (evenPart (condDvd N (4 * 2 ^ e))) Y
    rw [hcard, hB, ho] at h1
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 ^ s by positivity)
    rw [realCycSup, h1]
    ring
  have hR : (evenPart (condDvd N (4 * 2 ^ e))).relIndex (realCycSup (2 ^ e) Y) = o := by
    have h1 := Subgroup.relIndex_mul_relIndex (⊥ : Subgroup (DirichletCharacter ℂ N))
      (evenPart (condDvd N (4 * 2 ^ e))) (realCycSup (2 ^ e) Y) bot_le le_sup_left
    rw [Subgroup.relIndex_bot_left, Subgroup.relIndex_bot_left, hB, hC] at h1
    exact Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ e by positivity) h1
  have hH : Nat.card (hostCharsOf (2 ^ e) ch ps Y) = 4 * 2 ^ e * o := by
    have h1 := natCard_sup_mul_natCard_inf (Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)))
      (realCycSup (2 ^ e) Y)
    rw [hdisj.eq_bot, Subgroup.card_bot, mul_one, hA, hC, ← mul_assoc] at h1
    exact h1
  have hmem : ch ∈ hostCharsOf (2 ^ e) ch ps Y :=
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hE : Nat.card (evenPart (hostCharsOf (2 ^ e) ch ps Y)) = 2 * 2 ^ e * o := by
    have h1 := (card_evenPart _).2 ⟨ch, hmem, hodd⟩
    rw [hH] at h1
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by norm_num)
    rw [← h1]
    ring
  refine ⟨s, o, hcard, hs, ho, hR, hC, hH, hE, ?_, ?_, ?_⟩
  · obtain ⟨f, rfl⟩ := Nat.exists_eq_add_of_le he
    rw [hE]
    exact ⟨2 ^ f * o, by ring⟩
  · rw [ho]
    exact Nat.le_mul_of_pos_left o (by positivity)
  · rw [← (mem_condDvd_iff (fieldCond Y) (1 : DirichletCharacter ℂ N)).2
      fieldConductor_dvd_level]
    exact Subgroup.card_le_of_le (((fieldCond_sup Y ⊥ 1).2.2 _).1 dvd_rfl)

end KStar.Ram
end

section
namespace KStar.Ram

open DirichletCharacter

section PrimePower

variable {l v : ℕ} [hl : Fact l.Prime]

private instance bounds_neZero : NeZero (l ^ v) := ⟨pow_ne_zero _ hl.out.ne_zero⟩

private def boundsSub (m d : ℕ) [NeZero m] : Subgroup (DirichletCharacter ℂ m) where
  carrier := {θ | θ.conductor ∣ d}
  mul_mem' {a b} ha hb := (conductor_mul_dvd_lcm_conductor a b).trans (Nat.lcm_dvd ha hb)
  one_mem' := by simp [conductor_one]
  inv_mem' {a} ha := by simpa [conductor_inv] using ha

end PrimePower

variable {N : ℕ} [NeZero N] (l : ℕ) [Fact l.Prime]

end KStar.Ram
end

section
namespace KStar.Ram

open DirichletCharacter

variable {N : ℕ} [NeZero N] {n d q₁ : ℕ} {ch ps : DirichletCharacter ℂ N}
  {Y : Subgroup (DirichletCharacter ℂ N)}

private theorem hv_unr_iff (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    (∀ ψ ∈ X, ¬ l ∣ ψ.conductor) ↔ X ≤ (localPart N l).ker := by
  constructor
  · intro h ψ hψ
    exact (MonoidHom.mem_ker).2 ((localPart_eq_one_iff l ψ).2.2 (h ψ hψ))
  · intro h ψ hψ
    exact (localPart_eq_one_iff l ψ).2.1 ((MonoidHom.mem_ker).1 (h hψ))

private theorem hv_unr_sup (l : ℕ) [Fact l.Prime] {X Y : Subgroup (DirichletCharacter ℂ N)}
    (hX : ∀ ψ ∈ X, ¬ l ∣ ψ.conductor) (hY : ∀ ψ ∈ Y, ¬ l ∣ ψ.conductor) :
    ∀ ψ ∈ X ⊔ Y, ¬ l ∣ ψ.conductor :=
  (hv_unr_iff l _).2 (sup_le ((hv_unr_iff l _).1 hX) ((hv_unr_iff l _).1 hY))

private theorem hv_unr_zpowers (l : ℕ) [Fact l.Prime] {φ : DirichletCharacter ℂ N}
    (h : ¬ l ∣ φ.conductor) : ∀ ψ ∈ Subgroup.zpowers φ, ¬ l ∣ ψ.conductor :=
  (hv_unr_iff l _).2 ((Subgroup.zpowers_le).2
    ((MonoidHom.mem_ker).2 ((localPart_eq_one_iff l φ).2.2 h)))

omit [NeZero N] in
private theorem hv_closure_pair (ch ps : DirichletCharacter ℂ N) :
    Subgroup.closure ({ch, ps} : Set (DirichletCharacter ℂ N)) =
      Subgroup.zpowers ch ⊔ Subgroup.zpowers ps := by
  rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure,
    Subgroup.zpowers_eq_closure]

omit [NeZero N] in
private theorem hv_not_dvd {l d : ℕ} (hl : l.Prime) (hd : d.Prime) (hne : l ≠ d)
    {ch : DirichletCharacter ℂ N} (h : IsImagQuad ch d) : ¬ l ∣ ch.conductor := by
  rw [h.2.2]
  exact fun h' => hne ((Nat.prime_dvd_prime_iff_eq hl hd).1 h')

omit [NeZero N] in
private theorem hv_mem (n : ℕ) (ch ps : DirichletCharacter ℂ N)
    (Y : Subgroup (DirichletCharacter ℂ N)) :
    ch ∈ hostCharsOf n ch ps Y ∧ ps ∈ hostCharsOf n ch ps Y ∧
      evenPart (condDvd N (4 * n)) ≤ hostCharsOf n ch ps Y :=
  ⟨Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    Subgroup.mem_sup_left (Subgroup.subset_closure (by simp)),
    le_sup_of_le_right le_sup_left⟩

private theorem hv_arith1 {n f g r : ℕ} (hn : 0 < n) (h : n * f * g = 4 * n * r) :
    g * f = 4 * r := by
  apply Nat.eq_of_mul_eq_mul_left hn
  linarith

private theorem hv_arith2 {f g r : ℕ} (h : 2 * g * f = 4 * r) : g * f = 2 * r := by
  linarith

omit [NeZero N] in
private theorem hv_mem_charKer (X : Subgroup (DirichletCharacter ℂ N)) (u : (ZMod N)ˣ) :
    u ∈ charKer X ↔ ∀ ψ ∈ X, ψ (u : ZMod N) = 1 := by
  simp only [charKer, Subgroup.mem_iInf, MonoidHom.mem_ker, ← Units.val_eq_one,
    MulChar.coe_toUnitHom]

private theorem hv_inertia (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    inertiaUnits N l ⊔ charKer X = charKer (X ⊓ (localPart N l).ker) := by
  rw [← (annihilator_charKer ⊥ (inertiaUnits N l ⊔ charKer X)).2.1]
  congr 1
  ext ψ
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, (localPart_eq_one_iff l ψ).1, mem_annihilator_iff]
  constructor
  · intro h
    refine ⟨?_, fun u hu => h u (Subgroup.mem_sup_left hu)⟩
    rw [← (annihilator_charKer X ⊥).1, mem_annihilator_iff]
    exact fun u hu => h u (Subgroup.mem_sup_right hu)
  · rintro ⟨hX, hI⟩ u hu
    obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hu
    rw [Units.val_mul, map_mul, hI a ha, (hv_mem_charKer X b).1 hb ψ hX, one_mul]

private theorem hv_inertia_sup (l : ℕ) [Fact l.Prime] (A B : Subgroup (DirichletCharacter ℂ N))
    (hA : ∀ ψ ∈ A, ¬ l ∣ ψ.conductor) :
    inertiaUnits N l ⊔ charKer (A ⊔ B) = charKer (A ⊔ (B ⊓ (localPart N l).ker)) := by
  rw [hv_inertia, sup_inf_assoc_of_le _ ((hv_unr_iff l A).1 hA)]

private theorem hv_card (l : ℕ) [Fact l.Prime] (X : Subgroup (DirichletCharacter ℂ N)) :
    ramIdx l X * Nat.card ↥(X ⊓ (localPart N l).ker) = Nat.card X := by
  unfold ramIdx
  rw [← Subgroup.relIndex_ker, ← Subgroup.inf_relIndex_left, Subgroup.relIndex,
    ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (inf_le_left : X ⊓ (localPart N l).ker ≤ X)).toEquiv, Subgroup.index_mul_card]

private theorem hv_fieldCond_ne (X : Subgroup (DirichletCharacter ℂ N)) : fieldCond X ≠ 0 :=
  ne_zero_of_dvd_ne_zero (NeZero.ne N) (((fieldCond_sup X ⊥ 1).2.2 N).2
    fun ψ _ => (mem_condDvd_iff N ψ).1.2 ψ.conductor_dvd_level)

private theorem hv_two (e : ℕ) (Y : Subgroup (DirichletCharacter ℂ N)) :
    realCycSup (2 ^ e) Y ⊓ (localPart N 2).ker =
      realCycSup (2 ^ e) Y ⊓ condDvd N (ordCompl[2] (fieldCond Y)) := by
  ext ψ
  rw [Subgroup.mem_inf, Subgroup.mem_inf]
  refine and_congr_right fun hψ => ?_
  rw [MonoidHom.mem_ker, (localPart_eq_one_iff 2 ψ).2, (mem_condDvd_iff _ ψ).1]
  constructor
  · intro h2
    have hle : realCycSup (2 ^ e) Y ≤ condDvd N (4 * 2 ^ e * fieldCond Y) := by
      refine sup_le (fun φ hφ => ?_) (((fieldCond_sup Y ⊥ 1).2.2 _).1 (dvd_mul_left _ _))
      exact (mem_condDvd_iff _ φ).1.2 (((mem_condDvd_iff (4 * 2 ^ e) φ).1.1
        (((card_evenPart _).1 φ).1 hφ).1).trans (dvd_mul_right _ _))
    have h1 := (mem_condDvd_iff _ ψ).1.1 (hle hψ)
    have hc : Nat.Coprime ψ.conductor (4 * 2 ^ e) := by
      rw [show 4 * 2 ^ e = 2 ^ (e + 2) by ring]
      exact Nat.Coprime.pow_right _ ((Nat.prime_two.coprime_iff_not_dvd.2 h2).symm)
    exact Nat.dvd_ordCompl_of_dvd_not_dvd (hc.dvd_of_dvd_mul_left h1) h2
  · intro h1 h2
    exact Nat.not_dvd_ordCompl Nat.prime_two (hv_fieldCond_ne Y) (h2.trans h1)

theorem HostDataOf.at_two (h : HostDataOf n d q₁ ch ps Y) :
    n ∣ ramIdx 2 (hostCharsOf n ch ps Y) ∧ 2 ∣ ramIdx 2 (hostCharsOf n ch ps Y) ∧
      inertiaUnits N 2 ⊔ charKer (hostCharsOf n ch ps Y) =
        charKer (Subgroup.closure {ch, ps} ⊔
          (realCycSup n Y ⊓ condDvd N (ordCompl[2] (fieldCond Y)))) ∧
      ramIdx 2 (hostCharsOf n ch ps Y) *
          Nat.card ↥(realCycSup n Y ⊓ condDvd N (ordCompl[2] (fieldCond Y))) =
        Nat.card (realCycSup n Y) ∧
      resDeg 2 (hostCharsOf n ch ps Y) = Nat.lcm 2 (resDeg 2 (realCycSup n Y)) ∧
      (¬ 2 ∣ fieldCond Y →
        ramIdx 2 (hostCharsOf n ch ps Y) = n ∧
        resDeg 2 (hostCharsOf n ch ps Y) = Nat.lcm 2 (resDeg 2 Y) ∧
        numPlaces 2 (hostCharsOf n ch ps Y) * Nat.lcm 2 (resDeg 2 Y) = 4 * Nat.card Y ∧
        numPlaces 2 (evenPart (hostCharsOf n ch ps Y)) * Nat.lcm 2 (resDeg 2 Y) =
          2 * Nat.card Y) := by
  obtain ⟨-, s, o, -, hs, ho, -, -, hc, -⟩ := h.card
  obtain ⟨⟨e, he, rfl⟩, hN, hd, hd16, hq, hq8, hch, hps, hY'⟩ := h
  obtain ⟨m1, m2, m3⟩ := hv_mem (2 ^ e) ch ps Y
  have h4 : 4 * 2 ^ e = 2 ^ (e + 2) := by ring
  have hF := (fieldCond_evenPart_condDvd_two_pow (N := N) (k := e + 2) (h4 ▸ hN) (by omega)).2
  rw [← h4, Nat.add_sub_cancel] at hF
  have hdv : 2 ^ e ∣ ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) := by
    have hdv : ramIdx 2 (evenPart (condDvd N (4 * 2 ^ e))) ∣
        ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) :=
      Subgroup.card_dvd_of_le (Subgroup.map_mono m3)
    rwa [hF.1] at hdv
  have u1 := hv_not_dvd Nat.prime_two hd (by omega) hch
  have u2 := hv_not_dvd Nat.prime_two hq (by omega) hps
  have uE := hv_unr_sup 2 (hv_unr_zpowers 2 u1) (hv_unr_zpowers 2 u2)
  obtain ⟨v1, v2, -⟩ := IsImagQuad.values hd hq (by omega) hq8 hch hps
  have hneg : orderOf (-1 : ℂ) = 2 := by
    apply orderOf_eq_prime
    · norm_num
    · norm_num
  have e0 : hostCharsOf (2 ^ e) ch ps Y =
      (Subgroup.zpowers ch ⊔ Subgroup.zpowers ps) ⊔ realCycSup (2 ^ e) Y := by
    rw [hostCharsOf, hv_closure_pair]
  have hr0 : ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) = ramIdx 2 (realCycSup (2 ^ e) Y) := by
    rw [e0, (resDeg_sup 2 _ _ uE).2.1]
  have hf0 : resDeg 2 (hostCharsOf (2 ^ e) ch ps Y) =
      Nat.lcm 2 (resDeg 2 (realCycSup (2 ^ e) Y)) := by
    rw [e0, (resDeg_sup 2 _ _ uE).1,
      (resDeg_sup 2 _ _ (hv_unr_zpowers 2 u1)).1, resDeg_zpowers 2 ch u1, resDeg_zpowers 2 ps u2,
      show ch.primitiveCharacter ((2 : ℕ) : ZMod ch.conductor) = 1 from v1, orderOf_one,
      Nat.lcm_one_left, v2, hneg]
  refine ⟨hdv, (dvd_pow_self 2 (by omega)).trans hdv, ?_, ?_, hf0, fun h2 => ?_⟩
  · rw [e0, hv_inertia_sup 2 _ _ uE, hv_two, hv_closure_pair]
  · rw [hr0, ← hv_two, hv_card]
  have uY : ∀ ψ ∈ Y, ¬ 2 ∣ ψ.conductor :=
    (ramIdx_eq_one_iff 2 Y).1.1 ((ramIdx_eq_one_iff 2 Y).2.1.2 h2)
  have e1 : realCycSup (2 ^ e) Y = Y ⊔ evenPart (condDvd N (4 * 2 ^ e)) := sup_comm _ _
  have hr : ramIdx 2 (hostCharsOf (2 ^ e) ch ps Y) = 2 ^ e := by
    rw [hr0, e1, (resDeg_sup 2 _ _ uY).2.1, hF.1]
  have hf : resDeg 2 (hostCharsOf (2 ^ e) ch ps Y) = Nat.lcm 2 (resDeg 2 Y) := by
    rw [hf0, e1, (resDeg_sup 2 _ _ uY).1, hF.2, Nat.lcm_one_right]
  have hc0 : (fieldCond Y).factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd h2
  have hs0 : s = 0 := by omega
  rw [hs0, pow_zero, one_mul] at ho
  have hp := ramIdx_mul_resDeg_mul_numPlaces 2 (hostCharsOf (2 ^ e) ch ps Y)
  rw [hr, hf, hc, ← ho] at hp
  have hg := hv_arith1 (Nat.two_pow_pos e) hp
  refine ⟨hr, hf, hg, ?_⟩
  rw [(split_of_splitsFor 2 _ m1 hch.2.1 v1).2.2.1] at hg
  exact hv_arith2 hg

end KStar.Ram
end
