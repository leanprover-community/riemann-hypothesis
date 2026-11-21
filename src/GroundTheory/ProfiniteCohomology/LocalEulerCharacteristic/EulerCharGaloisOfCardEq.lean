import Mathlib
import GroundTheory.LocalFields.RamificationStructure
import GroundTheory.LocalFields.UnramifiedRootsOfUnity
import GroundTheory.ProfiniteCohomology.GaloisModules.FixedField
import GroundTheory.LocalFields.LubinTatePoints
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Descent
import GroundTheory.ProfiniteCohomology.InflationRestriction
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.UnitsPower
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Cohomology
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing.Vanishing
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCount
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.MainCoind
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Coprime
import GroundTheory.ProfiniteCohomology.LocalClassFormation.FiniteVanishing

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

def coprimePart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | (orderOf x).Coprime p}

def primaryPart (p : ℕ) (Q : Type*) [Group Q] : Subgroup Q :=
  Subgroup.closure {x : Q | ∃ n : ℕ, orderOf x = p ^ n}

variable {G : Type*} [Group G]

def coprimeQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (coprimePart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def primaryQuotientPreimage (N : Subgroup G) [N.Normal] (p : ℕ) : Subgroup G :=
  (primaryPart p (G ⧸ N)).comap (QuotientGroup.mk' N)

def coprimeRelPreimage (N₀ N₁ : Subgroup G) [N₁.Normal] (p : ℕ) : Subgroup G :=
  (coprimeQuotientPreimage (N₁.subgroupOf N₀) p).map N₀.subtype

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

section Parts

variable {Q Q' : Type*} [Group Q] [Group Q']

theorem map_coprimePart_le (p : ℕ) (f : Q →* Q') :
    (coprimePart p Q).map f ≤ coprimePart p Q' := by
  rw [coprimePart, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.subset_closure (Nat.Coprime.coprime_dvd_left (orderOf_map_dvd f x) hx)

instance coprimePart_normal (p : ℕ) : (coprimePart p Q).Normal where
  conj_mem x hx g := by
    simpa using map_coprimePart_le p (MulAut.conj g).toMonoidHom (Subgroup.mem_map_of_mem _ hx)

instance primaryPart_normal (p : ℕ) : (primaryPart p Q).Normal where
  conj_mem x hx g := by
    have h : (primaryPart p Q).map (MulAut.conj g).toMonoidHom ≤ primaryPart p Q := by
      rw [primaryPart, MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨y, ⟨n, hy⟩, rfl⟩
      exact Subgroup.subset_closure ⟨n, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.orderOf_eq, hy]⟩
    simpa using h (Subgroup.mem_map_of_mem _ hx)

theorem mem_coprimePart_iff_of_comm {p : ℕ} (hQ : ∀ a b : Q, a * b = b * a) {x : Q} :
    x ∈ coprimePart p Q ↔ (orderOf x).Coprime p := by
  let S : Subgroup Q :=
    { carrier := {x | (orderOf x).Coprime p}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb ↦
        Nat.Coprime.coprime_dvd_left ((Commute.orderOf_mul_dvd_lcm (hQ a b)).trans
          (Nat.lcm_dvd_mul _ _)) (Nat.Coprime.mul_left ha hb)
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : coprimePart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl

theorem mem_primaryPart_iff_of_comm {p : ℕ} (hp : p.Prime) (hQ : ∀ a b : Q, a * b = b * a)
    {x : Q} : x ∈ primaryPart p Q ↔ ∃ n : ℕ, orderOf x = p ^ n := by
  let S : Subgroup Q :=
    { carrier := {x | ∃ n : ℕ, orderOf x = p ^ n}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := fun {a b} ha hb ↦ by
        obtain ⟨m, hm⟩ := ha
        obtain ⟨n, hn⟩ := hb
        have h := (Commute.orderOf_mul_dvd_lcm (hQ a b)).trans (Nat.lcm_dvd_mul _ _)
        rw [hm, hn, ← pow_add] at h
        obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hp).1 h
        exact ⟨k, hk⟩
      inv_mem' := fun {a} ha ↦ by simpa using ha }
  have h : primaryPart p Q = S :=
    le_antisymm ((Subgroup.closure_le S).2 fun _ hx ↦ hx) fun _ hx ↦ Subgroup.subset_closure hx
  rw [h]
  rfl

theorem exists_pow_prime_pow_mem_coprimePart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ k : ℕ, x ^ p ^ k ∈ coprimePart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  refine ⟨e, Subgroup.subset_closure ?_⟩
  have hdvd : p ^ e ∣ orderOf x := ⟨m, he⟩
  rw [Set.mem_ofPred_eq, orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, he,
    Nat.mul_div_cancel_left _ (pow_pos hp.pos _)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm

theorem exists_coprime_pow_mem_primaryPart {p : ℕ} (hp : p.Prime) {x : Q}
    (hx : IsOfFinOrder x) : ∃ m : ℕ, m.Coprime p ∧ x ^ m ∈ primaryPart p Q := by
  obtain ⟨e, m, hm, he⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hx.orderOf_pos.ne' p hp.one_lt.ne'
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  refine ⟨m, ((Nat.Prime.coprime_iff_not_dvd hp).2 hm).symm, Subgroup.subset_closure ⟨e, ?_⟩⟩
  have hdvd : m ∣ orderOf x := ⟨p ^ e, by rw [he, mul_comm]⟩
  rw [orderOf_pow_of_dvd hm0 hdvd, he, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

theorem mem_of_pow_mem_of_pow_mem {S : Subgroup Q} {x : Q} {a b : ℕ} (hab : a.Coprime b)
    (ha : x ^ a ∈ S) (hb : x ^ b ∈ S) : x ∈ S := by
  have h := Nat.gcd_eq_gcd_ab a b
  rw [hab.gcd_eq_one, Nat.cast_one] at h
  have hx : x = (x ^ a) ^ (Nat.gcdA a b) * (x ^ b) ^ (Nat.gcdB a b) := by
    rw [← zpow_natCast x a, ← zpow_natCast x b, ← zpow_mul, ← zpow_mul, ← zpow_add, ← h,
      zpow_one]
  rw [hx]
  exact mul_mem (zpow_mem ha _) (zpow_mem hb _)

theorem eq_one_of_pow_eq_one_of_coprime {p : ℕ} {x : Q} (hx : (orderOf x).Coprime p)
    (h : x ^ p = 1) : x = 1 :=
  orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hx dvd_rfl (orderOf_dvd_of_pow_eq_one h))

theorem coprime_card_of_pow_eq_one {p : ℕ} [Fact p.Prime] [Finite Q]
    (h : ∀ x : Q, x ^ p = 1 → x = 1) : (Nat.card Q).Coprime p := by
  refine ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun hdvd ↦ ?_).symm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have h1 := h x (hx ▸ pow_orderOf_eq_one x)
  rw [h1, orderOf_one] at hx
  exact (Fact.out : p.Prime).one_lt.ne hx

end Parts

section LemmaG

variable {G : Type*} [Group G]

theorem isCyclic_quotient_of_le {M N : Subgroup G} [M.Normal] [N.Normal] (h : M ≤ N)
    [IsCyclic (G ⧸ M)] : IsCyclic (G ⧸ N) :=
  isCyclic_of_surjective (QuotientGroup.map M N (MonoidHom.id G) h) fun y ↦ by
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨g, rfl⟩

variable (N : Subgroup G) [N.Normal]

instance coprimeQuotientPreimage_normal (p : ℕ) : (coprimeQuotientPreimage N p).Normal :=
  (coprimePart_normal p).comap _

instance primaryQuotientPreimage_normal (p : ℕ) : (primaryQuotientPreimage N p).Normal :=
  (primaryPart_normal p).comap _

theorem le_coprimeQuotientPreimage (p : ℕ) : N ≤ coprimeQuotientPreimage N p := by
  intro x hx
  rw [coprimeQuotientPreimage, Subgroup.mem_comap, QuotientGroup.mk'_apply,
    (QuotientGroup.eq_one_iff x).2 hx]
  exact one_mem _

theorem isPGroup_quotient_coprimeQuotientPreimage [Finite G] {p : ℕ} (hp : p.Prime) :
    IsPGroup p (G ⧸ coprimeQuotientPreimage N p) := by
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨k, hk⟩ :=
    exists_pow_prime_pow_mem_coprimePart hp (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  refine ⟨k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, coprimeQuotientPreimage,
    Subgroup.mem_comap, map_pow]
  exact hk

theorem exists_card_quotient_coprimeQuotientPreimage_eq_pow [Finite G] {p : ℕ} (hp : p.Prime) :
    ∃ a : ℕ, Nat.card (G ⧸ coprimeQuotientPreimage N p) = p ^ a := by
  have := Fact.mk hp
  exact IsPGroup.iff_card.1 (isPGroup_quotient_coprimeQuotientPreimage N hp)

theorem coprime_card_quotient_primaryQuotientPreimage [Finite G] {l : ℕ} (hl : l.Prime) :
    (Nat.card (G ⧸ primaryQuotientPreimage N l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, primaryQuotientPreimage,
    Subgroup.mem_comap, map_pow] at hy
  rw [QuotientGroup.eq_one_iff, primaryQuotientPreimage, Subgroup.mem_comap]
  obtain ⟨m, hm, hgm⟩ :=
    exists_coprime_pow_mem_primaryPart hl (isOfFinOrder_of_finite (QuotientGroup.mk' N g))
  exact mem_of_pow_mem_of_pow_mem hm.symm hy hgm

theorem coprime_card_coprimeQuotientPreimage_quotient [Finite G] {p : ℕ} (hp : p.Prime)
    (G₀ G₁ : Subgroup G) [G₀.Normal] [G₁.Normal] (h10 : G₁ ≤ G₀) [IsCyclic (G ⧸ G₀)]
    (hG0 : (Nat.card (G₀ ⧸ G₁.subgroupOf G₀)).Coprime p) :
    (Nat.card (coprimeQuotientPreimage G₀ p ⧸
      G₁.subgroupOf (coprimeQuotientPreimage G₀ p))).Coprime p := by
  have := Fact.mk hp
  apply coprime_card_of_pow_eq_one
  intro y hy
  obtain ⟨⟨h, hH⟩, rfl⟩ := QuotientGroup.mk_surjective y
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.coe_pow] at hy
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  have h0 : h ∈ G₀ := by
    rw [coprimeQuotientPreimage, Subgroup.mem_comap, mem_coprimePart_iff_of_comm hcomm] at hH
    have h1 := eq_one_of_pow_eq_one_of_coprime hH (by
      rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact h10 hy)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h1 := eq_one_of_pow_eq_one_of_coprime
    (x := (QuotientGroup.mk (⟨h, h0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
    (Nat.Coprime.coprime_dvd_left (orderOf_dvd_natCard _) hG0) (by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        Subgroup.coe_pow]
      exact hy)
  rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1

section Relative

variable (G₀ G₁ : Subgroup G) [G₁.Normal]

theorem coprimeRelPreimage_le (p : ℕ) : coprimeRelPreimage G₀ G₁ p ≤ G₀ :=
  Subgroup.map_subtype_le _

theorem mem_coprimeRelPreimage_iff {p : ℕ} {x : G} :
    x ∈ coprimeRelPreimage G₀ G₁ p ↔ ∃ hx : x ∈ G₀,
      (QuotientGroup.mk (⟨x, hx⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀) ∈ coprimePart p _ := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

instance coprimeRelPreimage_normal [G₀.Normal] (p : ℕ) : (coprimeRelPreimage G₀ G₁ p).Normal where
  conj_mem x hx g := by
    rw [mem_coprimeRelPreimage_iff] at hx ⊢
    obtain ⟨hx0, hx⟩ := hx
    let c : G₀ →* G₀ :=
      { toFun := fun y ↦ ⟨g * y * g⁻¹, (inferInstance : G₀.Normal).conj_mem y y.2 g⟩
        map_one' := by ext; simp
        map_mul' := fun a b ↦ by
          ext
          simp only [Subgroup.coe_mul]
          group }
    have hc : G₁.subgroupOf G₀ ≤ (G₁.subgroupOf G₀).comap c := fun y hy ↦ by
      rw [Subgroup.mem_subgroupOf] at hy
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact (inferInstance : G₁.Normal).conj_mem _ hy g
    exact ⟨(inferInstance : G₀.Normal).conj_mem x hx0 g,
      map_coprimePart_le p (QuotientGroup.map _ _ c hc) (Subgroup.mem_map_of_mem _ hx)⟩

theorem coprime_card_coprimeRelPreimage [Finite G] {l p : ℕ} (hl : l.Prime) (hp : p.Prime)
    (hlp : l ≠ p) (hG1 : IsPGroup p G₁) [IsCyclic (G₀ ⧸ G₁.subgroupOf G₀)] :
    (Nat.card (coprimeRelPreimage G₀ G₁ l)).Coprime l := by
  have := Fact.mk hl
  apply coprime_card_of_pow_eq_one
  rintro ⟨b, hb⟩ hbl
  have hbl' : b ^ l = 1 := by
    simpa using congrArg Subtype.val hbl
  obtain ⟨hb0, hb'⟩ := (mem_coprimeRelPreimage_iff G₀ G₁).1 hb
  have hcomm : ∀ a c : G₀ ⧸ G₁.subgroupOf G₀, a * c = c * a :=
    fun a c ↦ (IsCyclic.commGroup).mul_comm a c
  rw [mem_coprimePart_iff_of_comm hcomm] at hb'
  have h1 := eq_one_of_pow_eq_one_of_coprime hb' (by
    rw [← QuotientGroup.mk_pow, show (⟨b, hb0⟩ : G₀) ^ l = 1 from Subtype.ext (by simpa using hbl'),
      QuotientGroup.mk_one])
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  obtain ⟨k, hk⟩ := hG1 ⟨b, h1⟩
  have hbk : b ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hco : (orderOf b).Coprime l :=
    Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hbk)
      (Nat.Coprime.pow_left k ((Nat.coprime_primes hp hl).2 hlp.symm))
  exact Subtype.ext (eq_one_of_pow_eq_one_of_coprime hco hbl')

variable [G₀.Normal]

theorem isPGroup_primaryQuotientPreimage_quotient [Finite G] {l : ℕ} (hl : l.Prime)
    [IsCyclic (G ⧸ G₀)] :
    IsPGroup l (primaryQuotientPreimage G₀ l ⧸
      (coprimeRelPreimage G₀ G₁ l).subgroupOf (primaryQuotientPreimage G₀ l)) := by
  intro y
  obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk_surjective y
  have hcomm : ∀ a b : G ⧸ G₀, a * b = b * a := fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at ha
  obtain ⟨n, hn⟩ := ha
  have ha0 : a ^ l ^ n ∈ G₀ := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  obtain ⟨k, hk⟩ := exists_pow_prime_pow_mem_coprimePart hl
    (isOfFinOrder_of_finite (QuotientGroup.mk (⟨a ^ l ^ n, ha0⟩ : G₀) : G₀ ⧸ G₁.subgroupOf G₀))
  have hB : (a ^ l ^ n) ^ l ^ k ∈ coprimeRelPreimage G₀ G₁ l := by
    refine (mem_coprimeRelPreimage_iff G₀ G₁).2 ⟨pow_mem ha0 _, ?_⟩
    rw [← QuotientGroup.mk_pow] at hk
    exact hk
  refine ⟨n + k, ?_⟩
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_pow,
    pow_add, pow_mul]
  exact hB

end Relative

end LemmaG

section Galois

open GroundTheory.LocalField ValuativeRel IntermediateField

theorem algEquiv_apply_eq_of_pow_prime_pow_apply_eq {K L : Type*} [Field K] [Field L]
    [Algebra K L] {l : ℕ} (hl : l.Prime) {ζ : L} (hζ : ζ ^ l = 1) (σ : L ≃ₐ[K] L) {n : ℕ}
    (h : (σ ^ l ^ n) ζ = ζ) : σ ζ = ζ := by
  rcases (Nat.dvd_prime hl).1 (orderOf_dvd_of_pow_eq_one hζ) with h1 | hl'
  · rw [orderOf_eq_one_iff.1 h1, map_one]
  have hprim : IsPrimitiveRoot ζ l := hl' ▸ IsPrimitiveRoot.orderOf ζ
  have : NeZero l := ⟨hl.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ, map_one])
  have key : ∀ m : ℕ, (σ ^ m) ζ = ζ ^ k ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, AlgEquiv.mul_apply, ← hk, map_pow, ih, ← pow_mul, ← pow_succ]
  have hmod : ∀ a : ℕ, ζ ^ a = ζ ^ (a % l) := fun a ↦ by
    conv_lhs => rw [← Nat.div_add_mod a l, pow_add, pow_mul, hζ, one_pow, one_mul]
  have hkm : k ^ l ^ n % l = k % l := by
    have := Fact.mk hl
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_pow, ZMod.pow_card_pow]
  rw [key] at h
  calc σ ζ = ζ ^ k := hk.symm
    _ = ζ ^ (k ^ l ^ n % l) := by rw [hkm, ← hmod]
    _ = ζ := by rw [← hmod, h]

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

instance isCyclic_quotient_lowerRamificationGroup_zero :
    IsCyclic ((L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0) := by
  have : IsCyclic ((L ≃ₐ[K] L) ⧸ (residueAlgEquiv K L).ker) :=
    isCyclic_of_injective (QuotientGroup.kerLift _) (QuotientGroup.kerLift_injective _)
  exact isCyclic_of_surjective
    (QuotientGroup.quotientMulEquivOfEq (lowerRamificationGroup_zero K L).symm).toMonoidHom
    (MulEquiv.surjective _)

theorem natCast_residueField_ne_zero {l : ℕ} (hl : l.Prime) (hlp : l ≠ ringChar 𝓀[K]) :
    (l : 𝓀[L]) ≠ 0 := by
  rw [Ne, ringChar.spec, ← Algebra.ringChar_eq 𝓀[K] 𝓀[L]]
  intro h
  exact hlp ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hl).1 h).symm

variable {K L} in

theorem apply_eq_of_mem_lowerRamificationGroup_zero {m : ℕ} (hm : (m : 𝓀[L]) ≠ 0)
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ lowerRamificationGroup K L 0) {ζ : L} (hζ : ζ ^ m = 1) :
    σ ζ = ζ := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hm
  let z : 𝒪[L] := ⟨ζ, mem_integer_of_pow_eq_one hm0 hζ⟩
  have hz : z ^ m = 1 := Subtype.ext (by simpa [z] using hζ)
  have h := eq_of_pow_eq_one_of_residue_eq hm (x := integerAlgEquiv K L σ z) (y := z)
    (by rw [← map_pow, hz, map_one]) hz (residue_integerAlgEquiv_of_mem_zero K L hσ z)
  simpa [z] using congrArg Subtype.val h

theorem lowerRamificationGroup_one_le_coprimeQuotientPreimage :
    lowerRamificationGroup K L 1 ≤
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) :=
  (lowerRamificationGroup_antitone K L zero_le_one).trans (le_coprimeQuotientPreimage _ _)

theorem isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup :
    IsCyclic ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
  isCyclic_quotient_of_le (le_coprimeQuotientPreimage _ _)

theorem exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow :
    ∃ a : ℕ, Nat.card ((L ≃ₐ[K] L) ⧸
      coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) =
        ringChar 𝓀[K] ^ a :=
  exists_card_quotient_coprimeQuotientPreimage_eq_pow _ (CharP.char_is_prime 𝓀[K] _)

theorem coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one :
    (Nat.card (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K]) ⧸
      (lowerRamificationGroup K L 1).subgroupOf
        (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))).Coprime
      (ringChar 𝓀[K]) := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeQuotientPreimage_quotient (CharP.char_is_prime 𝓀[K] _) _ _
    (lowerRamificationGroup_antitone K L zero_le_one)
    (coprime_card_lowerRamificationGroup_zero_quotient K L)

theorem pow_eq_one_mem_fixedField_lowerRamificationGroup_one {ζ : L}
    (hζ : ζ ^ ringChar 𝓀[K] = 1) : ζ ∈ fixedField (lowerRamificationGroup K L 1) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨σ, hσ⟩
  have hσn : σ ^ ringChar 𝓀[K] ^ n = 1 := by simpa using congrArg Subtype.val hn
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq (CharP.char_is_prime 𝓀[K] _) hζ σ
    (by rw [hσn, AlgEquiv.one_apply])

theorem coprime_card_coprimeRelPreimage_lowerRamificationGroup {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) :
    (Nat.card (coprimeRelPreimage (lowerRamificationGroup K L 0)
      (lowerRamificationGroup K L 1) l)).Coprime l := by
  have := isCyclic_lowerRamificationGroup_zero_quotient K L
  exact coprime_card_coprimeRelPreimage _ _ hl (CharP.char_is_prime 𝓀[K] _) hlp
    (isPGroup_lowerRamificationGroup_one K L)

theorem isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup {l : ℕ}
    (hl : l.Prime) :
    IsPGroup l (primaryQuotientPreimage (lowerRamificationGroup K L 0) l ⧸
      (coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l).subgroupOf
        (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) :=
  isPGroup_primaryQuotientPreimage_quotient _ _ hl

theorem coprime_card_quotient_primaryQuotientPreimage_lowerRamificationGroup {l : ℕ}
    (hl : l.Prime) :
    (Nat.card ((L ≃ₐ[K] L) ⧸
      primaryQuotientPreimage (lowerRamificationGroup K L 0) l)).Coprime l :=
  coprime_card_quotient_primaryQuotientPreimage _ hl

theorem pow_eq_one_mem_fixedField_primaryQuotientPreimage {l : ℕ} (hl : l.Prime)
    (hlp : l ≠ ringChar 𝓀[K]) {ζ : L} (hζ : ζ ^ l = 1) :
    ζ ∈ fixedField (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) := by
  refine (mem_fixedField_iff _ _).2 fun σ hσ ↦ ?_
  have hcomm : ∀ a b : (L ≃ₐ[K] L) ⧸ lowerRamificationGroup K L 0, a * b = b * a :=
    fun a b ↦ (IsCyclic.commGroup).mul_comm a b
  rw [primaryQuotientPreimage, Subgroup.mem_comap, mem_primaryPart_iff_of_comm hl hcomm] at hσ
  obtain ⟨n, hn⟩ := hσ
  have h0 : σ ^ l ^ n ∈ lowerRamificationGroup K L 0 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← QuotientGroup.mk'_apply, ← hn,
      pow_orderOf_eq_one]
  exact algEquiv_apply_eq_of_pow_prime_pow_apply_eq hl hζ σ
    (apply_eq_of_mem_lowerRamificationGroup_zero (natCast_residueField_ne_zero K L hl hlp) h0 hζ)

end Galois

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

section Trivial

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (N : Subgroup G) [N.Normal]

def resTrivMor {X Y : Rep.{u} k G} (hX : ∀ (m : N) (x : X), X.ρ m x = x)
    (hY : ∀ (m : N) (y : Y), Y.ρ m y = y) (f : X →ₗ[k] Y) :
    Rep.res N.subtype X ⟶ Rep.res N.subtype Y :=
  Rep.ofHom ⟨f, fun m => by
    ext x
    change f (X.ρ m x) = Y.ρ m (f x)
    rw [hX, hY]⟩

omit [TopologicalSpace G] [IsTopologicalGroup G] [N.Normal] in
@[simp]
theorem resTrivMor_hom_apply {X Y : Rep.{u} k G} (hX : ∀ (m : N) (x : X), X.ρ m x = x)
    (hY : ∀ (m : N) (y : Y), Y.ρ m y = y) (f : X →ₗ[k] Y) (x : X) :
    (resTrivMor N hX hY f).hom x = f x :=
  rfl

theorem cohomologyMap_comp_cohomologyConj_of_apply {T A : Rep.{u} k G} [IsDiscreteRep T]
    [IsDiscreteRep A] (φ ψ : Rep.res N.subtype T ⟶ Rep.res N.subtype A) (g : G)
    (h : ∀ t : T, A.ρ g (φ.hom t) = ψ.hom (T.ρ g t)) (n : ℕ) :
    cohomologyMap φ n ≫ cohomologyConj A N n g = cohomologyConj T N n g ≫ cohomologyMap ψ n := by
  rw [← cohomologyMapAlong_id_eq_cohomologyMap, ← cohomologyMapAlong_id_eq_cohomologyMap,
    cohomologyConj, cohomologyConj, ← cohomologyMapAlong_comp, ← cohomologyMapAlong_comp]
  refine cohomologyMapAlong_congr _ _ _ _ (by ext s; simp) (fun t => ?_) n
  exact h t

theorem cohomologyConj_eq_cohomologyMap_of_sum {T A : Rep.{u} k G} [IsDiscreteRep T]
    [IsDiscreteRep A] (hT : ∀ (m : N) (t : T), T.ρ m t = t) (hA : ∀ (m : N) (a : A), A.ρ m a = a)
    {ι : Type} [Fintype ι] (i : ι → (T →ₗ[k] A)) (p : ι → (A →ₗ[k] T))
    (hip : ∑ j, i j ∘ₗ p j = LinearMap.id) (g : G) (hg : ∀ t : T, T.ρ g t = t) (n : ℕ)
    (hconj : cohomologyConj T N n g = 𝟙 _) :
    cohomologyConj A N n g = cohomologyMap (resTrivMor N hA hA (A.ρ g)) n := by
  have hipa : ∀ a : A, ∑ j, i j (p j a) = a := fun a => by
    have := congrArg (fun f : A →ₗ[k] A => f a) hip
    simpa [LinearMap.sum_apply] using this
  have hsum : ∑ j, resTrivMor N hA hT (p j) ≫ resTrivMor N hT hA (i j) = 𝟙 _ := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    exact hipa a
  have hsum' : ∑ j, resTrivMor N hA hT (p j) ≫ resTrivMor N hT hA (A.ρ g ∘ₗ i j) =
      resTrivMor N hA hA (A.ρ g) := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    change ∑ j, A.ρ g (i j (p j a)) = A.ρ g a
    rw [← map_sum, hipa]
  have hj : ∀ j, cohomologyMap (resTrivMor N hT hA (i j)) n ≫ cohomologyConj A N n g =
      cohomologyMap (resTrivMor N hT hA (A.ρ g ∘ₗ i j)) n := fun j => by
    rw [cohomologyMap_comp_cohomologyConj_of_apply N _ (resTrivMor N hT hA (A.ρ g ∘ₗ i j)) g
      (fun t => by rw [hg t]; rfl) n, hconj, Category.id_comp]
  calc cohomologyConj A N n g = 𝟙 _ ≫ cohomologyConj A N n g := (Category.id_comp _).symm
    _ = ∑ j, cohomologyMap (resTrivMor N hA hT (p j)) n ≫
          (cohomologyMap (resTrivMor N hT hA (i j)) n ≫ cohomologyConj A N n g) := by
        rw [← cohomologyMap_id, ← hsum, cohomologyMap_sum, Preadditive.sum_comp]
        simp only [cohomologyMap_comp, Category.assoc]
    _ = cohomologyMap (resTrivMor N hA hA (A.ρ g)) n := by
        simp only [hj, ← cohomologyMap_comp]
        rw [← cohomologyMap_sum, hsum']

end Trivial

section Descent

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G) [(U : Subgroup G).Normal]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [(U : Subgroup G).Normal] in

theorem sum_quotient_out_apply_eq_zero (A : Rep.{u} k G)
    (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0) (a : A) :
    ∑ c : G ⧸ (U : Subgroup G), A.ρ c.out a = 0 := by
  apply hinv
  intro g
  rw [map_sum]
  have hc : ∀ c : G ⧸ (U : Subgroup G), A.ρ g (A.ρ c.out a) = A.ρ (g • c).out a := by
    intro c
    obtain ⟨m, hm⟩ := QuotientGroup.mk_out_eq_mul (U : Subgroup G) (g * c.out)
    have e : (g • c).out = g * c.out * m := by
      rw [← hm]
      congr 1
      conv_lhs => rw [← QuotientGroup.out_eq' c]
      rfl
    rw [e, map_mul, Module.End.mul_apply, hA m, ← Module.End.mul_apply, ← map_mul]
  simp_rw [hc]
  exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)

theorem subsingleton_cohomology_of_cohomologyConj_eq (A : Rep.{u} k G) [IsDiscreteRep A]
    (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0)
    (hbij : Function.Bijective fun a : A => (U : Subgroup G).index • a) (n : ℕ)
    (hconj : ∀ g : G, cohomologyConj A (U : Subgroup G) n g =
      cohomologyMap (resTrivMor (U : Subgroup G) hA hA (A.ρ g)) n) :
    Subsingleton (cohomology A n) := by
  have hAU : Function.Bijective fun a : Rep.res (U : Subgroup G).subtype A =>
      (U : Subgroup G).index • a := hbij
  have hzero : ∑ c : G ⧸ (U : Subgroup G), resTrivMor (U : Subgroup G) hA hA (A.ρ c.out) = 0 := by
    ext a
    rw [Rep.sum_hom, Representation.IntertwiningMap.toLinearMap_sum, LinearMap.sum_apply]
    exact sum_quotient_out_apply_eq_zero U A hA hinv a
  refine ⟨fun x y => cohomologyRes_injective_of_bijective U A hbij n ?_⟩
  suffices h : ∀ z : cohomology A n, (cohomologyRes A (U : Subgroup G) n).hom z = 0 by
    rw [h x, h y]
  intro z
  set w := (cohomologyRes A (U : Subgroup G) n).hom z
  have hw : ∀ g : G, (cohomologyConj A (U : Subgroup G) n g).hom w = w :=
    cohomologyRes_apply_mem_cohomologyConjInvariants A _ n z
  apply (bijective_nsmul_cohomology (Rep.res (U : Subgroup G).subtype A) _ hAU n).1
  change (U : Subgroup G).index • w = (U : Subgroup G).index • 0
  rw [smul_zero]
  calc (U : Subgroup G).index • w = ∑ c : G ⧸ (U : Subgroup G), w := by
        rw [Finset.sum_const, Finset.card_univ, Subgroup.index_eq_card, Nat.card_eq_fintype_card]
    _ = ∑ c : G ⧸ (U : Subgroup G), (cohomologyConj A (U : Subgroup G) n c.out).hom w := by
        simp only [hw]
    _ = (cohomologyMap (∑ c : G ⧸ (U : Subgroup G),
          resTrivMor (U : Subgroup G) hA hA (A.ρ c.out)) n).hom w := by
        simp only [hconj, cohomologyMap_sum, ModuleCat.hom_sum, LinearMap.sum_apply]
    _ = 0 := by
        rw [hzero, cohomologyMap_zero]
        rfl

theorem subsingleton_cohomology_of_sum {T A : Rep.{u} k G} [IsDiscreteRep T] [IsDiscreteRep A]
    (hT : ∀ (g : G) (t : T), T.ρ g t = t) (hA : ∀ (m : (U : Subgroup G)) (a : A), A.ρ m a = a)
    (hinv : ∀ a : A, (∀ g : G, A.ρ g a = a) → a = 0)
    (hbij : Function.Bijective fun a : A => (U : Subgroup G).index • a)
    {ι : Type} [Fintype ι] (i : ι → (T →ₗ[k] A)) (p : ι → (A →ₗ[k] T))
    (hip : ∑ j, i j ∘ₗ p j = LinearMap.id) (n : ℕ)
    (hconj : ∀ g : G, cohomologyConj T (U : Subgroup G) n g = 𝟙 _) :
    Subsingleton (cohomology A n) :=
  subsingleton_cohomology_of_cohomologyConj_eq U A hA hinv hbij n fun g =>
    cohomologyConj_eq_cohomologyMap_of_sum (U : Subgroup G) (fun m t => hT m t) hA i p hip g
      (hT g) n (hconj g)

end Descent

section InfRes

variable {k Γ : Type u} [CommRing k] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]

variable [CompactSpace Γ] [TotallyDisconnectedSpace Γ]

theorem subsingleton_cohomology_of_normal (W : Subgroup Γ) [W.Normal] (hW : IsClosed (W : Set Γ))
    (A : Rep.{u} k Γ) [IsDiscreteRep A] (hinv : ∀ a : A, (∀ w : W, A.ρ w a = a) → a = 0) (q : ℕ)
    (hq : ∀ i, 0 < i → i ≤ q → Subsingleton (cohomology (Rep.res W.subtype A) i)) :
    ∀ i ≤ q, Subsingleton (cohomology A i) := by
  intro i hi
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have : Subsingleton (ModuleCat.of k A.ρ.invariants) := ⟨fun a b => Subtype.ext <| by
      rw [hinv a (fun w => a.2 w), hinv b (fun w => b.2 w)]⟩
    exact (H0Iso A).toLinearEquiv.toEquiv.subsingleton
  · have hz : ∀ j, 0 < j → j < i → IsZero (cohomology (Rep.res W.subtype A) j) := fun j hj hji =>
      (ModuleCat.isZero_iff_subsingleton).2 (hq j hj (by omega))
    have hex := infRes_exact A W hW (Nat.pos_iff_ne_zero.1 hpos) hz
    have : Subsingleton (A.quotientToInvariants W) := ⟨fun a b => Subtype.ext <| by
      rw [hinv a (fun w => a.2 w), hinv b (fun w => b.2 w)]⟩
    have hs := subsingleton_cohomology_of_subsingleton (A.quotientToInvariants W) i
    have hres := hq i hpos hi
    have hmem : ∀ z : cohomology A i, z = 0 := by
      intro z
      have hk : z ∈ LinearMap.ker (cohomologyRes A W i).hom :=
        LinearMap.mem_ker.2 (Subsingleton.elim _ _)
      rw [← hex.2] at hk
      obtain ⟨y, rfl⟩ := hk
      rw [Subsingleton.elim y 0, map_zero]
    exact ⟨fun x y => by rw [hmem x, hmem y]⟩

end InfRes

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open GroundTheory.LocalField ValuativeRel IsLocalRing

section Group

variable {G : Type*} [CommGroup G]

theorem mul_inv_mem_of_iterate_eq {l m : ℕ} (P O : Subgroup G) (s : G →* G)
    (hPl : ∀ y : G, y ^ l ∈ P) (hO : ∀ x : G, s x * x⁻¹ ∈ O)
    (hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P) (hm : m.Coprime l) (hsm : ∀ x : G, s^[m] x = x) (x : G) :
    s x * x⁻¹ ∈ P := by
  have hPn : P.Normal := Subgroup.normal_of_isMulCommutative P
  have hq : ∀ a b : G, a * b⁻¹ ∈ P → (a : G ⧸ P) = b := fun a b h => by
    rw [QuotientGroup.eq]
    have := P.inv_mem h
    rwa [mul_inv_rev, inv_inv, mul_comm] at this
  set c := s x * x⁻¹ with hc
  have hOs : ∀ e ∈ O, s e ∈ O := fun e he => by
    have := O.mul_mem (hO e) he
    rwa [inv_mul_cancel_right] at this
  have hcO : ∀ j : ℕ, s^[j] c ∈ O := fun j => by
    induction j with
    | zero => exact hO x
    | succ j ih => rw [Function.iterate_succ_apply']; exact hOs _ ih
  have hcj : ∀ j : ℕ, ((s^[j] c : G) : G ⧸ P) = c := fun j => by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', hq _ _ (hOP _ (hcO j)), ih]
  have hsx : s x = x * c := by rw [hc, mul_comm (s x), mul_inv_cancel_left]
  have hxj : ∀ j : ℕ, ((s^[j] x : G) : G ⧸ P) = (x : G ⧸ P) * (c : G ⧸ P) ^ j := fun j => by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply, hsx, iterate_map_mul, QuotientGroup.mk_mul, ih,
        hcj, pow_succ, mul_assoc]
  have h1 : (c : G ⧸ P) ^ m = 1 := by
    have h := hxj m
    rw [hsm] at h
    exact mul_left_cancel (h.symm.trans (mul_one _).symm)
  have h2 : (c : G ⧸ P) ^ l = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hPl c
  have h3 : (c : G ⧸ P) = 1 := by
    have h := (pow_gcd_eq_one (a := (c : G ⧸ P))).2 ⟨h1, h2⟩
    rwa [Nat.Coprime.gcd_eq_one hm, pow_one] at h
  exact (QuotientGroup.eq_one_iff c).1 h3

end Group

section LocalField

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem exists_map_units_eq_mul_pow {l m : ℕ} (hl : (l : 𝓀[F]) ≠ 0) (σ : F ≃+* F)
    (hval : ∀ x : F, valuation F (σ x) = valuation F x)
    (hin : ∀ x : F, valuation F x ≤ 1 → valuation F (σ x - x) < 1)
    (hm : m.Coprime l) (hσm : ∀ x : F, σ^[m] x = x) (u : Fˣ) :
    ∃ y : Fˣ, Units.map (σ : F →* F) u = u * y ^ l := by
  set s : Fˣ →* Fˣ := Units.map (σ : F →* F) with hs_def
  have hs : ∀ x : Fˣ, ((s x : Fˣ) : F) = σ x := fun x => rfl
  let P : Subgroup Fˣ := (powMonoidHom l : Fˣ →* Fˣ).range
  let O : Subgroup Fˣ :=
    { carrier := {x | valuation F (x : F) = 1}
      one_mem' := by simp
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, Units.val_mul, map_mul] at ha hb ⊢
        rw [ha, hb, mul_one]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_ofPred_eq, Units.val_inv_eq_inv_val, map_inv₀] at ha ⊢
        rw [ha, inv_one] }
  have hmemO : ∀ x : Fˣ, x ∈ O ↔ valuation F (x : F) = 1 := fun x => Iff.rfl
  have hv0 : ∀ x : Fˣ, valuation F (x : F) ≠ 0 := fun x => (valuation F).ne_zero_iff.2 x.ne_zero
  have hO : ∀ x : Fˣ, s x * x⁻¹ ∈ O := fun x => by
    rw [hmemO, Units.val_mul, hs, map_mul, Units.val_inv_eq_inv_val, map_inv₀, hval,
      mul_inv_cancel₀ (hv0 x)]
  have hOP : ∀ e ∈ O, s e * e⁻¹ ∈ P := fun e he => by
    rw [hmemO] at he
    set t := s e * e⁻¹ with ht
    have htv : valuation F (t : F) = 1 := (hmemO t).1 (hO e)
    have ht1 : valuation F ((t : F) - 1) < 1 := by
      have e1 : (t : F) - 1 = (σ e - e) * (e : F)⁻¹ := by
        rw [ht, Units.val_mul, hs, Units.val_inv_eq_inv_val, sub_mul,
          mul_inv_cancel₀ e.ne_zero]
      rw [e1, map_mul, map_inv₀, he, inv_one, mul_one]
      exact hin _ he.le
    have hnt : normalizedValuation F (t : F) = 1 := by
      rw [← map_one (normalizedValuation F), normalizedValuation_eq_iff, map_one]
      exact htv
    obtain ⟨t', ht'⟩ := mem_range_unitsIncl_iff.2 hnt
    have ht'F : ((t' : 𝒪[F]) : F) = t := by rw [← coe_unitsIncl, ht']
    have hmem : t' ∈ unitFiltration F 1 := by
      rw [mem_unitFiltration, pow_one, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      intro hu
      have h1 := valuation_unit hu.unit
      rw [IsUnit.unit_spec] at h1
      have h2 : (((t' : 𝒪[F]) - 1 : 𝒪[F]) : F) = (t : F) - 1 := by
        push_cast
        rw [ht'F]
      rw [h2] at h1
      exact (lt_irrefl _ (h1 ▸ ht1))
    obtain ⟨z, -, hz⟩ := exists_pow_eq_of_mem_unitFiltration_one hl hmem
    refine ⟨unitsIncl F z, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hz, ht']
  have hiter : ∀ (j : ℕ) (x : Fˣ), ((s^[j] x : Fˣ) : F) = σ^[j] (x : F) := fun j => by
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  have hsm : ∀ x : Fˣ, s^[m] x = x := fun x => Units.ext (by rw [hiter, hσm])
  obtain ⟨y, hy⟩ := mul_inv_mem_of_iterate_eq P O s (fun y => ⟨y, rfl⟩) hO hOP hm hsm u
  refine ⟨y, ?_⟩
  rw [powMonoidHom_apply] at hy
  rw [hy, mul_comm (s u), mul_inv_cancel_left]

end LocalField

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section FixedField

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]

theorem isNonarchimedeanLocalField_fixedField (V : OpenSubgroup Gal(Ksep/K)) :
    letI := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
    IsNonarchimedeanLocalField (fixedField (V : Subgroup Gal(Ksep/K))) := by
  have hrel := valuativeRel_eq_finiteExtensionStructure K (L := fixedField (V : Subgroup Gal(Ksep/K)))
  have h1 := finiteExtensionStructure_isNonarchimedeanLocalField K (fixedField (V : Subgroup Gal(Ksep/K)))
  rw [← hrel] at h1
  exact h1

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in

theorem valuation_le_valuation_iff_coe (E : IntermediateField K Ksep) (x y : E) :
    valuation E x ≤ valuation E y ↔ valuation Ksep (x : Ksep) ≤ valuation Ksep (y : Ksep) := by
  rw [← (valuation E).vle_iff_le, ← (valuation Ksep).vle_iff_le, IntermediateField.coe_vle_coe_iff]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_le_one_iff_coe (E : IntermediateField K Ksep) (x : E) :
    valuation E x ≤ 1 ↔ valuation Ksep (x : Ksep) ≤ 1 := by
  rw [← map_one (valuation E), valuation_le_valuation_iff_coe, IntermediateField.coe_one, map_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_lt_one_iff_coe (E : IntermediateField K Ksep) (x : E) :
    valuation E x < 1 ↔ valuation Ksep (x : Ksep) < 1 := by
  rw [← not_le, ← not_le, ← map_one (valuation E), valuation_le_valuation_iff_coe,
    IntermediateField.coe_one, map_one]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [IsSepClosure K Ksep]
  [ValuativeExtension K Ksep] in
theorem valuation_eq_iff_coe (E : IntermediateField K Ksep) (x y : E) :
    valuation E x = valuation E y ↔ valuation Ksep (x : Ksep) = valuation Ksep (y : Ksep) := by
  rw [le_antisymm_iff, le_antisymm_iff, valuation_le_valuation_iff_coe, valuation_le_valuation_iff_coe]

theorem natCast_residueField_fixedField_ne_zero {l : ℕ} (hl : (l : 𝓀[K]) ≠ 0)
    (V : OpenSubgroup Gal(Ksep/K)) :
    letI := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
    (l : 𝓀[fixedField (V : Subgroup Gal(Ksep/K))]) ≠ 0 := by
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have h := (algebraMap 𝓀[K] 𝓀[fixedField (V : Subgroup Gal(Ksep/K))]).injective.ne hl
  rwa [map_natCast, map_zero] at h

omit [IsSepClosure K Ksep] in

theorem natCast_ne_zero_of_residueField {l : ℕ} (hl : (l : 𝓀[K]) ≠ 0) : (l : K) ≠ 0 := by
  intro h
  apply hl
  have : ((l : 𝒪[K]) : K) = 0 := by push_cast; exact h
  have h0 : (l : 𝒪[K]) = 0 := Subtype.ext this
  rw [← map_natCast (residue 𝒪[K]), h0, map_zero]

end FixedField

end GroundTheory.ProfCoh

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section DegreeZero

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem cohomologyConj_zero_eq_id_of_apply (A : Rep.{u} k G) [IsDiscreteRep A] (N : Subgroup G)
    [N.Normal] (g : G) (hg : ∀ a : A, A.ρ g a = a) : cohomologyConj A N 0 g = 𝟙 _ := by
  have hinj : Function.Injective (H0Iso (Rep.res N.subtype A)).hom.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine ModuleCat.hom_ext (LinearMap.ext fun x => hinj ?_)
  rw [H0Iso_hom_cohomologyConj]
  exact Subtype.ext (hg _)

end DegreeZero

section Conj

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]
  {l : ℕ} {W V : OpenSubgroup Gal(Ksep/K)}

theorem apply_eq_of_valuation_sub_lt_one (hl : (l : 𝓀[K]) ≠ 0)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    {g : Gal(Ksep/K)}
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep (g x - x) < 1)
    {ζ : Ksep} (hζ : ζ ^ l = 1) : g ζ = ζ := by
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have hlF := natCast_residueField_fixedField_ne_zero hl V
  have hl0 : l ≠ 0 := by rintro rfl; simp at hlF
  have hgζ : (g ζ) ^ l = 1 := by rw [← map_pow, hζ, map_one]
  let a : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hμ ζ hζ⟩
  let b : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨g ζ, hμ _ hgζ⟩
  have ha : a ^ l = 1 := Subtype.ext (by simpa [a] using hζ)
  have hb : b ^ l = 1 := Subtype.ext (by simpa [b] using hgζ)
  let x : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] := ⟨a, mem_integer_of_pow_eq_one hl0 ha⟩
  let y : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] := ⟨b, mem_integer_of_pow_eq_one hl0 hb⟩
  have hx : x ^ l = 1 := Subtype.ext (by simpa [x] using ha)
  have hy : y ^ l = 1 := Subtype.ext (by simpa [y] using hb)
  have hres : residue 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] y =
      residue 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] x := by
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
    intro hu
    have h1 := valuation_unit hu.unit
    rw [IsUnit.unit_spec] at h1
    have hle : valuation Ksep ζ ≤ 1 :=
      (valuation_le_one_iff_coe _ a).1 ((Valuation.mem_integer_iff _ _).1 x.2)
    have hlt : valuation (fixedField (V : Subgroup Gal(Ksep/K))) (((y - x :
        𝒪[fixedField (V : Subgroup Gal(Ksep/K))])) : fixedField (V : Subgroup Gal(Ksep/K))) < 1 := by
      rw [valuation_lt_one_iff_coe]
      exact hg ζ (hμ ζ hζ) hle
    exact lt_irrefl _ (h1 ▸ hlt)
  have := eq_of_pow_eq_one_of_residue_eq hlF hy hx hres
  exact congrArg (fun z : 𝒪[fixedField (V : Subgroup Gal(Ksep/K))] =>
    ((z : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep)) this

variable (h : V ≤ W) [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]

include h in

theorem cohomologyConj_one_galRootsOfUnity_eq_id (hl : (l : 𝓀[K]) ≠ 0)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l) (g : (W : Subgroup Gal(Ksep/K)))
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1) :
    cohomologyConj (Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf W) 1 g = 𝟙 _ := by
  have hlK := natCast_ne_zero_of_residueField hl
  let := (finiteExtensionStructure K (fixedField (V : Subgroup Gal(Ksep/K)))).top
  have := isNonarchimedeanLocalField_fixedField V
  have hlF := natCast_residueField_fixedField_ne_zero hl V
  set σ : fixedField (V : Subgroup Gal(Ksep/K)) ≃+* fixedField (V : Subgroup Gal(Ksep/K)) :=
    (fixedFieldConjHom h g).toRingEquiv with hσ
  have hσx : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      ((σ x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = (g : Gal(Ksep/K)) (x : Ksep) :=
    fun x => rfl
  have hval : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      valuation (fixedField (V : Subgroup Gal(Ksep/K))) (σ x) =
        valuation (fixedField (V : Subgroup Gal(Ksep/K))) x := fun x => by
    rw [valuation_eq_iff_coe, hσx]
    exact valuation_algEquiv_apply_of_isAlgebraic (K := K) (g : Gal(Ksep/K)) (x : Ksep)
  have hin : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      valuation (fixedField (V : Subgroup Gal(Ksep/K))) x ≤ 1 →
        valuation (fixedField (V : Subgroup Gal(Ksep/K))) (σ x - x) < 1 := fun x hx => by
    rw [valuation_lt_one_iff_coe]
    rw [valuation_le_one_iff_coe] at hx
    have e : (((σ x - x : fixedField (V : Subgroup Gal(Ksep/K)))) : Ksep) =
        (g : Gal(Ksep/K)) (x : Ksep) - x := by
      rw [← hσx]
      rfl
    rw [e]
    exact hg x x.2 hx
  have hiter : ∀ (j : ℕ) (x : fixedField (V : Subgroup Gal(Ksep/K))),
      ((σ^[j] x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = ((g : Gal(Ksep/K)) ^ j) (x : Ksep) := by
    intro j
    induction j with
    | zero => intro x; rfl
    | succ j ih =>
      intro x
      rw [Function.iterate_succ_apply', hσx, ih, pow_succ', AlgEquiv.mul_apply]
  have hσm : ∀ x : fixedField (V : Subgroup Gal(Ksep/K)),
      σ^[(V : Subgroup Gal(Ksep/K)).relIndex W] x = x := fun x => by
    apply Subtype.ext
    rw [hiter]
    have hmem := Subgroup.pow_index_mem ((V : Subgroup Gal(Ksep/K)).subgroupOf W) g
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow] at hmem
    exact (mem_fixedField_iff _ _).1 x.2 _ hmem
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  obtain ⟨u, rfl⟩ := kummerOpenHom_surjective h hlK x
  change (cohomologyConj _ _ 1 g).hom (kummerOpenHom h hlK u) = kummerOpenHom h hlK u
  rw [← kummerOpenHom_smul, ← sub_eq_zero, ← map_sub, kummerOpenHom_eq_zero_iff]
  obtain ⟨y, hy⟩ := exists_map_units_eq_mul_pow hlF σ hval hin hind hσm (Additive.toMul u)
  refine ⟨Additive.ofMul y, ?_⟩
  have hsm : Additive.toMul (fixedFieldConjHom h g • u) =
      Units.map (σ : fixedField (V : Subgroup Gal(Ksep/K)) →* fixedField (V : Subgroup Gal(Ksep/K)))
        (Additive.toMul u) :=
    Units.ext (Subtype.ext rfl)
  rw [eq_sub_iff_add_eq, add_comm]
  apply Additive.toMul.injective
  rw [toMul_add, toMul_nsmul, toMul_ofMul, hsm, hy]

include h in

theorem cohomologyConj_galRootsOfUnity_eq_id (hl : (l : 𝓀[K]) ≠ 0)
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l) (g : (W : Subgroup Gal(Ksep/K)))
    (hg : ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)), valuation Ksep x ≤ 1 →
      valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1) {n : ℕ} (hn : n ≤ 2) :
    cohomologyConj (Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l))
      ((V : Subgroup Gal(Ksep/K)).subgroupOf W) n g = 𝟙 _ := by
  interval_cases n
  · refine cohomologyConj_zero_eq_id_of_apply _ _ g fun a => ?_
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    exact apply_eq_of_valuation_sub_lt_one hl hμ hg
      (by
        have h1 := congrArg Units.val ((mem_rootsOfUnity l _).1 (Additive.toMul a).2)
        rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
        convert h1 using 2
        rfl)
  · exact cohomologyConj_one_galRootsOfUnity_eq_id h hl hind g hg
  · exact cohomologyConj_two_galRootsOfUnity_eq_id (natCast_ne_zero_of_residueField hl) h g

end Conj

end GroundTheory.ProfCoh

namespace GroundTheory.ProfCoh

open CategoryTheory GroundTheory.LocalField ValuativeRel IsLocalRing IntermediateField

section Helpers

def addHomToULiftLinear {M N : Type*} [AddCommGroup M] [AddCommGroup N] {iM : Module (ULift.{0} ℤ) M}
    {iN : Module (ULift.{0} ℤ) N} (f : M →+ N) :
    @LinearMap (ULift.{0} ℤ) (ULift.{0} ℤ) _ _ (RingHom.id _) M N _ _ iM iN where
  toFun := f
  map_add' := f.map_add
  map_smul' c x := by
    obtain ⟨n⟩ := c
    have h1 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) M _ _ iM n x
    have h2 := @Int.cast_smul_eq_zsmul (ULift.{0} ℤ) N _ _ iN n (f x)
    have e : ((n : ℤ) : ULift.{0} ℤ) = ULift.up n := rfl
    rw [RingHom.id_apply, ← e, h1, h2, map_zsmul]

theorem addHomToULiftLinear_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {iM : Module (ULift.{0} ℤ) M} {iN : Module (ULift.{0} ℤ) N} (f : M →+ N) (x : M) :
    (addHomToULiftLinear (iM := iM) (iN := iN) f) x = f x :=
  rfl

theorem exists_sum_addHom_comp_eq {l : ℕ} [Fact l.Prime] {T A : Type*} [AddCommGroup T]
    [AddCommGroup A] [Module (ZMod l) A] [Finite A] (e : ZMod l ≃+ T) :
    ∃ (ι : Type) (_ : Fintype ι) (i : ι → (T →+ A)) (p : ι → (A →+ T)),
      ∀ a : A, ∑ j, i j (p j a) = a := by
  obtain ⟨n, b⟩ : ∃ n : ℕ, Nonempty (Module.Basis (Fin n) (ZMod l) A) := by
    have : Module.Finite (ZMod l) A := Module.Finite.of_finite
    exact ⟨_, ⟨Module.finBasis (ZMod l) A⟩⟩
  obtain ⟨b⟩ := b
  refine ⟨Fin n, inferInstance, fun j => (LinearMap.toSpanSingleton (ZMod l) A (b j)).toAddMonoidHom.comp
    e.symm.toAddMonoidHom, fun j => e.toAddMonoidHom.comp (b.coord j).toAddMonoidHom, fun a => ?_⟩
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, LinearMap.toAddMonoidHom_coe, LinearMap.toSpanSingleton_apply,
    Module.Basis.coord_apply]
  exact b.sum_repr a

end Helpers

section LemmaY

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [ValuativeExtension K Ksep]
  {l : ℕ}

theorem subsingleton_cohomology_of_inertia_open (hlp : l.Prime) (hl : (l : 𝓀[K]) ≠ 0)
    {W V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ W)
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hin : ∀ g : (W : Subgroup Gal(Ksep/K)), ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)),
      valuation Ksep x ≤ 1 → valuation Ksep ((g : Gal(Ksep/K)) x - x) < 1)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l)
    (A : Rep (ULift.{0} ℤ) (W : Subgroup Gal(Ksep/K))) [IsDiscreteRep A] [Finite A]
    (hA : ∀ a : A, l • a = 0)
    (hV : ∀ g : (W : Subgroup Gal(Ksep/K)), (g : Gal(Ksep/K)) ∈ (V : Subgroup Gal(Ksep/K)) →
      ∀ a : A, A.ρ g a = a)
    (hinv : ∀ a : A, (∀ g : (W : Subgroup Gal(Ksep/K)), A.ρ g a = a) → a = 0)
    {n : ℕ} (hn : n ≤ 2) : Subsingleton (cohomology A n) := by
  have hlK := natCast_ne_zero_of_residueField hl
  have : Fact l.Prime := ⟨hlp⟩
  obtain ⟨e⟩ := nonempty_zmod_addEquiv_rootsOfUnity K Ksep hlp hlK
  let : Module (ZMod l) A := AddCommGroup.zmodModule hA
  let T := Rep.res (W : Subgroup Gal(Ksep/K)).subtype (galRootsOfUnity.{0} K Ksep l)
  obtain ⟨ι, _, i, p, hip⟩ := exists_sum_addHom_comp_eq (T := T) (A := A) e
  have hT : ∀ (g : (W : Subgroup Gal(Ksep/K))) (t : T), T.ρ g t = t := fun g t => by
    refine congrArg Additive.ofMul (Subtype.ext (Units.ext ?_))
    exact apply_eq_of_valuation_sub_lt_one hl hμ (hin g) (by
      have h1 := congrArg Units.val ((mem_rootsOfUnity l _).1 (Additive.toMul t).2)
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h1
      convert h1 using 2
      rfl)
  have hbij : Function.Bijective fun a : A =>
      ((openSubgroupOf W V : OpenSubgroup (W : Subgroup Gal(Ksep/K))) :
        Subgroup (W : Subgroup Gal(Ksep/K))).index • a := by
    set m := ((openSubgroupOf W V : OpenSubgroup (W : Subgroup Gal(Ksep/K))) :
        Subgroup (W : Subgroup Gal(Ksep/K))).index
    have hm : m.Coprime l := hind
    set u := ZMod.unitOfCoprime m hm
    have hu : ∀ a : A, m • a = (u : ZMod l) • a := fun a => by
      rw [ZMod.coe_unitOfCoprime, Nat.cast_smul_eq_nsmul]
    refine Function.bijective_iff_has_inverse.2 ⟨fun a => ((u⁻¹ : (ZMod l)ˣ) : ZMod l) • a,
      fun a => ?_, fun a => ?_⟩
    · simp only [hu, smul_smul, Units.inv_mul, one_smul]
    · simp only [hu, smul_smul, Units.mul_inv, one_smul]
  exact subsingleton_cohomology_of_sum (openSubgroupOf W V) hT
    (fun m a => hV m ((Subgroup.mem_subgroupOf).1 m.2) a) hinv hbij
    (fun j => addHomToULiftLinear (i j)) (fun j => addHomToULiftLinear (p j))
    (DFunLike.ext _ _ fun a => by simpa [LinearMap.sum_apply, addHomToULiftLinear_apply] using hip a) n
    (fun g => cohomologyConj_galRootsOfUnity_eq_id h hl hμ hind g (hin g) hn)

theorem subsingleton_cohomology_of_inertia (hlp : l.Prime) (hl : (l : 𝓀[K]) ≠ 0)
    {W V : OpenSubgroup Gal(Ksep/K)} (h : V ≤ W) [(W : Subgroup Gal(Ksep/K)).Normal]
    [((V : Subgroup Gal(Ksep/K)).subgroupOf (W : Subgroup Gal(Ksep/K))).Normal]
    (hμ : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)))
    (hin : ∀ g ∈ (W : Subgroup Gal(Ksep/K)), ∀ x ∈ fixedField (V : Subgroup Gal(Ksep/K)),
      valuation Ksep x ≤ 1 → valuation Ksep (g x - x) < 1)
    (hind : ((V : Subgroup Gal(Ksep/K)).relIndex W).Coprime l)
    (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M] (hM : ∀ m : M, l • m = 0)
    (hV : ∀ g ∈ (V : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m)
    (hW : ∀ m : M, (∀ g ∈ (W : Subgroup Gal(Ksep/K)), M.ρ g m = m) → m = 0)
    {i : ℕ} (hi : i ≤ 2) : Subsingleton (cohomology M i) := by
  refine subsingleton_cohomology_of_normal (W : Subgroup Gal(Ksep/K)) W.isClosed M
    (fun m hm => hW m fun g hg => hm ⟨g, hg⟩) 2 (fun j _ hj => ?_) i hi
  have : Finite (Rep.res (W : Subgroup Gal(Ksep/K)).subtype M) := ‹Finite M›
  exact subsingleton_cohomology_of_inertia_open hlp hl h hμ (fun g => hin g g.2) hind
    (Rep.res (W : Subgroup Gal(Ksep/K)).subtype M) hM (fun g hg m => hV g hg m)
    (fun m hm => hW m fun g hg => hm ⟨g, hg⟩) hj

end LemmaY

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open IntermediateField GroundTheory.LocalField ValuativeRel

section Preimage

variable {K Ksep : Type} [Field K] [Field Ksep] [Algebra K Ksep] [IsGalois K Ksep]
  (V : OpenNormalSubgroup Gal(Ksep/K))

noncomputable abbrev restrictFixed : Gal(Ksep/K) →* Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) :=
  AlgEquiv.restrictNormalHom (fixedField (V : Subgroup Gal(Ksep/K)))

theorem restrictFixed_surjective : Function.Surjective (restrictFixed V) :=
  AlgEquiv.restrictNormalHom_surjective Ksep

theorem restrictFixed_apply (σ : Gal(Ksep/K)) (x : fixedField (V : Subgroup Gal(Ksep/K))) :
    ((restrictFixed V σ x : fixedField (V : Subgroup Gal(Ksep/K))) : Ksep) = σ x :=
  AlgEquiv.restrictNormal_commutes σ _ x

theorem ker_restrictFixed : (restrictFixed V).ker = (V : Subgroup Gal(Ksep/K)) := by
  rw [restrictFixed, IntermediateField.restrictNormalHom_ker,
    fixingSubgroup_fixedField_openNormalSubgroup]

theorem mem_V_iff_restrictFixed_eq_one (σ : Gal(Ksep/K)) :
    σ ∈ (V : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ = 1 := by
  rw [← MonoidHom.mem_ker]
  exact (SetLike.ext_iff.1 (ker_restrictFixed V) σ).symm

noncomputable def preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    OpenSubgroup Gal(Ksep/K) where
  toSubgroup := S.comap (restrictFixed V)
  isOpen' := Subgroup.isOpen_mono (H₁ := (V : Subgroup Gal(Ksep/K))) (fun σ hσ => by
      change restrictFixed V σ ∈ S
      rw [(mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
      exact S.one_mem) V.isOpen'

variable {V}

@[simp]
theorem mem_preimageOpen {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)} {σ : Gal(Ksep/K)} :
    σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)) ↔ restrictFixed V σ ∈ S :=
  Iff.rfl

theorem coe_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (preimageOpen V S : Subgroup Gal(Ksep/K)) = S.comap (restrictFixed V) :=
  rfl

theorem le_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)) ≤ preimageOpen V S := fun σ hσ => by
  rw [mem_preimageOpen, (mem_V_iff_restrictFixed_eq_one V σ).1 hσ]
  exact S.one_mem

theorem preimageOpen_le_preimageOpen {S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (h : S ≤ S') : preimageOpen V S ≤ preimageOpen V S' := fun _ hσ => h hσ

instance preimageOpen_normal (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) [S.Normal] :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).Normal :=
  Subgroup.Normal.comap inferInstance _

theorem preimageOpen_bot :
    ((preimageOpen V ⊥ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = V := by
  ext σ
  rw [coe_preimageOpen, Subgroup.mem_comap, Subgroup.mem_bot, mem_V_iff_restrictFixed_eq_one]

theorem relIndex_preimageOpen (S S' : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).relIndex
      (preimageOpen V S') = S.relIndex S' := by
  rw [coe_preimageOpen, coe_preimageOpen, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (restrictFixed_surjective V)]

theorem relIndex_V_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    (V : Subgroup Gal(Ksep/K)).relIndex (preimageOpen V S) = Nat.card S := by
  have h := relIndex_preimageOpen (V := V) ⊥ S
  rw [preimageOpen_bot, Subgroup.relIndex_bot_left] at h
  exact h

theorem index_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)) :
    ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).index = S.index := by
  rw [coe_preimageOpen]
  exact Subgroup.index_comap_of_surjective S (restrictFixed_surjective V)

noncomputable def quotientPreimageOpenEquiv (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) ≃*
      Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S :=
  (QuotientGroup.quotientMulEquivOfEq (by
      ext σ
      rw [coe_preimageOpen, Subgroup.mem_comap, MonoidHom.mem_ker, MonoidHom.comp_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff])).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' S).comp (restrictFixed V))
      ((QuotientGroup.mk'_surjective S).comp (restrictFixed_surjective V)))

theorem isCyclic_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] [IsCyclic (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S)] :
    IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
  isCyclic_of_surjective (quotientPreimageOpenEquiv S).symm.toMonoidHom
    (quotientPreimageOpenEquiv S).symm.surjective

theorem card_quotient_preimageOpen (S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K))
    [S.Normal] :
    Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) =
      Nat.card (Gal(fixedField (V : Subgroup Gal(Ksep/K))/K) ⧸ S) :=
  Nat.card_congr (quotientPreimageOpenEquiv S).toEquiv

theorem pow_eq_one_mem_fixedField_preimageOpen {n : ℕ}
    (hV : ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ n = 1 → σ ζ = ζ)
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : ∀ ζ : fixedField (V : Subgroup Gal(Ksep/K)), ζ ^ n = 1 → ζ ∈ IntermediateField.fixedField S)
    {ζ : Ksep} (hζ : ζ ^ n = 1) :
    ζ ∈ fixedField ((preimageOpen V S : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) := by
  have hζV : ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) :=
    (mem_fixedField_iff _ _).2 fun σ hσ => hV σ hσ ζ hζ
  set ζ' : fixedField (V : Subgroup Gal(Ksep/K)) := ⟨ζ, hζV⟩
  have hζ' : ζ' ^ n = 1 := Subtype.ext (by simp [ζ', hζ])
  have h := (mem_fixedField_iff _ _).1 (hS ζ' hζ')
  refine (mem_fixedField_iff _ _).2 fun σ hσ => ?_
  have := congrArg (fun y : fixedField (V : Subgroup Gal(Ksep/K)) => (y : Ksep)) (h _ hσ)
  simpa [ζ', restrictFixed_apply] using this

end Preimage

section Inertia

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep] [ValuativeRel Ksep] [TopologicalSpace Ksep]
  [IsValuativeTopology Ksep] [ValuativeExtension K Ksep]
  {V : OpenNormalSubgroup Gal(Ksep/K)}

theorem valuation_sub_lt_one_of_mem_preimageOpen
    {S : Subgroup Gal(fixedField (V : Subgroup Gal(Ksep/K))/K)}
    (hS : S ≤ lowerRamificationGroup K (fixedField (V : Subgroup Gal(Ksep/K))) 0)
    {σ : Gal(Ksep/K)} (hσ : σ ∈ (preimageOpen V S : Subgroup Gal(Ksep/K)))
    {x : Ksep} (hx : x ∈ fixedField (V : Subgroup Gal(Ksep/K))) (hx1 : valuation Ksep x ≤ 1) :
    valuation Ksep (σ x - x) < 1 := by
  have hx'1 : valuation (fixedField (V : Subgroup Gal(Ksep/K))) ⟨x, hx⟩ ≤ 1 :=
    (valuation_le_one_iff_coe _ ⟨x, hx⟩).2 hx1
  have h := hS hσ ⟨⟨x, hx⟩, hx'1⟩
  simp only [zero_add, Int.toNat_one, pow_one] at h
  have h2 := mem_maximalIdeal_integer_iff.1 h
  have h3 := (valuation_lt_one_iff_coe _ _).1 h2
  simpa [restrictFixed_apply] using h3

end Inertia

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Fixed

variable {k G : Type*} [CommRing k] [Group G]

def fixedSubmodule (M : Rep k G) (W : Subgroup G) : Submodule k M where
  carrier := {m | ∀ g ∈ W, M.ρ g m = m}
  add_mem' {a b} ha hb g hg := by
    simp only [Set.mem_ofPred_eq] at ha hb ⊢
    rw [map_add, ha g hg, hb g hg]
  zero_mem' g _ := map_zero _
  smul_mem' c m hm g hg := by
    simp only [Set.mem_ofPred_eq] at hm ⊢
    rw [map_smul, hm g hg]

theorem fixedSubmodule_le_comap (M : Rep k G) (W : Subgroup G) [hW : W.Normal] (g : G) :
    fixedSubmodule M W ≤ (fixedSubmodule M W).comap (M.ρ g) := by
  intro m hm w hw
  have h := hm (g⁻¹ * w * g) (by simpa using hW.conj_mem w hw g⁻¹)
  have e : w * g = g * (g⁻¹ * w * g) := by group
  change M.ρ w (M.ρ g m) = M.ρ g m
  calc M.ρ w (M.ρ g m) = M.ρ (w * g) m := by rw [map_mul]; rfl
    _ = M.ρ (g * (g⁻¹ * w * g)) m := by rw [e]
    _ = M.ρ g (M.ρ (g⁻¹ * w * g) m) := by rw [map_mul]; rfl
    _ = M.ρ g m := by rw [h]

end Fixed

section Simple

attribute [-instance] ULift.module

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerChar_of_forall_eq_bot_or_eq_top (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M] [Nontrivial M] (hM : (Nat.card M : K) ≠ 0)
    (hsimple : ∀ N : Submodule (ULift.{0} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤) :
    eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by

  obtain ⟨l, hlp, hldvd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card (α := M)).ne'
  have := Fact.mk hlp
  have : NeZero l := ⟨hlp.ne_zero⟩
  have hlK : (l : K) ≠ 0 := by
    obtain ⟨c, hc⟩ := hldvd
    intro h
    apply hM
    rw [hc, Nat.cast_mul, h, zero_mul]
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  have hPmul : ∀ m n : ℕ, (m : K) ≠ 0 → (n : K) ≠ 0 → ((m * n : ℕ) : K) ≠ 0 := by
    intro m n hm hn
    rw [Nat.cast_mul]
    exact mul_ne_zero hm hn

  have hMl : ∀ m : M, l • m = 0 := by
    let N : Submodule (ULift.{0} ℤ) M := LinearMap.ker (l • LinearMap.id)
    have hN : ∀ g, N ≤ N.comap (M.ρ g) := fun g m hm => by
      simp only [N, LinearMap.mem_ker, Submodule.mem_comap, LinearMap.smul_apply,
        LinearMap.id_apply] at hm ⊢
      rw [← map_nsmul, hm, map_zero]
    obtain ⟨x, hx⟩ := exists_prime_addOrderOf_dvd_card' l hldvd
    have hxN : x ∈ N := by
      simp only [N, LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
      rw [← hx]
      exact addOrderOf_nsmul_eq_zero x
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [addOrderOf_zero] at hx
      exact hlp.one_lt.ne hx
    rcases hsimple N hN with h | h
    · rw [h] at hxN
      exact absurd ((Submodule.mem_bot _).1 hxN) hx0
    · intro m
      have : m ∈ N := h ▸ Submodule.mem_top
      simpa [N] using this
  obtain ⟨d, hd⟩ := exists_card_eq_prime_pow_of_nsmul hMl
  have hG := hasFiniteCohomology_galois_top K Ksep

  let := algebraicValuativeRel K Ksep
  let := algebraicTopology K Ksep
  have := algebraicTopology_isValuativeTopology K Ksep
  have := algebraicValuativeRel_valuativeExtension K Ksep

  obtain ⟨V, hVM, hVμ⟩ : ∃ V : OpenNormalSubgroup Gal(Ksep/K),
      (∀ g ∈ (V : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m) ∧
        ∀ σ ∈ (V : Subgroup Gal(Ksep/K)), ∀ ζ : Ksep, ζ ^ l = 1 → σ ζ = ζ := by
    have hdisc := (isDiscreteRep_iff_forall_exists_openNormalSubgroup M).1 inferInstance
    choose U hU using hdisc
    obtain ⟨V, hV⟩ := OpenNormalSubgroup.exists_le_of_finite
      (fun o : Option M => o.elim (rootsOfUnityFixingNormal (K := K) (Ksep := Ksep) l) U)
    refine ⟨V, fun g hg m => ?_, fun σ hσ ζ hζ => ?_⟩
    · exact (Representation.mem_invariants _ _).1 (hU m) ⟨g, hV (some m) hg⟩
    · exact apply_eq_of_mem_rootsOfUnityFixing (hV none hσ) hζ
  have hμV : ∀ ζ : Ksep, ζ ^ l = 1 → ζ ∈ fixedField (V : Subgroup Gal(Ksep/K)) := fun ζ hζ =>
    (mem_fixedField_iff _ _).2 fun σ hσ => hVμ σ hσ ζ hζ
  set L : IntermediateField K Ksep := fixedField (V : Subgroup Gal(Ksep/K)) with hL
  by_cases hlq : l = ringChar 𝓀[K]
  ·
    have hlE : ∀ E : IntermediateField K Ksep, (l : E) ≠ 0 := fun E h =>
      hlK ((algebraMap K E).injective (by rw [map_natCast, map_zero]; exact h))

    obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
      (preimageOpen V (lowerRamificationGroup K L 1)) (V : Subgroup Gal(Ksep/K)) hVM (fun g hg => by
        obtain ⟨n, hn⟩ := isPGroup_lowerRamificationGroup_one K L ⟨restrictFixed V g, hg⟩
        refine ⟨n, ?_⟩
        rw [mem_V_iff_restrictFixed_eq_one, map_pow, hlq]
        exact congrArg Subtype.val hn)
    have h1fix : ∀ g ∈ (preimageOpen V (lowerRamificationGroup K L 1) : Subgroup Gal(Ksep/K)),
        ∀ m : M, M.ρ g m = m := by
      have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
        have : m0 ∈ fixedSubmodule M (preimageOpen V (lowerRamificationGroup K L 1)) := hm0fix
        rw [h] at this
        exact (Submodule.mem_bot _).1 this))
      intro g hg m
      have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
      exact this g hg

    obtain ⟨nE, hnE⟩ := exists_card_quotient_eq_pow (E := fixedField (preimageOpen V
      (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : Subgroup Gal(Ksep/K)))
      (p := l) (hlE _)
    have hX := eulerChar_coprime
      (U := preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])))
      (V := preimageOpen V (lowerRamificationGroup K L 1)) hlK
      (preimageOpen_le_preimageOpen (lowerRamificationGroup_one_le_coprimeQuotientPreimage (K := K) (L := L)))
      (by
        rw [relIndex_preimageOpen, hlq]
        exact coprime_card_coprimeQuotientPreimage_quotient_lowerRamificationGroup_one (K := K) (L := L))
      (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
        (fun ζ' hζ' => pow_eq_one_mem_fixedField_lowerRamificationGroup_one (K := K) (L := L)
          (by rw [← hlq]; exact hζ')) hζ)
      (Rep.res ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0)
        (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
      (fun g hg m => h1fix g hg m) hnE

    have : IsCyclic (Gal(L/K) ⧸ coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :=
      isCyclic_quotient_coprimeQuotientPreimage_lowerRamificationGroup (K := K) (L := L)
    have : IsCyclic (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) :=
      isCyclic_quotient_preimageOpen _
    obtain ⟨a, ha⟩ := exists_card_quotient_coprimeQuotientPreimage_lowerRamificationGroup_eq_pow
      (K := K) (L := L)
    have hcard : Nat.card (Gal(Ksep/K) ⧸ ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [card_quotient_preimageOpen, ha, hlq]
    have hC := eulerChar_res_eq_pow (P := fun m => (m : K) ≠ 0) hPdvd hPmul hG _ hcard M hM hMl

    have hfin : Module.finrank K (fixedField ((preimageOpen V (coprimeQuotientPreimage
        (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) : OpenSubgroup Gal(Ksep/K)) :
          Subgroup Gal(Ksep/K))) = l ^ a := by
      rw [← index_openSubgroup, Subgroup.index, hcard]
    obtain ⟨nK, hnK⟩ := exists_card_quotient_eq_pow (E := K) (p := l) hlK
    have hext := card_quotient_span_natCast_finiteExtension (K := K) (L := fixedField
      ((preimageOpen V (coprimeQuotientPreimage (lowerRamificationGroup K L 0) (ringChar 𝓀[K])) :
        OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K))) l
    rw [hnE, hnK, hfin, ← pow_mul] at hext
    have hnE' : nE = nK * l ^ a := Nat.pow_right_injective hlp.two_le hext

    have hpos := eulerChar_pos hG M hM
    have key : eulerChar M ^ (l ^ a) = (((Nat.card M : ℚ) ^ nK)⁻¹) ^ (l ^ a) := by
      rw [← hC, hX, hnE', pow_mul, inv_pow]
    have hχ := (pow_left_inj₀ hpos.le (by positivity) (pow_ne_zero a hlp.ne_zero)).1 key
    rw [hχ, hd, card_quotient_span_natCast_pow hlK, hnK]
    push_cast
    ring
  ·
    have hl𝓀 : (l : 𝓀[K]) ≠ 0 := by
      rw [Ne, ringChar.spec]
      intro h
      exact hlq ((Nat.prime_dvd_prime_iff_eq (CharP.char_is_prime 𝓀[K] _) hlp).1 h).symm
    have hRHS : Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) = 1 :=
      card_quotient_span_natCast_eq_one (by rw [hd, Nat.cast_pow]; exact pow_ne_zero _ hl𝓀)
    rw [hRHS, Nat.cast_one, inv_one]
    have hBle : coprimeRelPreimage (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l ≤
        lowerRamificationGroup K L 0 :=
      coprimeRelPreimage_le _ _ l
    by_cases hB : fixedSubmodule M (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
        (lowerRamificationGroup K L 1) l)) = ⊥
    ·
      have hsub : ∀ i ≤ 2, Subsingleton (cohomology M i) := fun i hi =>
        subsingleton_cohomology_of_inertia hlp hl𝓀 (V := V.toOpenSubgroup) (le_preimageOpen _) hμV
          (fun g hg x hx hx1 => valuation_sub_lt_one_of_mem_preimageOpen hBle hg hx hx1)
          (by
            rw [relIndex_V_preimageOpen]
            exact coprime_card_coprimeRelPreimage_lowerRamificationGroup (K := K) (L := L) hlp hlq)
          M hMl hVM (fun m hm => by
            have : m ∈ fixedSubmodule M (preimageOpen V (coprimeRelPreimage
                (lowerRamificationGroup K L 0) (lowerRamificationGroup K L 1) l)) := hm
            rw [hB] at this
            exact (Submodule.mem_bot _).1 this) hi
      have h0 := hsub 0 (by norm_num)
      have h1 := hsub 1 (by norm_num)
      have h2 := hsub 2 le_rfl
      rw [eulerChar_eq, Nat.card_of_subsingleton (0 : cohomology M 0),
        Nat.card_of_subsingleton (0 : cohomology M 1), Nat.card_of_subsingleton (0 : cohomology M 2)]
      norm_num
    ·
      have hBfix : ∀ g ∈ (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l) : Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left hB
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      obtain ⟨m0, hm0, hm0fix⟩ := exists_ne_zero_forall_mem_eq M hMl
        (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l))
        (preimageOpen V (coprimeRelPreimage (lowerRamificationGroup K L 0)
          (lowerRamificationGroup K L 1) l)) hBfix (fun g hg => by
          obtain ⟨n, hn⟩ := isPGroup_primaryQuotientPreimage_quotient_lowerRamificationGroup
            (K := K) (L := L) hlp (QuotientGroup.mk ⟨restrictFixed V g, hg⟩)
          refine ⟨n, ?_⟩
          rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hn
          rw [mem_preimageOpen, map_pow]
          simpa using hn)
      have hAfix : ∀ g ∈ (preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l) :
          Subgroup Gal(Ksep/K)), ∀ m : M, M.ρ g m = m := by
        have htop := (hsimple _ (fixedSubmodule_le_comap M _)).resolve_left (fun h => hm0 (by
          have : m0 ∈ fixedSubmodule M (preimageOpen V
            (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) := hm0fix
          rw [h] at this
          exact (Submodule.mem_bot _).1 this))
        intro g hg m
        have : m ∈ fixedSubmodule M _ := htop ▸ Submodule.mem_top
        exact this g hg
      have hX := eulerChar_coprime (U := ⊤)
        (V := preimageOpen V (primaryQuotientPreimage (lowerRamificationGroup K L 0) l)) hlK le_top
        (by
          rw [show ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)) = ⊤ from rfl,
            Subgroup.relIndex_top_right, index_preimageOpen]
          exact coprime_card_quotient_primaryQuotientPreimage_lowerRamificationGroup (K := K) (L := L) hlp)
        (fun ζ hζ => pow_eq_one_mem_fixedField_preimageOpen hVμ
          (fun ζ' hζ' => pow_eq_one_mem_fixedField_primaryQuotientPreimage (K := K) (L := L) hlp hlq hζ') hζ)
        (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) hMl
        (fun g hg m => hAfix g hg m) (n := 0)
        (by
          rw [pow_zero]
          exact card_quotient_span_natCast_eq_one (natCast_residueField_fixedField_ne_zero hl𝓀 ⊤))
      have hres : eulerChar (Rep.res ((⊤ : OpenSubgroup Gal(Ksep/K)) : Subgroup Gal(Ksep/K)).subtype M) =
          eulerChar M := by
        simp only [eulerChar]
        refine Finset.prod_congr rfl fun q _ => ?_
        rw [← Nat.card_eq_of_bijective _ (bijective_cohomologyRes_top M q)]
      rw [← hres, hX, pow_zero, inv_one]

end Simple

end GroundTheory.ProfCoh
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory IntermediateField GroundTheory.LocalField ValuativeRel

section Main

attribute [-instance] ULift.module

variable {K Ksep : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]

theorem eulerChar_galois_of_card_eq (n : ℕ) : ∀ (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M]
    [Finite M], Nat.card M = n → (Nat.card M : K) ≠ 0 →
      eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro M _ _ hn hM
  have hPdvd : ∀ m n : ℕ, m ∣ n → (n : K) ≠ 0 → (m : K) ≠ 0 := by
    rintro m n ⟨c, rfl⟩ hn hm
    apply hn
    rw [Nat.cast_mul, hm, zero_mul]
  rcases subsingleton_or_nontrivial M with hsub | hnt
  ·
    have h1 : Nat.card M = 1 := Nat.card_eq_one_iff_unique.2 ⟨hsub, ⟨0⟩⟩
    rw [eulerChar_eq_one_of_subsingleton, h1, Nat.cast_one,
      card_quotient_span_eq_one_of_isUnit isUnit_one, Nat.cast_one, inv_one]
  by_cases hs : ∀ N : Submodule (ULift.{0} ℤ) M, (∀ g, N ≤ N.comap (M.ρ g)) → N = ⊥ ∨ N = ⊤
  · exact eulerChar_of_forall_eq_bot_or_eq_top M hM hs

  push Not at hs
  obtain ⟨N, hN, hbot, htop⟩ := hs
  let i := Rep.subtype M N hN
  have hi : Function.Injective i.hom := Submodule.injective_subtype N
  have hS := cokerShortComplex_shortExact i hi
  have : IsDiscreteRep (cokerShortComplex i).X₁ := isDiscreteRep_subrepresentation M N hN
  have : IsDiscreteRep (cokerShortComplex i).X₂ := inferInstanceAs (IsDiscreteRep M)
  have : Finite (cokerShortComplex i).X₂ := inferInstanceAs (Finite M)
  have : IsDiscreteRep (cokerShortComplex i).X₃ :=
    isDiscreteRep_quotient M (LinearMap.range i.hom.toLinearMap) (range_hom_le_comap i)
  have hG := hasFiniteCohomology_galois_top K Ksep
  have hχ := eulerChar_shortExact hPdvd hG hS hM

  have hrange : LinearMap.range i.hom.toLinearMap = N := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  have hX₁ : Nat.card (cokerShortComplex i).X₁ = Nat.card N := rfl
  have hX₃ : Nat.card (cokerShortComplex i).X₃ = Nat.card (M ⧸ LinearMap.range i.hom.toLinearMap) := rfl
  have hcardM : Nat.card M = Nat.card (cokerShortComplex i).X₁ * Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₁, hX₃, Submodule.card_eq_card_quotient_mul_card (LinearMap.range i.hom.toLinearMap),
      Nat.card_congr (LinearEquiv.ofInjective i.hom.toLinearMap hi).toEquiv.symm]
  have : Finite (cokerShortComplex i).X₁ := Finite.of_injective _ hi
  have : Finite (cokerShortComplex i).X₃ :=
    Finite.of_surjective _ (Submodule.mkQ_surjective (LinearMap.range i.hom.toLinearMap))
  have h1 : 1 < Nat.card (cokerShortComplex i).X₁ := by
    rw [hX₁]
    obtain ⟨x, hxN, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
    have : Nontrivial N := ⟨⟨⟨x, hxN⟩, 0, fun h => hx0 (congrArg Subtype.val h)⟩⟩
    exact Finite.one_lt_card
  have h3 : 1 < Nat.card (cokerShortComplex i).X₃ := by
    rw [hX₃, hrange]
    have : Nontrivial (M ⧸ N) := Submodule.Quotient.nontrivial_iff.2 htop
    have : Finite (M ⧸ N) := Finite.of_surjective _ (Submodule.mkQ_surjective N)
    exact Finite.one_lt_card
  have hpos1 : 0 < Nat.card (cokerShortComplex i).X₁ := by omega
  have hpos3 : 0 < Nat.card (cokerShortComplex i).X₃ := by omega
  have hlt1 : Nat.card (cokerShortComplex i).X₁ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_right hpos1 h3
  have hlt3 : Nat.card (cokerShortComplex i).X₃ < n := by
    rw [← hn, hcardM]
    exact lt_mul_of_one_lt_left hpos3 h1
  have hP1 : (Nat.card (cokerShortComplex i).X₁ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM⟩ hM
  have hP3 : (Nat.card (cokerShortComplex i).X₃ : K) ≠ 0 :=
    hPdvd _ _ ⟨_, hcardM.trans (mul_comm _ _)⟩ hM
  change eulerChar (cokerShortComplex i).X₂ = _
  rw [hχ, ih _ hlt1 _ rfl hP1, ih _ hlt3 _ rfl hP3]
  rw [hcardM, card_quotient_span_natCast_mul hP1 hP3]
  push_cast
  rw [mul_inv]

theorem eulerChar_galois (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    eulerChar M = (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ :=
  eulerChar_galois_of_card_eq _ M rfl hM

theorem card_cohomology_mul_div_eq (M : Rep (ULift.{0} ℤ) Gal(Ksep/K)) [IsDiscreteRep M] [Finite M]
    (hM : (Nat.card M : K) ≠ 0) :
    (Nat.card (cohomology M 0) : ℚ) * Nat.card (cohomology M 2) / Nat.card (cohomology M 1) =
      (Nat.card (𝒪[K] ⧸ Ideal.span {(Nat.card M : 𝒪[K])}) : ℚ)⁻¹ := by
  rw [← eulerChar_eq, eulerChar_galois M hM]

end Main

end GroundTheory.ProfCoh
end
