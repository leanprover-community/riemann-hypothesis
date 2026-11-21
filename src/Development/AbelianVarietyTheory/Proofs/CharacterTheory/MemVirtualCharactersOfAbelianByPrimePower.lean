import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemOfMulMemOfForallPrimeNotDvd
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharacterExtendScalarsRep
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInducedClassFunctionStatement
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InducedClassFunctionFromSubgroupEqFinsumCosets
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharactersStatement

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd : ∀ (X : Type) [Finite X] (S : AddSubgroup (X → ℤ)), (∀ f ∈ S, ∀ g ∈ S, f * g ∈ S) → (∀ (x : X) (p : ℕ), p.Prime → ∃ f ∈ S, ¬ (p : ℤ) ∣ f x) → (1 : X → ℤ) ∈ S := by
  first | exact @GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | exact GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd | (intros; apply GlobalTheory.one_mem_of_mul_mem_of_forall_prime_not_dvd <;> assumption)
end

section
section
namespace GlobalTheory

theorem conj_mem_zpowers_of_mem_of_pRegular {G : Type} [Group G] (c : G) (p : ℕ) (H : Subgroup G)
    (hc : Nat.Coprime (orderOf c) p)
    (hp : ∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) (g : G)
    (hg : g⁻¹ * c * g ∈ H) : g⁻¹ * c * g ∈ Subgroup.zpowers c := by
  obtain ⟨k, hk⟩ := hp _ hg
  have ho : orderOf (g⁻¹ * c * g) = orderOf c := by
    have := (MulAut.conj g⁻¹).orderOf_eq c
    simpa using this
  have hcop : Nat.Coprime (p ^ k) (orderOf (g⁻¹ * c * g)) := by
    rw [ho]
    exact Nat.Coprime.pow_left k hc.symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ hk m

theorem card_fixedBy_quotient_eq_relIndex_of_pRegular :
    ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  intro G _ _ c p H N hc hH hp hN
  have key : ∀ g : G, c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g ∈ N := by
    intro g
    have h1 : c • (g : G ⧸ H) = (g : G ⧸ H) ↔ g⁻¹ * c * g ∈ H := by
      rw [eq_comm, MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, mul_assoc]
    rw [h1]
    constructor
    · intro hg
      have hy := conj_mem_zpowers_of_mem_of_pRegular c p H hc hp g hg
      rw [← N.inv_mem_iff, hN]
      rintro d ⟨n, rfl⟩
      have h2 := Subgroup.zpow_mem _ hy n
      have h3 : (g⁻¹ * c * g) ^ n = g⁻¹ * c ^ n * g⁻¹⁻¹ := by
        rw [← conj_zpow, inv_inv]
      rw [h3] at h2
      exact h2
    · intro hg
      have := (hN _).1 (N.inv_mem hg) c (Subgroup.mem_zpowers c)
      rw [inv_inv] at this
      exact hH this
  let f : N ⧸ H.subgroupOf N → MulAction.fixedBy (G ⧸ H) c :=
    Quotient.lift (fun n : N => ⟨((n : G) : G ⧸ H), (key n).2 n.2⟩) (by
      intro a b hab
      apply Subtype.ext
      have h : a⁻¹ * b ∈ H.subgroupOf N := QuotientGroup.leftRel_apply.1 hab
      exact QuotientGroup.eq.2 (by simpa [Subgroup.mem_subgroupOf] using h))
  have hf : Function.Bijective f := by
    constructor
    · intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      intro hab
      have h : ((a : G) : G ⧸ H) = ((b : G) : G ⧸ H) := congrArg Subtype.val hab
      rw [QuotientGroup.eq] at h ⊢
      simpa [Subgroup.mem_subgroupOf] using h
    · rintro ⟨x, hx⟩
      induction x using QuotientGroup.induction_on with
      | H g => exact ⟨((⟨g, (key g).1 hx⟩ : N) : N ⧸ H.subgroupOf N), rfl⟩
  exact (Nat.card_eq_of_bijective f hf).symm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime : ∀ (G : Type) [Group G] [Finite G] (c : G) (p : ℕ) (H N : Subgroup G), Nat.Coprime (orderOf c) p → Subgroup.zpowers c ≤ H → (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ Subgroup.zpowers c) → (∀ g : G, g ∈ N ↔ ∀ d ∈ Subgroup.zpowers c, g * d * g⁻¹ ∈ Subgroup.zpowers c) → Nat.card (MulAction.fixedBy (G ⧸ H) c) = H.relIndex N := by
  atlas_forward_decl GlobalTheory.card_fixedBy_quotient_eq_relIndex_of_pRegular
end

section
section
namespace GlobalTheory

theorem card_fixedBy_pow_prime_pow_modEq (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X]
    (x : G) (p k : ℕ) (hp : p.Prime) :
    Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype X := Fintype.ofFinite X
  let f : Function.End (MulAction.fixedBy X (x ^ p ^ k)) := fun y => ⟨x • (y : X), by
    have hy : (x ^ p ^ k) • (y : X) = y := y.2
    show (x ^ p ^ k) • x • (y : X) = x • (y : X)
    rw [← mul_smul, ← pow_succ, pow_succ', mul_smul, hy]⟩
  have hf : ∀ (n : ℕ) (y : MulAction.fixedBy X (x ^ p ^ k)), (((f ^ n) y : MulAction.fixedBy X (x ^ p ^ k)) : X) = x ^ n • (y : X) := by
    intro n
    induction n with
    | zero => intro y; rw [pow_zero, pow_zero, one_smul]; rfl
    | succ n ih =>
      intro y
      rw [pow_succ', pow_succ', mul_smul, ← ih y]
      rfl
  have h1 : f ^ p ^ k = 1 := by
    funext y
    apply Subtype.ext
    rw [hf]
    exact y.2
  have h2 := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := k) h1
  have e : (Function.fixedPoints f) ≃ MulAction.fixedBy X x :=
    { toFun := fun y => ⟨(y.1 : X), congrArg Subtype.val y.2⟩
      invFun := fun y => ⟨⟨y.1, MulAction.fixedBy_subset_fixedBy_zpow X x ((p ^ k : ℕ) : ℤ) y.2 |> fun h => by
          rwa [zpow_natCast] at h⟩, Subtype.ext y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  convert h2

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy : ∀ (G : Type) [Group G] (X : Type) [Finite X] [MulAction G X] (x : G) (p k : ℕ), p.Prime → Nat.card (MulAction.fixedBy X (x ^ p ^ k)) ≡ Nat.card (MulAction.fixedBy X x) [MOD p] := by
  atlas_forward_decl GlobalTheory.card_fixedBy_pow_prime_pow_modEq
end

section
section
namespace GlobalTheory

theorem exists_coprime_orderOf_pow_prime_pow (G : Type) [Group G] [Finite G] (x : G) (p : ℕ)
    (hp : p.Prime) : ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  obtain ⟨k, u, hu, h⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.ne_one
  refine ⟨k, ?_⟩
  have h1 : orderOf (x ^ p ^ k) ∣ u := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← pow_mul, ← h, pow_orderOf_eq_one]
  exact Nat.Coprime.coprime_dvd_left h1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hu).symm

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ k : ℕ, Nat.Coprime (orderOf (x ^ p ^ k)) p := by
  atlas_forward_decl GlobalTheory.exists_coprime_orderOf_pow_prime_pow
end

section
section
namespace GlobalTheory

theorem exists_sylow_over_subgroup (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ)
    (hp : p.Prime) :
    ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧
      (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧
      ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  let N : Subgroup G :=
    { carrier := {g | ∀ c ∈ C, g * c * g⁻¹ ∈ C}
      one_mem' := by intro c hc; simpa using hc
      mul_mem' := by
        intro a b ha hb c hc
        have := ha _ (hb c hc)
        simpa [mul_assoc] using this
      inv_mem' := by
        intro a ha c hc
        have key : ∀ n : ℕ, ∀ c ∈ C, a ^ n * c * (a ^ n)⁻¹ ∈ C := by
          intro n
          induction n with
          | zero => intro c hc; simpa using hc
          | succ n ih =>
            intro c hc
            have := ha _ (ih c hc)
            simpa [pow_succ', mul_assoc] using this
        have h1 : a ^ (orderOf a - 1) = a⁻¹ := by
          have hpos : 0 < orderOf a := orderOf_pos a
          apply eq_inv_of_mul_eq_one_left
          rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
        have := key (orderOf a - 1) c hc
        rwa [h1] at this }
  have hN : ∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C := fun g => Iff.rfl
  let C' : Subgroup N := C.subgroupOf N
  haveI hC' : C'.Normal := ⟨fun n hn g => by
    simp only [C', Subgroup.mem_subgroupOf] at hn ⊢
    exact (hN g).1 g.2 _ hn⟩
  let P : Sylow p (N ⧸ C') := Classical.arbitrary _
  let H' : Subgroup N := (P : Subgroup (N ⧸ C')).comap (QuotientGroup.mk' C')
  refine ⟨H'.map N.subtype, ?_, ?_, ?_, ?_⟩
  · intro c hc
    have hcN : c ∈ N := (hN c).2 fun d hd => C.mul_mem (C.mul_mem hc hd) (C.inv_mem hc)
    refine ⟨⟨c, hcN⟩, ?_, rfl⟩
    have : QuotientGroup.mk' C' ⟨c, hcN⟩ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    change QuotientGroup.mk' C' ⟨c, hcN⟩ ∈ (P : Subgroup (N ⧸ C'))
    rw [this]
    exact one_mem _
  · rintro _ ⟨h, -, rfl⟩
    exact (hN h).1 h.2
  · rintro _ ⟨h, hh, rfl⟩
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨QuotientGroup.mk' C' h, hh⟩
    refine ⟨k, ?_⟩
    have h2 : QuotientGroup.mk' C' (h ^ p ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    exact h2
  · intro N' hN'
    obtain rfl : N' = N := by
      ext g
      rw [hN', hN]
    have h1 : (H'.map N.subtype).subgroupOf N = H' :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective H'
    rw [Subgroup.relIndex, h1]
    have h2 : H'.index = (P : Subgroup (N ⧸ C')).index :=
      Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective C')
    rw [h2]
    exact P.not_dvd_index

end GlobalTheory
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex : ∀ (G : Type) [Group G] [Finite G] (C : Subgroup G) (p : ℕ), p.Prime → ∃ H : Subgroup G, C ≤ H ∧ (∀ h ∈ H, ∀ c ∈ C, h * c * h⁻¹ ∈ C) ∧ (∀ h ∈ H, ∃ k : ℕ, h ^ p ^ k ∈ C) ∧ ∀ N : Subgroup G, (∀ g : G, g ∈ N ↔ ∀ c ∈ C, g * c * g⁻¹ ∈ C) → ¬ p ∣ H.relIndex N := by
  atlas_forward_decl GlobalTheory.exists_sylow_over_subgroup
end

section
section
open GlobalTheory.BI
namespace GlobalTheory.BI

theorem exists_abelianByPrimePower_not_dvd_card_fixedBy₂ :
    ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime →
      ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  intro G _ _ x p hp
  obtain ⟨k, hk⟩ := GlobalTheory.T.exists_coprime_orderOf_pow_prime_pow' G x p hp
  obtain ⟨H, hCH, hnorm, hpow, hidx⟩ := GlobalTheory.T.exists_subgroup_ge_normalizing_not_dvd_relIndex G (Subgroup.zpowers (x ^ p ^ k)) p hp
  have hN : ∀ g : G, g ∈ Subgroup.normalizer ((Subgroup.zpowers (x ^ p ^ k) : Subgroup G) : Set G) ↔
      ∀ d ∈ Subgroup.zpowers (x ^ p ^ k), g * d * g⁻¹ ∈ Subgroup.zpowers (x ^ p ^ k) := by
    intro g
    constructor
    · intro hg d hd
      exact (Subgroup.mem_normalizer_iff.1 hg d).1 hd
    · intro h
      exact Subgroup.mem_normalizer_fintype h
  refine ⟨H, ⟨p, hp, (Subgroup.zpowers (x ^ p ^ k)).subgroupOf H, ⟨?_⟩, ?_, ?_⟩, ?_⟩
  · intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hnorm g g.2 n hn
  · intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    obtain ⟨m, hm⟩ := ha
    obtain ⟨n, hn⟩ := hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hm, ← hn]
    exact (Commute.refl _).zpow_zpow m n
  · intro g
    obtain ⟨j, hj⟩ := hpow g g.2
    exact ⟨j, by rw [Subgroup.mem_subgroupOf]; simpa using hj⟩
  · intro hd
    haveI : Finite (G ⧸ H) := inferInstance
    have h1 := GlobalTheory.T.card_fixedBy_quotient_eq_relIndex_normalizer_of_coprime G (x ^ p ^ k) p H _ hk hCH hpow hN
    have h2 := GlobalTheory.T.card_fixedBy_pow_prime_pow_modEq_card_fixedBy G (G ⧸ H) x p k hp
    apply hidx _ hN
    rw [← h1]
    exact (h2.dvd_iff dvd_rfl).2 hd

end GlobalTheory.BI
end

open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy : ∀ (G : Type) [Group G] [Finite G] (x : G) (p : ℕ), p.Prime → ∃ H : Subgroup G, AbByP H ∧ ¬ p ∣ Nat.card (MulAction.fixedBy (G ⧸ H) x) := by
  atlas_forward_decl GlobalTheory.BI.exists_abelianByPrimePower_not_dvd_card_fixedBy₂
end

section
section
open GlobalTheory.BI
noncomputable section
namespace GlobalTheory.BI

theorem out_conj_mem_iff_smul_eq {G : Type} [Group G] (H : Subgroup G) (g : G) (q : G ⧸ H) :
    q.out⁻¹ * g * q.out ∈ H ↔ g • q = q := by
  conv_rhs => rw [← QuotientGroup.out_eq' q]
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, QuotientGroup.eq, ← H.inv_mem_iff]
  simp only [mul_inv_rev, inv_inv, mul_assoc]

theorem ind_restrict_eq_card_fixedBy_mul : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  intro L _ _ G _ _ H χ hχ g
  classical
  have : Fintype (G ⧸ H) := Fintype.ofFinite _
  have hψ : ∀ h x : H, (fun h : H => χ h) (x⁻¹ * h * x) = (fun h : H => χ h) h := by
    intro h x
    simpa using hχ h x
  have hterm : ∀ q : G ⧸ H, ext0 H (fun h : H => χ h) (q.out⁻¹ * g * q.out)
      = (if g • q = q then (1 : L) else 0) * χ g := by
    intro q
    unfold ext0
    by_cases hq : g • q = q
    · have hm := (out_conj_mem_iff_smul_eq H g q).2 hq
      rw [dif_pos hm, if_pos hq, one_mul]
      exact hχ g q.out
    · have hm : q.out⁻¹ * g * q.out ∉ H := fun h => hq ((out_conj_mem_iff_smul_eq H g q).1 h)
      rw [dif_neg hm, if_neg hq, zero_mul]
  rw [ind_eq_finsum_cosets L G H _ hψ g, finsum_eq_sum_of_fintype]
  simp_rw [hterm]
  rw [← Finset.sum_mul, Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  rfl

end GlobalTheory.BI
end
end

open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn : ∀ (L : Type) [Field L] [CharZero L] (G : Type) [Group G] [Finite G] (H : Subgroup G) (χ : G → L), (∀ g x : G, χ (x⁻¹ * g * x) = χ g) → ∀ g : G, ind H (fun h : H => χ h) g = (Nat.card (MulAction.fixedBy (G ⧸ H) g) : L) * χ g := by
  atlas_forward_decl GlobalTheory.BI.ind_restrict_eq_card_fixedBy_mul
end

section
noncomputable section
namespace GlobalTheory.BI

theorem mem_virt_of_forall_abByP (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K]
    [CharZero L] (G : Type) [Group G] [Finite G]
    (hH : ∀ H : Subgroup G, AbByP H → ∀ ψ : H → L, IsChar L L ψ → IsChar K L ψ) :
    ∀ χ : G → L, IsChar L L χ → χ ∈ Virt K L G := by
  let S : AddSubgroup (G → ℤ) :=
    { carrier := {f | ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G}
      zero_mem' := by
        intro χ _
        have : (fun g => (((0 : G → ℤ) g : ℤ) : L) * χ g) = 0 := by
          funext g; simp
        rw [this]; exact zero_mem _
      add_mem' := by
        intro a b ha hb χ hχ
        have : (fun g => (((a + b) g : ℤ) : L) * χ g)
            = (fun g => (a g : L) * χ g) + (fun g => (b g : L) * χ g) := by
          funext g; simp [add_mul]
        rw [this]; exact add_mem (ha χ hχ) (hb χ hχ)
      neg_mem' := by
        intro a ha χ hχ
        have : (fun g => (((-a) g : ℤ) : L) * χ g) = -(fun g => (a g : L) * χ g) := by
          funext g; simp
        rw [this]; exact neg_mem (ha χ hχ) }
  have hS : ∀ f : G → ℤ, f ∈ S ↔
      ∀ χ : G → L, IsChar L L χ → (fun g => (f g : L) * χ g) ∈ Virt K L G := fun _ => Iff.rfl
  have hmul : ∀ f ∈ S, ∀ f' ∈ S, f * f' ∈ S := by
    intro f hf f' hf'
    rw [hS] at hf hf' ⊢
    intro χ hχ
    obtain ⟨a, b, ha, hb, hab⟩ := (GlobalTheory.T.mem_virtualCharacters_iff_sub_characters K L G _).1 (hf' χ hχ)
    have : (fun g => (((f * f') g : ℤ) : L) * χ g)
        = (fun g => (f g : L) * a g) - (fun g => (f g : L) * b g) := by
      funext g
      have h := congrFun hab g
      simp only [Pi.sub_apply] at h
      simp only [Pi.mul_apply, Pi.sub_apply, Int.cast_mul]
      rw [mul_assoc, h, mul_sub]
    rw [this]
    exact sub_mem (hf a (GlobalTheory.BI.isChar_baseChange K L G a ha)) (hf b (GlobalTheory.BI.isChar_baseChange K L G b hb))
  have hperm : ∀ H : Subgroup G, AbByP H →
      (fun g => (Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) ∈ S := by
    intro H hA
    rw [hS]
    intro χ hχ
    obtain ⟨hres, hconj, -⟩ := GlobalTheory.isChar_restrict_conj_one L L G χ hχ
    have h1 : IsChar K L (fun h : H => χ h) := hH H hA _ (hres H H.subtype)
    have h2 := GlobalTheory.T.isCharacterOverSubfield_inducedClassFunction K L G H _ h1
    have : (fun g => (((Nat.card (MulAction.fixedBy (G ⧸ H) g) : ℤ)) : L) * χ g)
        = ind H (fun h : H => χ h) := by
      funext g
      rw [GlobalTheory.T.ind_restrict_eq_card_fixedBy_mul_of_classFn L G H χ hconj g, Int.cast_natCast]
    rw [this]
    exact AddSubgroup.subset_closure h2
  have hone : (1 : G → ℤ) ∈ S := by
    refine GlobalTheory.T.one_mem_of_mul_mem_of_forall_prime_exists_not_dvd G S hmul fun x p hp => ?_
    obtain ⟨H, hA, hp'⟩ := GlobalTheory.T.exists_abelianByPrimePower_not_dvd_card_fixedBy G x p hp
    exact ⟨_, hperm H hA, fun h => hp' (Int.natCast_dvd_natCast.1 h)⟩
  intro χ hχ
  simpa using (hS 1).1 hone χ hχ

end GlobalTheory.BI
end
end
