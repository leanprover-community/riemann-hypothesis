import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import BuildAid.ForwardExisting

section
section
open NumberField

namespace GlobalTheory

theorem nsmul_surjective_torsion_lift (M : Type) [AddCommGroup M] (N e : ℕ) (hN : 1 ≤ N)
    (h : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ e)
    (j : ℕ) (y : M) (hy : (N ^ j) • y = 0) :
    ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  let A : ℕ → AddSubgroup M := fun k => (DistribMulAction.toAddMonoidHom M (N ^ k)).ker
  have hA : ∀ k x, x ∈ A k ↔ (N ^ k) • x = 0 := fun k x => by
    simp [A, AddMonoidHom.mem_ker]
  have hcard : ∀ k, Nat.card (A k) = (N ^ k) ^ e := fun k => by
    rw [← h k]; exact Nat.card_congr (Equiv.subtypeEquivRight (hA k))
  have hpos : ∀ k, 0 < (N ^ k) ^ e := fun k => by positivity
  have hfin : ∀ k, Finite (A k) := fun k =>
    Nat.finite_of_card_ne_zero (by rw [hcard k]; exact (hpos k).ne')
  let ψ : A (j + 1) →+ M := (DistribMulAction.toAddMonoidHom M N).comp (A (j + 1)).subtype
  have hψ : ∀ z : A (j + 1), ψ z = N • (z : M) := fun z => rfl
  have hN1 : ∀ x : M, x ∈ A 1 ↔ N • x = 0 := fun x => by rw [hA 1 x, pow_one]
  have hker : Nat.card ψ.ker = Nat.card (A 1) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun z => ⟨(z.1 : M), (hN1 _).2 (by rw [← hψ]; exact AddMonoidHom.mem_ker.1 z.2)⟩
        invFun := fun z => ⟨⟨(z : M), (hA (j+1) _).2 (by
            rw [pow_succ, mul_smul, (hN1 _).1 z.2, smul_zero])⟩,
            AddMonoidHom.mem_ker.2 (by rw [hψ]; exact (hN1 _).1 z.2)⟩
        left_inv := fun z => rfl
        right_inv := fun z => rfl }
  have hle : ψ.range ≤ A j := by
    rintro _ ⟨z, rfl⟩
    rw [hA, hψ, ← mul_smul, ← pow_succ]
    exact (hA (j+1) _).1 z.2
  have hmul := AddSubgroup.card_mul_index ψ.ker
  rw [AddSubgroup.index_ker] at hmul
  have hrange : Nat.card (Set.range ψ) = Nat.card (A j) := by
    have e1 : (N ^ (j + 1)) ^ e = (N ^ 1) ^ e * (N ^ j) ^ e := by
      rw [← mul_pow, ← pow_add, add_comm]
    rw [hker, hcard, hcard, e1] at hmul
    rw [hcard]
    exact Nat.eq_of_mul_eq_mul_left (hpos 1) hmul
  have heq : ψ.range = A j := by
    refine AddSubgroup.eq_of_le_of_card_ge hle ?_
    rw [← hrange]
    exact le_of_eq (Nat.card_congr (Equiv.setCongr (AddMonoidHom.coe_range ψ)).symm)
  have hyr : y ∈ ψ.range := by rw [heq]; exact (hA j y).2 hy
  obtain ⟨z, hz⟩ := hyr
  exact ⟨z, (hA (j+1) _).1 z.2, hz⟩

theorem nsmul_surj_of_card_torsion :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  intro F _ _ M _ _ N hN h j y hy
  exact nsmul_surjective_torsion_lift M N _ hN h j y hy

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_lift_number_field_module : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F)) →
    ∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y := by
  atlas_forward_decl GlobalTheory.nsmul_surj_of_card_torsion
end

section
section
open NumberField

namespace GlobalTheory

def killedBy {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M] (I : Ideal R) :
    AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun hx hy a ha => by rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun hx a ha => by rw [smul_neg, hx a ha, neg_zero]

theorem killedBy_anti {R : Type} [CommRing R] (M : Type) [AddCommGroup M] [Module R M]
    {I J : Ideal R} (h : I ≤ J) : killedBy M J ≤ killedBy M I :=
  fun _ hx a ha => hx a (h ha)

theorem card_eq_card_ker_mul_card_range {G H : Type} [AddCommGroup G] [AddCommGroup H]
    (f : G →+ H) : Nat.card G = Nat.card f.ker * Nat.card f.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem card_torsion_pow_log_concave : ∀ (F : Type) [Field F] [NumberField F] (M : Type)
    [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  intro F _ _ M _ _ 𝔭 hmax k hfin
  have hp0 : 𝔭 ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hmax (RingOfIntegers.not_isField F)
  have hp2 : 𝔭 ^ 2 ≠ ⊥ := pow_ne_zero 2 hp0
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq (Ideal.pow_le_self two_ne_zero : 𝔭 ^ 2 ≤ 𝔭) hp2
  have haP : a ∈ 𝔭 := ha ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  have key : 𝔭 ^ (k + 2) ⊔ 𝔭 ^ k * Ideal.span {a} = 𝔭 ^ (k + 1) := by
    have e : 𝔭 ^ (k + 1) = 𝔭 ^ k * (𝔭 ^ 2 ⊔ Ideal.span {a}) := by rw [ha, pow_succ]
    rw [e, Ideal.mul_sup, ← pow_add]
  set A := killedBy M (𝔭 ^ (k + 2)) with hA
  set B := killedBy M (𝔭 ^ (k + 1)) with hB
  set C := killedBy M (𝔭 ^ k) with hC
  have eA : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} = Nat.card A := rfl
  have eB : Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} = Nat.card B := rfl
  have eC : Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} = Nat.card C := rfl
  rw [eA, eB, eC]
  have hBA : B ≤ A := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  have hCB : C ≤ B := killedBy_anti M (Ideal.pow_le_pow_right (by omega))
  haveI : Finite A := hfin
  haveI : Finite B := Finite.of_injective _ (AddSubgroup.inclusion_injective hBA)

  have hAB : ∀ x ∈ A, a • x ∈ B := by
    intro x hx b hb
    rw [← mul_smul]
    apply hx
    rw [pow_succ]
    exact Ideal.mul_mem_mul hb haP

  have hiff : ∀ x ∈ A, (a • x ∈ C ↔ x ∈ B) := by
    intro x hx
    constructor
    · intro hax
      have hle : 𝔭 ^ (k + 1) ≤ LinearMap.ker (LinearMap.toSpanSingleton (𝓞 F) M x) := by
        rw [← key]
        apply sup_le
        · intro b hb
          simpa using hx b hb
        · rw [Ideal.mul_le]
          intro r hr s hs
          obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hs
          simp only [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
          rw [← mul_assoc, mul_smul]
          exact hax _ (Ideal.mul_mem_right c _ hr)
      intro b hb
      simpa using hle hb
    · intro hxB b hb
      rw [← mul_smul]
      apply hxB
      rw [pow_succ]
      exact Ideal.mul_mem_mul hb haP
  let π : M →+ M ⧸ C := QuotientAddGroup.mk' C
  let g : A →+ M ⧸ C := (π.comp (DistribMulAction.toAddMonoidHom M a)).comp A.subtype
  let h : B →+ M ⧸ C := π.comp B.subtype
  have hg : Nat.card g.ker = Nat.card B := by
    have : g.ker = B.addSubgroupOf A := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, g, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype, DistribMulAction.toAddMonoidHom_apply,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
      exact hiff x.1 x.2
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hBA).toEquiv
  have hh : Nat.card h.ker = Nat.card C := by
    have : h.ker = C.addSubgroupOf B := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, h, π,
        AddMonoidHom.comp_apply, AddSubgroup.coe_subtype,
        QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
    rw [this]
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hCB).toEquiv
  have hrange : g.range ≤ h.range := by
    rintro _ ⟨x, rfl⟩
    exact ⟨⟨a • (x : M), hAB x.1 x.2⟩, rfl⟩
  haveI : Finite h.range := Finite.of_surjective _ h.rangeRestrict_surjective
  have hcard : Nat.card g.range ≤ Nat.card h.range :=
    Nat.card_le_card_of_injective _ (AddSubgroup.inclusion_injective hrange)
  have e1 := card_eq_card_ker_mul_card_range g
  have e2 := card_eq_card_ker_mul_card_range h
  rw [hg] at e1
  rw [hh] at e2
  rw [e1, sq]
  nth_rewrite 3 [e2]
  calc Nat.card B * Nat.card g.range * Nat.card C
      ≤ Nat.card B * Nat.card h.range * Nat.card C := by gcongr
    _ = Nat.card B * (Nat.card C * Nat.card h.range) := by ring

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_count_log_concave_prime_powers : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (𝔭 : Ideal (𝓞 F)), 𝔭.IsMaximal → ∀ k : ℕ,
    Finite {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} →
    Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 2), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ k, a • x = 0} ≤
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (k + 1), a • x = 0} ^ 2 := by
  atlas_forward_decl GlobalTheory.card_torsion_pow_log_concave
end

section
section
open NumberField

namespace GlobalTheory.PrimaryTorsionBlocks

variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]

def killedBy (I : Ideal R) : AddSubgroup M where
  carrier := {x | ∀ a ∈ I, a • x = 0}
  zero_mem' := fun a _ => smul_zero a
  add_mem' := fun {x y} hx hy a ha => by
    show a • (x + y) = 0
    rw [smul_add, hx a ha, hy a ha, add_zero]
  neg_mem' := fun {x} hx a ha => by
    show a • (-x) = 0
    rw [smul_neg, hx a ha, neg_zero]

def annOf (x : M) : Ideal R := LinearMap.ker (LinearMap.toSpanSingleton R M x)

lemma mem_annOf {x : M} {a : R} : a ∈ annOf x ↔ a • x = 0 := by
  simp [annOf]

lemma mem_killedBy_iff {I : Ideal R} {x : M} : x ∈ killedBy (M := M) I ↔ I ≤ annOf x :=
  ⟨fun h a ha => mem_annOf.2 (h a ha), fun h a ha => mem_annOf.1 (h ha)⟩

theorem card_killedBy_block (P J : Ideal R) (n : R) (e : ℕ)
    (hspan : Ideal.span {n} = P ^ e * J) (hcop : P ⊔ J = ⊤)
    (hlift : ∀ j : ℕ, ∀ y : M, n ^ j • y = 0 → ∃ z : M, n ^ (j + 1) • z = 0 ∧ n • z = y)
    (j : ℕ) :
    Nat.card (killedBy (M := M) (P ^ (e * (j + 1)))) =
      Nat.card (killedBy (M := M) (P ^ (e * j))) * Nat.card (killedBy (M := M) (P ^ e)) := by
  have hpow : ∀ k : ℕ, Ideal.span {n ^ k} = P ^ (e * k) * J ^ k := by
    intro k
    rw [← Ideal.span_singleton_pow, hspan, mul_pow, pow_mul]
  have hcop' : ∀ a b : ℕ, P ^ a ⊔ J ^ b = ⊤ := by
    intro a b
    exact Ideal.isCoprime_iff_sup_eq.1 ((Ideal.isCoprime_iff_sup_eq.2 hcop).pow)
  have hnmem : ∀ k : ℕ, n ^ k ∈ P ^ (e * k) := by
    intro k
    have : n ^ k ∈ Ideal.span {n ^ k} := Ideal.mem_span_singleton_self _
    rw [hpow k] at this
    exact (Ideal.mul_le_left : P ^ (e * k) * J ^ k ≤ P ^ (e * k)) this
  have hn : n ∈ P ^ e := by simpa using hnmem 1
  have hexp : e * (j + 1) = e * j + e := by ring
  have hle1 : P ^ (e * (j + 1)) ≤ P ^ (e * j) := Ideal.pow_le_pow_right (by rw [hexp]; omega)
  have hle2 : P ^ (e * (j + 1)) ≤ P ^ e := Ideal.pow_le_pow_right (by rw [hexp]; omega)

  let f : killedBy (M := M) (P ^ (e * (j + 1))) →+ killedBy (M := M) (P ^ (e * j)) :=
    AddMonoidHom.mk' (fun x => ⟨n • (x : M), fun a ha => by
      rw [smul_smul]
      apply x.2
      rw [hexp, pow_add]
      exact Ideal.mul_mem_mul ha hn⟩)
      (fun x y => by ext; simp [smul_add])
  have hsurj : Function.Surjective f := by
    rintro ⟨y, hy⟩
    have hy0 : n ^ j • y = 0 := hy _ (hnmem j)
    obtain ⟨z, hz, hzy⟩ := hlift j y hy0
    have h1 : (1 : R) ∈ P ^ (e * (j + 1)) ⊔ J ^ (j + 1) := by rw [hcop']; trivial
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.1 h1
    refine ⟨⟨t • z, fun a ha => ?_⟩, ?_⟩
    · rw [smul_smul]
      have hat : a * t ∈ Ideal.span {n ^ (j + 1)} := by
        rw [hpow]
        exact Ideal.mul_mem_mul ha ht
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 hat
      rw [← hc, mul_smul, hz, smul_zero]
    · ext
      show n • t • z = y
      rw [smul_comm, hzy]
      have hsy : s • y = 0 := hy s (hle1 hs)
      calc t • y = s • y + t • y := by rw [hsy, zero_add]
        _ = (s + t) • y := (add_smul s t y).symm
        _ = y := by rw [hst, one_smul]
  have hsup : P ^ e ≤ P ^ (e * (j + 1)) ⊔ Ideal.span {n} := by
    have hc : P ^ (e * j) ⊔ J = ⊤ := by simpa using hcop' (e * j) 1
    have : P ^ e = P ^ e * (P ^ (e * j) ⊔ J) := by rw [hc, Ideal.mul_top]
    rw [this, Ideal.mul_sup, hspan, ← pow_add, hexp, add_comm (e * j) e]
  have hker : Nat.card f.ker = Nat.card (killedBy (M := M) (P ^ e)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x.1 : M), ?_⟩
        invFun := fun x => ⟨⟨(x : M), fun a ha => x.2 a (hle2 ha)⟩, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }
    · have hx1 := mem_killedBy_iff.1 x.1.2
      have hx2 : n • (x.1 : M) = 0 := by
        have := x.2
        rw [AddMonoidHom.mem_ker] at this
        exact congrArg Subtype.val this
      refine mem_killedBy_iff.2 (le_trans hsup (sup_le hx1 ?_))
      rw [Ideal.span_singleton_le_iff_mem]
      exact mem_annOf.2 hx2
    · rw [AddMonoidHom.mem_ker]
      ext
      exact x.2 n hn
  have hmul := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup f.ker
  rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv, hker] at hmul
  exact hmul

end GlobalTheory.PrimaryTorsionBlocks

namespace GlobalTheory

open GlobalTheory.PrimaryTorsionBlocks in

theorem card_primaryTorsion_mul_blocks :
    ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  classical
  intro F _ _ M _ _ N hN _ hlift 𝔭 h𝔭 hN𝔭
  have hne : (N : 𝓞 F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hI : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by
    rwa [Ne, Ideal.span_singleton_eq_bot]
  obtain ⟨Q, hPQ, hspan⟩ := Ideal.eq_prime_pow_mul_coprime hI 𝔭
  refine ⟨Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors (Ideal.span {(N : 𝓞 F)})),
    ?_, fun j => ?_⟩
  · by_contra h0
    have h0' : Multiset.count 𝔭 (UniqueFactorizationMonoid.normalizedFactors
        (Ideal.span {(N : 𝓞 F)})) = 0 := by omega
    rw [h0', pow_zero, one_mul] at hspan
    have hQ : Q ≤ 𝔭 := by rw [← hspan, Ideal.span_singleton_le_iff_mem]; exact hN𝔭
    rw [sup_eq_left.2 hQ] at hPQ
    exact h𝔭.ne_top hPQ
  · have hlift' : ∀ j : ℕ, ∀ y : M, (N : 𝓞 F) ^ j • y = 0 →
        ∃ z : M, (N : 𝓞 F) ^ (j + 1) • z = 0 ∧ (N : 𝓞 F) • z = y := by
      intro j y hy
      rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hy
      obtain ⟨z, h1, h2⟩ := hlift j y hy
      refine ⟨z, ?_, ?_⟩
      · rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]; exact h1
      · rw [Nat.cast_smul_eq_nsmul]; exact h2
    exact card_killedBy_block 𝔭 Q (N : 𝓞 F) _ hspan hPQ hlift' j

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_count_multiplicative_prime_powers : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    (∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0}) →
    (∀ j : ℕ, ∀ y : M, (N ^ j) • y = 0 → ∃ z : M, (N ^ (j + 1)) • z = 0 ∧ N • z = y) →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    ∃ e : ℕ, 1 ≤ e ∧ ∀ j : ℕ, Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * (j + 1)), a • x = 0} =
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ (e * j), a • x = 0} * Nat.card {x : M // ∀ a ∈ 𝔭 ^ e, a • x = 0} := by
  atlas_forward_decl GlobalTheory.card_primaryTorsion_mul_blocks
end

section
section
open NumberField

namespace GlobalTheory

theorem nat_le_of_forall_pow_le_mul_pow (x y C : ℕ) (h : ∀ j, x ^ j ≤ C * y ^ j) : x ≤ y := by
  by_contra hlt
  push_neg at hlt
  rcases Nat.eq_zero_or_pos y with hy | hy
  · subst hy
    have := h 1
    simp at this
    omega
  · have hyR : (0:ℝ) < y := by exact_mod_cast hy
    have hq : (1:ℝ) < (x:ℝ) / y := by
      rw [one_lt_div hyR]; exact_mod_cast hlt
    obtain ⟨j, hj⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (C:ℝ)).exists
    have h1 : ((x:ℝ))^j ≤ C * (y:ℝ)^j := by exact_mod_cast h j
    rw [div_pow, lt_div_iff₀ (pow_pos hyR j)] at hj
    linarith

theorem first_term_le_of_logConcave_blocks :
    ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  intro g e C B he h0 hpos hlc hblk hgr
  set r : ℕ → ℝ := fun k => (g (k+1) : ℝ) / g k with hr
  have gpos : ∀ n, (0:ℝ) < g n := fun n => by exact_mod_cast hpos n
  have rpos : ∀ k, 0 < r k := fun k => div_pos (gpos _) (gpos _)
  have rstep : ∀ k, r (k+1) ≤ r k := by
    intro k
    simp only [hr]
    rw [div_le_div_iff₀ (gpos _) (gpos _)]
    have h1 : ((g (k+2) : ℝ)) * g k ≤ (g (k+1):ℝ)^2 := by exact_mod_cast hlc k
    have h2 : k + 1 + 1 = k + 2 := by ring
    rw [h2]; nlinarith [h1]
  have ranti : Antitone r := antitone_nat_of_succ_le rstep
  have gmul : ∀ a n, (g (a + n) : ℝ) = g a * ∏ i ∈ Finset.range n, r (a + i) := by
    intro a n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.prod_range_succ, ← mul_assoc, ← ih]
      simp only [hr]
      rw [← add_assoc]
      field_simp [(gpos (a+n)).ne']
  have g0 : (g 0 : ℝ) = 1 := by exact_mod_cast h0
  have ge : (g e : ℝ) = ∏ i ∈ Finset.range e, r i := by
    have := gmul 0 e; simpa [g0] using this
  have g2e : (g (e + e) : ℝ) = g e * g e := by
    have := hblk 1
    have h2 : e * (1+1) = e + e := by ring
    rw [h2, mul_one] at this
    exact_mod_cast this
  have hprodeq : ∏ i ∈ Finset.range e, r (e + i) = ∏ i ∈ Finset.range e, r i := by
    have := gmul e e
    rw [g2e] at this
    have hne : (g e : ℝ) ≠ 0 := (gpos e).ne'
    rw [← ge]
    exact (mul_left_cancel₀ hne this).symm
  have hre : r e = r 0 := by
    apply le_antisymm (ranti (Nat.zero_le e))
    by_contra hlt
    push_neg at hlt
    have : ∏ i ∈ Finset.range e, r (e + i) < ∏ i ∈ Finset.range e, r i := by
      apply Finset.prod_lt_prod
      · intro i _; exact rpos _
      · intro i _; exact ranti (by omega)
      · exact ⟨0, Finset.mem_range.2 (by omega), by simpa using hlt⟩
    rw [hprodeq] at this
    exact lt_irrefl _ this
  have hconst : ∀ i ∈ Finset.range e, r i = r 0 := by
    intro i hi
    have hi' := Finset.mem_range.1 hi
    apply le_antisymm (ranti (Nat.zero_le i))
    rw [← hre]; exact ranti (by omega)
  have r0 : r 0 = g 1 := by simp [hr, g0]
  have geR : (g e : ℝ) = (g 1 : ℝ) ^ e := by
    rw [ge, Finset.prod_congr rfl hconst, Finset.prod_const, Finset.card_range, r0]
  have geN : g e = g 1 ^ e := by exact_mod_cast geR
  have gej : ∀ j, g (e * j) = (g 1 ^ e) ^ j := by
    intro j
    induction j with
    | zero => simp [h0]
    | succ j ih => rw [hblk, ih, geN, pow_succ]
  have hpow : g 1 ^ e ≤ B ^ e := by
    apply nat_le_of_forall_pow_le_mul_pow _ _ C
    intro j
    rw [← gej, ← pow_mul]
    exact hgr _
  exact (pow_le_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by omega : e ≠ 0)).1 hpow

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_concave_multiplicative_growth_bound : ∀ (g : ℕ → ℕ) (e C B : ℕ), 1 ≤ e → g 0 = 1 → (∀ n, 0 < g n) →
    (∀ k, g (k + 2) * g k ≤ g (k + 1) ^ 2) → (∀ j, g (e * (j + 1)) = g (e * j) * g e) →
    (∀ n, g n ≤ C * B ^ n) → g 1 ≤ B := by
  atlas_forward_decl GlobalTheory.first_term_le_of_logConcave_blocks
end

section
section
open NumberField

namespace GlobalTheory

open scoped Pointwise

theorem torsionBy_two_generators_mod_prime :
  ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  intro F _ _ M _ _ N hN hfin 𝔭 h𝔭 hN𝔭 hcard
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hT
  have memT : ∀ x : M, x ∈ T ↔ N • x = 0 := by
    intro x; rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  haveI : Finite T := by
    refine Finite.of_injective (fun y : T => (⟨y.1, (memT y.1).1 y.2⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hNR : (N : 𝓞 F) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  have hspan0 : Ideal.span {(N : 𝓞 F)} ≠ ⊥ := by simpa [Ideal.span_singleton_eq_bot] using hNR
  have h𝔭0 : 𝔭 ≠ ⊥ := fun h => hNR (by simpa [h] using hN𝔭)
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_sup_span_eq
    ((Ideal.span_singleton_le_iff_mem _).2 hN𝔭) hspan0
  let φ : T →ₗ[𝓞 F] T := a • LinearMap.id
  have hNT : ∀ y : T, (N : 𝓞 F) • y = 0 := fun y => Subtype.ext ((Submodule.mem_torsionBy_iff _ _).1 y.2)
  have hsmul : 𝔭 • (⊤ : Submodule (𝓞 F) T) = LinearMap.range φ := by
    rw [← ha, Submodule.sup_smul, Submodule.ideal_span_singleton_smul,
      Submodule.ideal_span_singleton_smul]
    ext y
    simp only [Submodule.mem_sup, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and, LinearMap.mem_range]
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, _, ⟨w, rfl⟩, rfl⟩
      exact ⟨w, by simp [φ, hNT]⟩
    · rintro ⟨w, rfl⟩
      exact ⟨0, ⟨0, by simp⟩, _, ⟨w, rfl⟩, by simp [φ]⟩

  let P := {x : M // ∀ b ∈ 𝔭, b • x = 0}
  haveI : Finite P := by
    refine Finite.of_injective (fun y : P => (⟨y.1, by
      rw [← Nat.cast_smul_eq_nsmul (𝓞 F)]; exact y.2 _ hN𝔭⟩ : {x : M // N • x = 0})) ?_
    intro y z h
    have h' := congrArg (fun w : {x : M // N • x = 0} => w.1) h
    exact Subtype.ext h'
  have hker : Nat.card (LinearMap.ker φ) ≤ Nat.card P := by
    refine Nat.card_le_card_of_injective (fun y : LinearMap.ker φ => (⟨y.1.1, by
      intro b hb
      rw [← ha] at hb
      obtain ⟨b1, hb1, b2, hb2, rfl⟩ := Submodule.mem_sup.1 hb
      obtain ⟨c1, rfl⟩ := Ideal.mem_span_singleton'.1 hb1
      obtain ⟨c2, rfl⟩ := Ideal.mem_span_singleton'.1 hb2
      have e1 : (N : 𝓞 F) • y.1.1 = 0 := congrArg Subtype.val (hNT y.1)
      have e2 : a • y.1.1 = 0 := by
        have := y.2
        rw [LinearMap.mem_ker] at this
        exact congrArg Subtype.val this
      rw [add_smul, mul_smul, mul_smul, e1, e2, smul_zero, smul_zero, add_zero]⟩ : P)) ?_
    intro y z h
    have h' := congrArg (fun w : P => w.1) h
    exact Subtype.ext (Subtype.ext h')
  have hQ : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) = Nat.card (LinearMap.ker φ) := by
    rw [hsmul]
    have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range φ)
    have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker φ)
    have h3 : Nat.card (T ⧸ LinearMap.ker φ) = Nat.card (LinearMap.range φ) :=
      Nat.card_congr φ.quotKerEquivRange.toEquiv
    have h4 : 0 < Nat.card (LinearMap.range φ) := Nat.card_pos
    rw [h3] at h2
    rw [h1, mul_comm (Nat.card (LinearMap.range φ))] at h2
    exact Nat.eq_of_mul_eq_mul_right h4 h2

  haveI : Finite (𝓞 F ⧸ 𝔭) := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 h𝔭0
  letI : Field (𝓞 F ⧸ 𝔭) := Ideal.Quotient.field 𝔭
  haveI : Finite (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  haveI : Module.Finite (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) := Module.Finite.of_finite
  have hk : 1 < Nat.card (𝓞 F ⧸ 𝔭) := Finite.one_lt_card
  have hnorm : Ideal.absNorm 𝔭 = Nat.card (𝓞 F ⧸ 𝔭) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hdim : Module.finrank (𝓞 F ⧸ 𝔭) (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ 2 := by
    have h5 := Module.natCard_eq_pow_finrank (K := 𝓞 F ⧸ 𝔭) (V := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T))
    have h6 : Nat.card (T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T)) ≤ Nat.card (𝓞 F ⧸ 𝔭) ^ 2 := by
      rw [hQ, ← hnorm]; exact hker.trans hcard
    rw [h5] at h6
    exact (Nat.pow_le_pow_iff_right hk).1 h6

  set Q := T ⧸ 𝔭 • (⊤ : Submodule (𝓞 F) T) with hQdef
  set r := Module.finrank (𝓞 F ⧸ 𝔭) Q with hr
  let bs := Module.finBasis (𝓞 F ⧸ 𝔭) Q
  let u' : Q := if h : 0 < r then bs ⟨0, h⟩ else 0
  let v' : Q := if h : 1 < r then bs ⟨1, h⟩ else 0
  have hspan : ∀ q : Q, ∃ c d : 𝓞 F ⧸ 𝔭, c • u' + d • v' = q := by
    intro q
    have hle : Set.range bs ⊆ ({u', v'} : Set Q) := by
      rintro _ ⟨i, rfl⟩
      have hi : i.val = 0 ∨ i.val = 1 := by have := i.2; omega
      rcases hi with hi | hi
      · left
        have h0 : 0 < r := by have := i.2; omega
        simp only [u', dif_pos h0]
        congr 1; exact Fin.ext hi
      · right
        have h1 : 1 < r := by have := i.2; omega
        simp only [v', dif_pos h1]
        simp only [Set.mem_singleton_iff]
        congr 1; exact Fin.ext hi
    have hq : q ∈ Submodule.span (𝓞 F ⧸ 𝔭) (Set.range bs) := by
      rw [bs.span_eq]; exact Submodule.mem_top
    have hq2 := Submodule.span_mono hle hq
    exact Submodule.mem_span_pair.1 hq2
  obtain ⟨u0, hu0⟩ := Submodule.Quotient.mk_surjective _ u'
  obtain ⟨v0, hv0⟩ := Submodule.Quotient.mk_surjective _ v'
  refine ⟨u0.1, v0.1, (memT _).1 u0.2, (memT _).1 v0.2, ?_⟩
  intro x hx
  let y : T := ⟨x, (memT x).2 hx⟩
  obtain ⟨c, d, hcd⟩ := hspan (Submodule.Quotient.mk y)
  obtain ⟨c0, rfl⟩ := Ideal.Quotient.mk_surjective c
  obtain ⟨d0, rfl⟩ := Ideal.Quotient.mk_surjective d
  refine ⟨c0, d0, ?_⟩
  rw [← hu0, ← hv0, Module.Quotient.mk_smul_mk, Module.Quotient.mk_smul_mk,
    ← Submodule.Quotient.mk_add, eq_comm, Submodule.Quotient.eq] at hcd
  have hmap := Submodule.mem_map_of_mem (f := T.subtype) hcd
  rw [Submodule.map_smul'', Submodule.map_subtype_top] at hmap
  convert hmap using 1
  simp [y, sub_sub]

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_two_generators_mod_prime : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
    Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 →
    ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
      x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) := by
  atlas_forward_decl GlobalTheory.torsionBy_two_generators_mod_prime
end

section
section
open NumberField

namespace GlobalTheory

theorem torsion_gens_glue_of_local (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M]
    [Module (𝓞 F) M] (N : ℕ) (hN : 1 ≤ N) (hfin : Finite {x : M // N • x = 0})
    (H : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  classical
  set T := Submodule.torsionBy (𝓞 F) M (N : 𝓞 F) with hTdef
  have hT : ∀ x, x ∈ T ↔ N • x = 0 := fun x => by
    rw [hTdef, Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
  set J : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hJdef
  have hJ : J ≠ ⊥ := by
    rw [hJdef, Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]; omega
  haveI : Finite (𝓞 F ⧸ J) := Ideal.finiteQuotientOfFreeOfNeBot J hJ
  have hPfin : {𝔭 : Ideal (𝓞 F) | 𝔭.IsMaximal ∧ J ≤ 𝔭}.Finite := by
    have key : ∀ 𝔭 𝔮 : Ideal (𝓞 F), J ≤ 𝔮 →
        (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F)) = (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) →
        𝔭 ≤ 𝔮 := by
      intro 𝔭 𝔮 hq he x hx
      have hmem : Ideal.Quotient.mk J x ∈ (Ideal.Quotient.mk J) '' (𝔮 : Set (𝓞 F)) :=
        he ▸ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy⟩ := hmem
      have hyx : y - x ∈ J := Ideal.Quotient.eq.mp hxy
      have := 𝔮.sub_mem hy (hq hyx)
      simpa using this
    refine Set.Finite.of_finite_image (f := fun 𝔭 : Ideal (𝓞 F) =>
      (Ideal.Quotient.mk J) '' (𝔭 : Set (𝓞 F))) (Set.toFinite _) ?_
    intro 𝔭 h𝔭 𝔮 h𝔮 he
    exact le_antisymm (key _ _ h𝔮.2 he) (key _ _ h𝔭.2 he.symm)
  set P := hPfin.toFinset with hPdef
  have hP : ∀ 𝔭, 𝔭 ∈ P ↔ 𝔭.IsMaximal ∧ J ≤ 𝔭 := fun 𝔭 => Set.Finite.mem_toFinset _
  have hmax : ∀ j : P, j.1.IsMaximal := fun j => ((hP j.1).1 j.2).1
  have H' : ∀ i : P, ∃ uv : M × M, N • uv.1 = 0 ∧ N • uv.2 = 0 ∧ ∀ x : M, N • x = 0 →
      ∃ a b : 𝓞 F, x - a • uv.1 - b • uv.2 ∈ i.1 • T := by
    intro i
    have hi := (hP i.1).1 i.2
    obtain ⟨u, v, hu, hv, hx⟩ :=
      H i.1 hi.1 ((Ideal.span_singleton_le_iff_mem _).mp hi.2)
    exact ⟨(u, v), hu, hv, hx⟩
  choose uv huv1 huv2 hgen using H'
  have hc : ∀ i : P, ∃ c : 𝓞 F, c - 1 ∈ i.1 ∧ ∀ j : P, j ≠ i → c ∈ j.1 := by
    intro i
    have htop : i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 = ⊤ := by
      apply Ideal.sup_prod_eq_top
      intro j hj
      exact (hmax i).coprime_of_ne (hmax j)
        (fun h => (Finset.ne_of_mem_erase hj) (Subtype.ext h.symm))
    have h1 : (1 : 𝓞 F) ∈ i.1 ⊔ ∏ j ∈ Finset.univ.erase i, j.1 := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, k, hk, hak⟩ := Submodule.mem_sup.mp h1
    refine ⟨k, ?_, fun j hj => ?_⟩
    · have hk1 : k - 1 = -a := by rw [← hak]; ring
      rw [hk1]; exact i.1.neg_mem ha
    · exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩))) hk
  choose c hc1 hc2 using hc
  have hcd : ∀ i j : P, c j - (if j = i then 1 else 0) ∈ i.1 := by
    intro i j
    by_cases h : j = i
    · subst h; simpa using hc1 j
    · simpa [h] using hc2 j i (fun e => h e.symm)
  have gl : ∀ (i : P) (w : P → M), (∀ j, w j ∈ T) → ∑ j, c j • w j - w i ∈ i.1 • T := by
    intro i w hw
    have hsum : ∑ j, c j • w j - w i = ∑ j, (c j - if j = i then 1 else 0) • w j := by
      simp [sub_smul, Finset.sum_sub_distrib, ite_smul]
    rw [hsum]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hcd i j) (hw j)
  have huT : ∀ j, (uv j).1 ∈ T := fun j => (hT _).2 (huv1 j)
  have hvT : ∀ j, (uv j).2 ∈ T := fun j => (hT _).2 (huv2 j)
  set p : Fin 2 → M := ![∑ j, c j • (uv j).1, ∑ j, c j • (uv j).2] with hpdef
  have hp0 : p 0 = ∑ j, c j • (uv j).1 := rfl
  have hp1 : p 1 = ∑ j, c j • (uv j).2 := rfl
  have hpT : ∀ i, p i ∈ T := by
    intro i
    fin_cases i
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (huT j)
    · exact Submodule.sum_mem _ fun j _ => T.smul_mem _ (hvT j)
  set S := Submodule.span (𝓞 F) (Set.range p) with hSdef
  have hloc : ∀ i : P, ∀ x ∈ T, ∃ a b : 𝓞 F, x - a • p 0 - b • p 1 ∈ i.1 • T := by
    intro i x hx
    obtain ⟨a, b, hab⟩ := hgen i x ((hT x).1 hx)
    refine ⟨a, b, ?_⟩
    have he : x - a • p 0 - b • p 1 = (x - a • (uv i).1 - b • (uv i).2)
        - a • (p 0 - (uv i).1) - b • (p 1 - (uv i).2) := by
      simp only [smul_sub]; abel
    rw [he]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hab (Submodule.smul_mem _ _ ?_))
      (Submodule.smul_mem _ _ ?_)
    · exact gl i (fun j => (uv j).1) huT
    · exact gl i (fun j => (uv j).2) hvT
  have hTfg : T.FG := by
    have hTset : (T : Set M) = {x : M | N • x = 0} := Set.ext hT
    have hfs : (T : Set M).Finite := by
      rw [hTset]; exact Set.finite_coe_iff.mp hfin
    exact Submodule.fg_def.mpr ⟨T, hfs, Submodule.span_eq T⟩
  set N' := T.map S.mkQ with hN'def
  have hN'fg : N'.FG := hTfg.map _
  have hprime : ∀ i : P, N' ≤ i.1 • N' := by
    rintro i _ ⟨x, hx, rfl⟩
    obtain ⟨a, b, hab⟩ := hloc i x hx
    have hq : S.mkQ x = S.mkQ (x - a • p 0 - b • p 1) := by
      simp only [Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      have : x - (x - a • p 0 - b • p 1) = a • p 0 + b • p 1 := by abel
      rw [this]
      exact S.add_mem (S.smul_mem _ (Submodule.subset_span ⟨0, rfl⟩))
        (S.smul_mem _ (Submodule.subset_span ⟨1, rfl⟩))
    rw [hq, hN'def, ← Submodule.map_smul'']
    exact Submodule.mem_map_of_mem hab
  have hprod : ∀ s : Finset P, N' ≤ (∏ i ∈ s, i.1) • N' := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert i s hi ih =>
      rw [Finset.prod_insert hi, Submodule.mul_smul]
      exact (hprime i).trans (Submodule.smul_mono le_rfl ih)
  have hjac : (∏ i : P, i.1) ≤ J.jacobson := by
    unfold Ideal.jacobson
    refine le_sInf ?_
    rintro m ⟨hJm, hm⟩
    have hmP : m ∈ P := (hP m).2 ⟨hm, hJm⟩
    exact Ideal.prod_le_inf.trans (Finset.inf_le (f := fun i : P => i.1) (Finset.mem_univ ⟨m, hmP⟩))
  have hJN' : J • N' = ⊥ := by
    rw [eq_bot_iff]
    refine Submodule.smul_le.mpr ?_
    rintro r hr _ ⟨x, hx, rfl⟩
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    have hx0 : (N : 𝓞 F) • x = 0 := (Submodule.mem_torsionBy_iff _ _).mp hx
    rw [mul_smul, ← LinearMap.map_smul, hx0, map_zero, smul_zero]
    exact Submodule.zero_mem _
  have hN'bot : N' = ⊥ := by
    rw [Submodule.eq_smul_of_le_smul_of_le_jacobson hN'fg (hprod Finset.univ) hjac, hJN']
  have hTS : T ≤ S := by
    intro x hx
    have hmem : S.mkQ x ∈ N' := Submodule.mem_map_of_mem hx
    rw [hN'bot, Submodule.mem_bot, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hmem
    exact hmem
  refine ⟨p, fun i => (hT _).1 (hpT i), fun y hy => ?_⟩
  have hyS : y ∈ S := hTS ((hT y).2 hy)
  obtain ⟨f, hf⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp hyS
  refine ⟨f 0, f 1, ?_⟩
  rw [← hf, Fin.sum_univ_two]

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_two_generators_global : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N → Finite {x : M // N • x = 0} →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      ∃ u v : M, N • u = 0 ∧ N • v = 0 ∧ ∀ x : M, N • x = 0 → ∃ a b : 𝓞 F,
        x - a • u - b • v ∈ 𝔭 • Submodule.torsionBy (𝓞 F) M (N : 𝓞 F)) →
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧ ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  atlas_forward_decl GlobalTheory.torsion_gens_glue_of_local
end

section
section
open NumberField

namespace GlobalTheory

theorem dvd_of_two_gens_of_card_torsion : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    Nat.card {x : M // N • x = 0} = N ^ (2 * Module.finrank ℚ F) →
    ∀ p : Fin 2 → M, (∀ i, N • p i = 0) →
    (∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1) →
    ∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  intro F _ _ M _ _ N hN hc p hp hgen a b hab
  classical
  set I : Ideal (𝓞 F) := Ideal.span {(N : 𝓞 F)} with hI
  have hNp : ∀ (c : 𝓞 F) i, ((N : 𝓞 F) * c) • p i = 0 := by
    intro c i
    rw [mul_comm, mul_smul, Nat.cast_smul_eq_nsmul, hp i, smul_zero]
  let ψ : 𝓞 F × 𝓞 F →+ M :=
    { toFun := fun x => x.1 • p 0 + x.2 • p 1
      map_zero' := by simp
      map_add' := by intro x y; simp [add_smul]; abel }
  let g : 𝓞 F × 𝓞 F →+ (𝓞 F ⧸ I) × (𝓞 F ⧸ I) :=
    { toFun := fun x => (Ideal.Quotient.mk I x.1, Ideal.Quotient.mk I x.2)
      map_zero' := by simp
      map_add' := by intro x y; simp }
  have hgker : ∀ x y : 𝓞 F, (x, y) ∈ g.ker ↔ (N : 𝓞 F) ∣ x ∧ (N : 𝓞 F) ∣ y := by
    intro x y
    simp only [AddMonoidHom.mem_ker, g, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Prod.mk_eq_zero,
      Ideal.Quotient.eq_zero_iff_mem, hI, Ideal.mem_span_singleton]
  have hle : g.ker ≤ ψ.ker := by
    rintro ⟨x, y⟩ hx
    rw [hgker] at hx
    obtain ⟨⟨c, rfl⟩, ⟨d, rfl⟩⟩ := hx
    simp [ψ, hNp]
  have hrange : (ψ.range : Set M) = {x : M | N • x = 0} := by
    ext y
    simp only [SetLike.mem_coe, AddMonoidHom.mem_range, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨x1, x2⟩, rfl⟩
      simp only [ψ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, smul_add]
      rw [smul_comm, hp 0, smul_zero, smul_comm, hp 1, smul_zero, add_zero]
    · intro hy
      obtain ⟨a, b, rfl⟩ := hgen y hy
      exact ⟨(a, b), rfl⟩
  have hindψ : ψ.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    rw [AddSubgroup.index_ker, ← hc]
    exact Nat.card_congr (Equiv.setCongr hrange)
  have hcardR : Nat.card (𝓞 F ⧸ I) = N ^ Module.finrank ℚ F := by
    have h1 := Ideal.absNorm_span_singleton (S := 𝓞 F) (N : 𝓞 F)
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply] at h1
    rw [hI, h1, ← map_natCast (algebraMap ℤ (𝓞 F)) N, Algebra.norm_algebraMap,
      NumberField.RingOfIntegers.rank]
    simp
  have hindg : g.ker.index = N ^ (2 * Module.finrank ℚ F) := by
    have hs : Function.Surjective g := by
      rintro ⟨u, v⟩
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective u
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
      exact ⟨(x, y), rfl⟩
    rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.mpr hs]
    rw [Nat.card_congr (AddSubgroup.topEquiv).toEquiv, Nat.card_prod, hcardR, ← pow_add, two_mul]
  have hrel := AddSubgroup.relIndex_mul_index hle
  rw [hindψ, hindg] at hrel
  have hpos : 0 < N ^ (2 * Module.finrank ℚ F) := pow_pos (by omega) _
  have h1 : g.ker.relIndex ψ.ker = 1 := by
    have := Nat.eq_of_mul_eq_mul_right hpos (hrel.trans (one_mul _).symm)
    exact this
  have hk := AddSubgroup.relIndex_eq_one.mp h1
  have hmem : ((a, b) : 𝓞 F × 𝓞 F) ∈ ψ.ker := hab
  have := hk hmem
  exact (hgker a b).mp this

end GlobalTheory
end

open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_basis_relations_divisible : ∀ (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M] (N : ℕ), 1 ≤ N →
    Nat.card {x : M // N • x = 0} = N ^ (2 * Module.finrank ℚ F) →
    ∀ p : Fin 2 → M, (∀ i, N • p i = 0) →
    (∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1) →
    ∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b := by
  atlas_forward_decl GlobalTheory.dvd_of_two_gens_of_card_torsion
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RankTwoTorsion

theorem ptorsion_sub (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (𝔭 : Ideal (𝓞 F)) (hN𝔭 : (N : 𝓞 F) ∈ 𝔭) (n : ℕ) (x : M) (hx : ∀ a ∈ 𝔭 ^ n, a • x = 0) :
    (N ^ n) • x = 0 := by
  have := hx _ (Ideal.pow_mem_pow hN𝔭 n)
  rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at this

theorem rank_two_torsion (F : Type) [Field F] [NumberField F] (M : Type) [AddCommGroup M] [Module (𝓞 F) M]
    (N : ℕ) (hN : 1 ≤ N)
    (h2 : ∀ j : ℕ, Nat.card {x : M // (N ^ j) • x = 0} = (N ^ j) ^ (2 * Module.finrank ℚ F))
    (h3 : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 → ∃ C : ℕ, ∀ n : ℕ,
      Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} ≤ C * Ideal.absNorm 𝔭 ^ (2 * n)) :
    ∃ p : Fin 2 → M, (∀ i, N • p i = 0) ∧
      (∀ a b : 𝓞 F, a • p 0 + b • p 1 = 0 → (N : 𝓞 F) ∣ a ∧ (N : 𝓞 F) ∣ b) ∧
      ∀ y : M, N • y = 0 → ∃ a b : 𝓞 F, y = a • p 0 + b • p 1 := by
  have hfin : ∀ j : ℕ, Finite {x : M // (N ^ j) • x = 0} := fun j => by
    apply Nat.finite_of_card_ne_zero
    rw [h2 j]; positivity
  have hdiv := GlobalTheory.T.torsion_lift_number_field_module F M N hN h2
  have hfin1 : Finite {x : M // N • x = 0} := by simpa using hfin 1
  have hp : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → (N : 𝓞 F) ∈ 𝔭 →
      Nat.card {x : M // ∀ a ∈ 𝔭, a • x = 0} ≤ Ideal.absNorm 𝔭 ^ 2 := by
    intro 𝔭 h𝔭 hN𝔭
    obtain ⟨C, hC⟩ := h3 𝔭 h𝔭 hN𝔭
    obtain ⟨e, he, hblk⟩ := GlobalTheory.T.torsion_count_multiplicative_prime_powers F M N hN hfin hdiv 𝔭 h𝔭 hN𝔭
    have hfinp : ∀ n, Finite {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := fun n =>
      Finite.of_injective (fun x => (⟨x.1, ptorsion_sub F M N 𝔭 hN𝔭 n x.1 x.2⟩ :
        {x : M // (N ^ n) • x = 0})) (fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h))
    have h0 : Nat.card {x : M // ∀ a ∈ 𝔭 ^ 0, a • x = 0} = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun x y => Subtype.ext ?_⟩, ⟨⟨0, fun a _ => smul_zero a⟩⟩⟩
      have hx := x.2 1 (by simp); have hy := y.2 1 (by simp)
      simp only [one_smul] at hx hy; rw [hx, hy]
    have := GlobalTheory.T.log_concave_multiplicative_growth_bound (fun n => Nat.card {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}) e C
      (Ideal.absNorm 𝔭 ^ 2) he h0
      (fun n => by
        haveI := hfinp n
        haveI : Nonempty {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0} := ⟨⟨0, fun a _ => smul_zero a⟩⟩
        exact Nat.card_pos (α := {x : M // ∀ a ∈ 𝔭 ^ n, a • x = 0}))
      (fun k => GlobalTheory.T.torsion_count_log_concave_prime_powers F M 𝔭 h𝔭 k (hfinp (k + 2))) hblk
      (fun n => by rw [← pow_mul]; exact hC n)
    simpa using this
  obtain ⟨p, hpN, hgen⟩ := GlobalTheory.T.torsion_two_generators_global F M N hN hfin1
    (fun 𝔭 h𝔭 hN𝔭 => GlobalTheory.T.torsion_two_generators_mod_prime F M N hN hfin1 𝔭 h𝔭 hN𝔭 (hp 𝔭 h𝔭 hN𝔭))
  exact ⟨p, hpN, GlobalTheory.T.torsion_basis_relations_divisible F M N hN (by simpa using h2 1) p hpN hgen, hgen⟩

end GlobalTheory.RankTwoTorsion
end
