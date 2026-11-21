import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ColsDim

noncomputable section

namespace PI.UnitaryGroupMassFormula.DiaFixDim.Main

open Formalism.UG Formalism.L2.SG.ClassAct Module

def dk {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) : Subgroup G where
  carrier := {g | ∃ δ ∈ D, ∃ κ ∈ K, g = δ * κ}
  one_mem' := ⟨1, D.one_mem, 1, K.one_mem, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨δ, hδ, κ, hκ, rfl⟩ ⟨δ', hδ', κ', hκ', rfl⟩
    exact ⟨δ * δ', D.mul_mem hδ hδ', (δ'⁻¹ * κ * δ') * κ',
      K.mul_mem (hN.inv_conj hδ' hκ) hκ', by group⟩
  inv_mem' := by
    rintro _ ⟨δ, hδ, κ, hκ, rfl⟩
    exact ⟨δ⁻¹, D.inv_mem hδ, δ * κ⁻¹ * δ⁻¹, hN δ hδ _ (K.inv_mem hκ), by group⟩

theorem mem_dk {G : Type} [Group G] (K D : Subgroup G) (hN : Normalises D K) {g : G} :
    g ∈ dk K D hN ↔ ∃ δ ∈ D, ∃ κ ∈ K, g = δ * κ := Iff.rfl




theorem exists_semidirect_decomposition {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K}
    (g : dk K D hN) : ∃ p : D × K, (g : G) = (p.1 : G) * (p.2 : G) := by
  obtain ⟨δ, hδ, κ, hκ, e⟩ := (mem_dk K D hN).1 g.2
  exact ⟨(⟨δ, hδ⟩, ⟨κ, hκ⟩), e⟩

theorem chi_wd {G : Type} [Group G] {K D : Subgroup G} (k : Type) [Field k] (χ : K →* kˣ)
    (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) {δ δ' : G} (hδ : δ ∈ D) (hδ' : δ' ∈ D)
    (κ κ' : K) (e : δ * (κ : G) = δ' * κ') : χ κ = χ κ' := by
  have hm : ((κ' * κ⁻¹ : K) : G) ∈ D := by
    have h2 : ((κ' * κ⁻¹ : K) : G) = δ'⁻¹ * δ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      calc (κ' : G) * (κ : G)⁻¹ = δ'⁻¹ * (δ' * κ') * (κ : G)⁻¹ := by group
        _ = δ'⁻¹ * (δ * κ) * (κ : G)⁻¹ := by rw [← e]
        _ = δ'⁻¹ * δ := by group
    rw [h2]
    exact D.mul_mem (D.inv_mem hδ') hδ
  have h1 := htriv _ hm
  rw [map_mul, map_inv, mul_inv_eq_one] at h1
  exact h1.symm

def extendedCharacterOnQuotient {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K} {k : Type} [Field k]
    (χ : K →* kˣ) (g : dk K D hN) : kˣ :=
  χ (Classical.choose (exists_semidirect_decomposition g)).2

theorem chi1Fun_eq {G : Type} [Group G] {K D : Subgroup G} {hN : Normalises D K} (k : Type)
    [Field k] (χ : K →* kˣ) (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) (g : dk K D hN) {δ : G}
    (hδ : δ ∈ D) (κ : K) (e : (g : G) = δ * κ) : extendedCharacterOnQuotient χ g = χ κ := by
  have spec := Classical.choose_spec (exists_semidirect_decomposition g)
  exact chi_wd k χ htriv (Classical.choose (exists_semidirect_decomposition g)).1.2 hδ _ _ (spec.symm.trans e)

def chi1 {G : Type} [Group G] {K D : Subgroup G} (hN : Normalises D K) (k : Type) [Field k]
    (χ : K →* kˣ) (hinv : ∀ δ ∈ D, ∀ κ κ' : K, (κ' : G) = δ * κ * δ⁻¹ → χ κ' = χ κ)
    (htriv : ∀ κ : K, (κ : G) ∈ D → χ κ = 1) : dk K D hN →* kˣ where
  toFun := extendedCharacterOnQuotient χ
  map_one' := by
    show extendedCharacterOnQuotient χ (1 : dk K D hN) = 1
    rw [chi1Fun_eq k χ htriv 1 D.one_mem 1 (by simp), map_one]
  map_mul' g g' := by
    show extendedCharacterOnQuotient χ (g * g') = extendedCharacterOnQuotient χ g * extendedCharacterOnQuotient χ g'
    obtain ⟨δ, hδ, κ, hκ, e⟩ := (mem_dk K D hN).1 g.2
    obtain ⟨δ', hδ', κ', hκ', e'⟩ := (mem_dk K D hN).1 g'.2
    let κc : K := ⟨δ'⁻¹ * κ * δ', hN.inv_conj hδ' hκ⟩
    have hg : ((g * g' : dk K D hN) : G) = (δ * δ') * ((κc * ⟨κ', hκ'⟩ : K) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, e, e']
      show δ * κ * (δ' * κ') = δ * δ' * ((δ'⁻¹ * κ * δ') * κ')
      group
    rw [chi1Fun_eq k χ htriv _ (D.mul_mem hδ hδ') _ hg, chi1Fun_eq k χ htriv g hδ ⟨κ, hκ⟩ e,
      chi1Fun_eq k χ htriv g' hδ' ⟨κ', hκ'⟩ e', map_mul]
    congr 1
    exact hinv δ'⁻¹ (D.inv_mem hδ') ⟨κ, hκ⟩ κc
      (by show δ'⁻¹ * κ * δ' = δ'⁻¹ * κ * δ'⁻¹⁻¹; rw [inv_inv])



theorem neat_one {G : Type} [Group G] {Γ K₀ : Subgroup G} (hn : IsNeat Γ K₀) {x γ : G}
    (hγ : γ ∈ Γ) (h : x⁻¹ * γ * x ∈ K₀) : γ = 1 := by
  have hm : (⟨γ, hγ⟩ : Γ) ∈ stabAt Γ K₀ x := h
  rw [hn x] at hm
  exact congrArg Subtype.val hm

theorem stabTriv_of {G : Type} [Group G] (Γ K₁ K₀ : Subgroup G) (h : K₁ ≤ K₀)
    (hn : IsNeat Γ K₀) : Formalism.L2.SG.ColsDim.StabTriv Γ.subtype K₁ := by
  intro x γ hx
  exact Subtype.ext (neat_one hn γ.2 (h hx))



def phiMap {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K)
    (p : ClassSet Γ (dk K D hN) × (D ⧸ K.subgroupOf D)) : ClassSet Γ K :=
  DoubleCoset.mk Γ K (Quotient.out p.1 * ((Quotient.out p.2 : D) : G))

theorem phiMap_inj {G : Type} [Group G] (Γ K K₀ D : Subgroup G) (hN : Normalises D K)
    (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) : Function.Injective (phiMap Γ K D hN) := by
  rintro ⟨c, q⟩ ⟨c', q'⟩ he
  obtain ⟨γ, hγ, κ, hκ, e0⟩ := (DoubleCoset.eq Γ K _ _).1 he
  have e : Quotient.out c' * ((Quotient.out q' : D) : G) =
      γ * (Quotient.out c * ((Quotient.out q : D) : G)) * κ := e0
  have hc : c = c' := by
    rw [← DoubleCoset.out_eq' Γ (dk K D hN) c, ← DoubleCoset.out_eq' Γ (dk K D hN) c']
    refine (DoubleCoset.eq Γ (dk K D hN) _ _).2 ⟨γ, hγ,
      ((Quotient.out q : D) : G) * κ * ((Quotient.out q' : D) : G)⁻¹, ?_, ?_⟩
    · exact (mem_dk K D hN).2 ⟨((Quotient.out q : D) : G) * ((Quotient.out q' : D) : G)⁻¹,
        D.mul_mem (Quotient.out q).2 (D.inv_mem (Quotient.out q').2),
        ((Quotient.out q' : D) : G) * κ * ((Quotient.out q' : D) : G)⁻¹,
        hN _ (Quotient.out q').2 _ hκ, by group⟩
    · calc Quotient.out c' = Quotient.out c' * ((Quotient.out q' : D) : G) *
            ((Quotient.out q' : D) : G)⁻¹ := by group
        _ = _ := by rw [e]; group
  rw [← hc] at e
  have hγe : γ = Quotient.out c * ((Quotient.out q' : D) : G) * κ⁻¹ *
      ((Quotient.out q : D) : G)⁻¹ * (Quotient.out c)⁻¹ := by
    rw [e]; group
  have hγ1 : γ = 1 := by
    refine neat_one hn hγ (x := Quotient.out c) ?_
    have h3 : (Quotient.out c)⁻¹ * γ * Quotient.out c =
        ((Quotient.out q' : D) : G) * κ⁻¹ * ((Quotient.out q : D) : G)⁻¹ := by
      rw [hγe]; group
    rw [h3]
    exact K₀.mul_mem (K₀.mul_mem (hD (Quotient.out q').2) (K₀.inv_mem (hK hκ)))
      (K₀.inv_mem (hD (Quotient.out q).2))
  have e3 : Quotient.out c * ((Quotient.out q' : D) : G) =
      Quotient.out c * (((Quotient.out q : D) : G) * κ) := by
    rw [e, hγ1]; group
  have hq : q = q' := by
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' q', QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    have h4 : (((Quotient.out q)⁻¹ * Quotient.out q' : D) : G) = κ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_left_cancel e3]; group
    rw [h4]; exact hκ
  rw [hc, hq]

theorem phiMap_surj {G : Type} [Group G] (Γ K D : Subgroup G) (hN : Normalises D K) :
    Function.Surjective (phiMap Γ K D hN) := by
  intro c
  obtain ⟨γ, hγ, κ₁, hκ₁, e⟩ := (DoubleCoset.eq Γ (dk K D hN)
    (Quotient.out (DoubleCoset.mk Γ (dk K D hN) (Quotient.out c))) (Quotient.out c)).1
    (DoubleCoset.out_eq' Γ (dk K D hN) (DoubleCoset.mk Γ (dk K D hN) (Quotient.out c)))
  obtain ⟨δ, hδ, κ, hκ, rfl⟩ := (mem_dk K D hN).1 hκ₁
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf D) (⟨δ, hδ⟩ : D)
  refine ⟨(DoubleCoset.mk Γ (dk K D hN) (Quotient.out c),
    (QuotientGroup.mk (⟨δ, hδ⟩ : D) : D ⧸ K.subgroupOf D)), ?_⟩
  refine Eq.trans ?_ (DoubleCoset.out_eq' Γ K c)
  dsimp only [phiMap]
  rw [hh]
  have hcoe : (((⟨δ, hδ⟩ : D) * (h : D) : D) : G) = δ * ((h : D) : G) := rfl
  rw [hcoe]
  refine (DoubleCoset.eq Γ K _ _).2 ⟨γ, hγ, ((h : D) : G)⁻¹ * κ,
    K.mul_mem (K.inv_mem (Subgroup.mem_subgroupOf.1 h.2)) hκ, ?_⟩
  refine e.trans ?_
  group

theorem card_classes {G : Type} [Group G] (Γ K K₀ D : Subgroup G) (hN : Normalises D K)
    (hK : K ≤ K₀) (hD : D ≤ K₀) (hn : IsNeat Γ K₀) :
    Nat.card (ClassSet Γ K) = Nat.card (ClassSet Γ (dk K D hN)) * K.relIndex D := by
  rw [← Nat.card_congr (Equiv.ofBijective (phiMap Γ K D hN)
    ⟨phiMap_inj Γ K K₀ D hN hK hD hn, phiMap_surj Γ K D hN⟩), Nat.card_prod,
    Subgroup.relIndex, Subgroup.index_eq_card]


end PI.UnitaryGroupMassFormula.DiaFixDim.Main
