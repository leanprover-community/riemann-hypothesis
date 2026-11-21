import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap
import GroundTheory.LocalFields.AbstractLocalReciprocity.FunctorialityTransfer
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.TransferOfCompSubtype

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Augmentation

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem exists_eq_smul_div_of_mem_augmentation_of_generator {K L : Subgroup G} (hLK : L ≤ K)
    [(L.subgroupOf K).Normal] {τ : G} (hτ : τ ∈ K) (hgen : ∀ g ∈ K, ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ L)
    {x : A} (hx : x ∈ augmentation A K L) : ∃ b ∈ fixedModule A L, x = τ • b / b := by

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A L, y = τ • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup K :=
    { carrier := {g | ∀ a ∈ fixedModule A L, (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A L := smul_mem_fixedModule_of_normal hLK h.2 ha
        have e : ((g * h : K) : G) • a / a = ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : K) : G) • a ∈ fixedModule A L :=
          smul_mem_fixedModule_of_normal hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : K) : G) • a / a =
            ((g : G) • (((g⁻¹ : K) : G) • a) / (((g⁻¹ : K) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hτT : (⟨τ, hτ⟩ : K) ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : K, (ρ : G) ∈ L → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : K, g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := hgen g g.2
    have hg : g = (⟨τ, hτ⟩ : K) ^ m * (((⟨τ, hτ⟩ : K) ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hτT m) (hLT _ (by simpa using hm))
  have hle : augmentation A K L ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

end Augmentation

theorem exists_pow_eq_of_exists_zpow_eq {α : Type*} [Group α] [Finite α] {g x : α}
    (h : ∃ n : ℤ, g ^ n = x) : ∃ k : ℕ, g ^ k = x := by
  have hx : x ∈ Subgroup.zpowers g := Subgroup.mem_zpowers_iff.2 h
  rw [← mem_powers_iff_mem_zpowers] at hx
  exact (Submonoid.mem_powers_iff _ _).1 hx

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

section Galois

omit [TotallyDisconnectedSpace G] in

theorem valuation_smul_of_map_eq (S : OpenSubgroup G) {g : G}
    (hg : (S : Subgroup G).map (MulAut.conj g).toMonoidHom = S) (a : fixedModule A (S : Subgroup G))
    (hga : g • (a : A) ∈ fixedModule A (S : Subgroup G)) :
    D.valuation S ⟨g • (a : A), hga⟩ = D.valuation S a := by
  rw [valuation_eq_iff, valuation_pow]
  congr 1
  ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective
  have h := smul_norm_of_map_eq (A := A) g htop hg a
  refine h.symm.trans ?_
  exact (norm A ⊤ (S : Subgroup G) a).2 g trivial

variable {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in

theorem commutator_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {a b : G}
    (ha : a ∈ (K : Subgroup G)) (hb : b ∈ (K : Subgroup G)) :
    a⁻¹ * b⁻¹ * a * b ∈ (L : Subgroup G) ⊓ D.deg.ker := by
  refine Subgroup.mem_inf.2 ⟨?_, MonoidHom.mem_ker.2 ?_⟩
  · have := hcyc
    have hc : ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        ((⟨a, ha⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
        ((⟨b, hb⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
      IsCyclic.commGroup.mul_comm _ _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hc
    simpa [mul_assoc] using hc
  · rw [map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_right_comm (D.deg a)⁻¹, inv_mul_cancel, one_mul, inv_mul_cancel]

omit [TotallyDisconnectedSpace G] in

theorem conj_mem_of_isCyclic [((L : Subgroup G).subgroupOf K).Normal]
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) {H : Subgroup G}
    (hH : (L : Subgroup G) ⊓ D.deg.ker ≤ H) {g h : G} (hg : g ∈ (K : Subgroup G))
    (hh : h ∈ (K : Subgroup G)) (hhH : h ∈ H) : g * h * g⁻¹ ∈ H := by
  have hc := commutator_mem_of_isCyclic (D := D) hcyc hh (K.inv_mem hg)
  have e : g * h * g⁻¹ = h * (h⁻¹ * g⁻¹⁻¹ * h * g⁻¹) := by group
  rw [e]
  exact H.mul_mem hhH (hH hc)

end Galois

section Hull

variable (D) in

def maxUnramified (K L : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G) ⊓ ((L : Subgroup G).map D.deg).comap D.deg
  isOpen' := Subgroup.isOpen_mono (H₁ := ((K ⊓ L : OpenSubgroup G) : Subgroup G))
    (fun x hx => ⟨hx.1, x, hx.2, rfl⟩) (K ⊓ L).isOpen

variable {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in
theorem mem_maxUnramified {g : G} :
    g ∈ (D.maxUnramified K L : Subgroup G) ↔
      g ∈ (K : Subgroup G) ∧ ∃ l ∈ (L : Subgroup G), D.deg l = D.deg g :=
  Iff.rfl

omit [TotallyDisconnectedSpace G] in
theorem maxUnramified_le : D.maxUnramified K L ≤ K := fun _ hx => hx.1

omit [TotallyDisconnectedSpace G] in
theorem le_maxUnramified (hLK : L ≤ K) : L ≤ D.maxUnramified K L :=
  fun x hx => ⟨hLK hx, x, hx, rfl⟩

omit [TotallyDisconnectedSpace G] in

theorem inf_ker_le_maxUnramified :
    (K : Subgroup G) ⊓ D.deg.ker ≤ (D.maxUnramified K L : Subgroup G) :=
  fun x hx => ⟨hx.1, 1, (L : Subgroup G).one_mem, by rw [map_one, (MonoidHom.mem_ker.1 hx.2)]⟩

omit [TotallyDisconnectedSpace G] in

theorem relInertiaDegree_maxUnramified :
    relInertiaDegree D.deg (D.maxUnramified K L) L = 1 := by
  rw [relInertiaDegree, Subgroup.relIndex_eq_one]
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨l, hl, e⟩ := hg.2
  exact ⟨l, hl, e⟩

end Hull

section Unramified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_frobenius_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    {π : fixedModule A (K : Subgroup G)} (hπ : D.valuation K π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK hax (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (π : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  have hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
    rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]
  set s : D.FrobeniusLift K := FrobeniusLift.ofDegOne φ.2 hdφ with hs
  have hSK := s.field_le hLK

  have he : relRamificationIndex D.deg K (s.field L hLK) = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro x hx
    exact le_frobeniusClosure ⟨hu ⟨hx.2, hx.1⟩, hx.1⟩
  have hrel : ((s.field L hLK : OpenSubgroup G) : Subgroup G).relIndex K = 1 := by
    rw [relIndex_eq_mul (d := D.deg) hSK, he, FrobeniusLift.relInertiaDegree_field hLK s]
    rfl
  have hπ' : D.valuation (s.field L hLK) ⟨π, fixedModule_anti hSK π.2⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hSK π.2, he, pow_one]
    exact hπ
  have h := reciprocity_mk_eq_norm hLK hax s hπ'
  refine h.trans ?_
  congr 1
  ext
  rw [coe_norm_of_mem hSK π.2, hrel, pow_one]

end Unramified

section TotallyRamified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_injective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Injective (D.reciprocity hLK hax) := by

  have hdeg : ∀ k ∈ (K : Subgroup G), ∃ l ∈ (L : Subgroup G), D.deg l = D.deg k := by
    intro k hk
    obtain ⟨l, hl, e⟩ := (Subgroup.relIndex_eq_one.1 htot) ⟨k, hk, rfl⟩
    exact ⟨l, hl, e⟩

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨φ, hφL, hdφ⟩ := hdeg φ0 hφ0K

  have := hcyc
  obtain ⟨γ, hγ⟩ := exists_zpow_surjective ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  obtain ⟨g0, rfl⟩ := QuotientGroup.mk_surjective γ
  obtain ⟨l0, hl0L, hl0⟩ := hdeg g0 g0.2
  obtain ⟨τ, hτdef⟩ : ∃ τ : G, τ = (g0 : G) * l0⁻¹ := ⟨_, rfl⟩
  have hτK : τ ∈ (K : Subgroup G) := hτdef ▸ K.mul_mem g0.2 (K.inv_mem (hLK hl0L))
  have hτker : D.deg τ = 1 := by rw [hτdef, map_mul, map_inv, hl0, mul_inv_cancel]
  have hτγ : (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (g0 : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hτdef, mul_assoc] using hl0L
  have hpow : ∀ q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K, ∃ m : ℕ,
      (((⟨τ, hτK⟩ : (K : Subgroup G))) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m = q := by
    intro q
    rw [hτγ]
    exact exists_pow_eq_of_exists_zpow_eq (hγ q)
  have hgen : ∀ k ∈ (K : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * k ∈ (L : Subgroup G) := by
    intro k hk
    obtain ⟨m, hm⟩ := hpow (⟨k, hk⟩ : (K : Subgroup G))
    refine ⟨m, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hm
    simpa using hm
  rw [injective_iff_map_eq_one]
  intro σ hσ
  obtain ⟨k, rfl⟩ := hpow σ
  rw [← QuotientGroup.mk_pow] at hσ ⊢

  obtain ⟨s, hs_elt, hs_deg⟩ : ∃ s : D.FrobeniusLift K, s.elt = τ ^ k * φ ∧ s.deg = 1 :=
    ⟨{ elt := τ ^ k * φ
       mem := K.mul_mem (K.pow_mem hτK k) (hLK hφL)
       deg := 1
       deg_pos := one_pos
       deg_eq := by rw [map_mul, map_pow, hτker, one_pow, one_mul, hdφ, hdφ0, one_mul] }, rfl, rfl⟩
  have hs : ((((⟨τ, hτK⟩ : (K : Subgroup G)) ^ k : (K : Subgroup G))) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [hs_elt] using hφL
  rw [hs] at hσ
  obtain ⟨π0, hπ0⟩ := D.exists_prime (s.field L hLK)
  rw [reciprocity_mk_eq_norm hLK hax s hπ0, QuotientGroup.eq_one_iff] at hσ
  obtain ⟨b, hb⟩ := hσ

  have hvb : D.valuation L b = Multiplicative.ofAdd 1 := by
    have h1 := D.valuation_norm hLK b
    rw [htot, pow_one, hb, valuation_norm_prime hLK s hπ0, hs_deg, Nat.cast_one] at h1
    exact h1.symm

  obtain ⟨L1, hL1L, hL1S, hIL⟩ : ∃ L1 : OpenSubgroup G, L1 ≤ L ∧ L1 ≤ s.field L hLK ∧
      (L : Subgroup G) ⊓ D.deg.ker ≤ L1 :=
    ⟨L ⊓ s.field L hLK, inf_le_left, inf_le_right, fun x hx => ⟨hx.1, le_frobeniusClosure hx⟩⟩
  have hL1K : L1 ≤ K := hL1L.trans hLK
  obtain ⟨K1, hL1K1, hK1K, hIK1, hK1deg⟩ : ∃ K1 : OpenSubgroup G, L1 ≤ K1 ∧ K1 ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ K1 ∧
      ∀ g ∈ (K1 : Subgroup G), ∃ l ∈ (L1 : Subgroup G), D.deg l = D.deg g :=
    ⟨D.maxUnramified K L1, le_maxUnramified hL1K, maxUnramified_le, inf_ker_le_maxUnramified,
      fun g hg => (mem_maxUnramified.1 hg).2⟩

  have hconj : ∀ g ∈ (K : Subgroup G), ∀ h ∈ (L1 : Subgroup G), g * h * g⁻¹ ∈ (L1 : Subgroup G) :=
    fun g hg h hh => conj_mem_of_isCyclic (D := D) hcyc hIL hg (hL1K hh) hh
  have hmapL1 : ∀ g ∈ (K : Subgroup G),
      (L1 : Subgroup G).map (MulAut.conj g).toMonoidHom = L1 := by
    intro g hg
    refine le_antisymm ?_ fun h hh => ⟨g⁻¹ * h * g, ?_, ?_⟩
    · rintro _ ⟨h, hh, rfl⟩
      exact hconj g hg h hh
    · simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    · simp [MulAut.conj_apply, mul_assoc]
  have hsmulL1 : ∀ g ∈ (K : Subgroup G), ∀ a ∈ fixedModule A (L1 : Subgroup G),
      g • a ∈ fixedModule A (L1 : Subgroup G) := by
    intro g hg a ha h hh
    have hc : g⁻¹ * h * g ∈ (L1 : Subgroup G) := by simpa using hconj g⁻¹ (K.inv_mem hg) h hh
    calc h • g • a = g • (g⁻¹ * h * g) • a := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = g • a := by rw [ha _ hc]
  have hN1 : ((L1 : Subgroup G).subgroupOf K1).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K g.2) n hn⟩

  have hτK1 : τ ∈ (K1 : Subgroup G) := hIK1 (Subgroup.mem_inf.2 ⟨hτK, MonoidHom.mem_ker.2 hτker⟩)
  have hgen1 : ∀ g ∈ (K1 : Subgroup G), ∃ m : ℕ, (τ ^ m)⁻¹ * g ∈ (L1 : Subgroup G) := by
    intro g hg
    obtain ⟨l, hl, hdl⟩ := hK1deg g hg
    obtain ⟨m, hm⟩ := hgen (g * l⁻¹) (K.mul_mem (hK1K hg) (K.inv_mem (hL1K hl)))
    refine ⟨m, ?_⟩
    have hker : (τ ^ m)⁻¹ * (g * l⁻¹) ∈ D.deg.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_pow, hτker, one_pow, inv_one, one_mul, map_mul,
        map_inv, hdl, mul_inv_cancel]
    have h := (L1 : Subgroup G).mul_mem (hIL (Subgroup.mem_inf.2 ⟨hm, hker⟩)) hl
    simpa [mul_assoc] using h
  have hcyc1 : IsCyclic ((K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1) := by
    refine ⟨⟨((⟨τ, hτK1⟩ : (K1 : Subgroup G)) : (K1 : Subgroup G) ⧸ (L1 : Subgroup G).subgroupOf K1),
      fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨m, hm⟩ := hgen1 g g.2
      refine ⟨m, ?_⟩
      show _ ^ ((m : ℕ) : ℤ) = _
      rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hm

  have hNS : (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) π0 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨π0, fixedModule_anti le_frobeniusClosure π0.2⟩ : A) := by
    rw [coe_norm_field_eq hLK s hφ0K hdφ0 π0, Fintype.prod_eq_single
      (⟨0, by rw [hs_deg]; exact one_pos⟩ : Fin s.deg) (fun ν hν => absurd (Fin.ext (by
        have := ν.2
        omega)) hν), Fin.val_mk, pow_zero, one_smul]
  have hNL : (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨b, fixedModule_anti inf_le_left b.2⟩ : A) := by
    have h := coe_norm_eq_prod_smul_norm (A := A) D.deg (n := 1) one_pos
      (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) (fun x hx => hLK hx)
      (fun x hx => by rw [one_mul]; exact toAdd_deg_mem_multiples (D := D) K (hLK hx))
      (fun k hk _ => hdeg k hk)
      (fun k hk => toAdd_deg_mem_multiples (D := D) K hk)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => (Subgroup.mem_inf.1 h).1⟩) hφ0K hdφ0 b (fixedModule_anti inf_le_left b.2)
    rw [h]
    simp
  have hNK1 : ∀ a : fixedModule A (L1 : Subgroup G),
      (norm A (K1 : Subgroup G) (L1 : Subgroup G) a : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti hIL a.2⟩ : A) := fun a =>
    coe_norm_eq_of_mul_eq (fun x hx => hIK1 hx)
      (fun k hk => by
        obtain ⟨l, hl, hdl⟩ := hK1deg k hk
        refine ⟨k * l⁻¹, Subgroup.mem_inf.2 ⟨K.mul_mem (hK1K hk) (K.inv_mem (hL1K hl)), ?_⟩, ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hdl, mul_inv_cancel]
        · simpa using hl)
      (fun q hq => ⟨fun h => Subgroup.mem_inf.2 ⟨hL1L h, (Subgroup.mem_inf.1 hq).2⟩,
        fun h => hIL h⟩) a _

  have hπ0L1 : (π0 : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1S π0.2
  have hbL1 : (b : A) ∈ fixedModule A (L1 : Subgroup G) := fixedModule_anti hL1L b.2
  have hy : norm A (K1 : Subgroup G) (L1 : Subgroup G)
      ((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩) = 1 := by
    rw [map_div, div_eq_one]
    ext
    rw [hNK1, hNK1]
    exact (hNS.symm.trans (congrArg Subtype.val hb).symm).trans hNL
  obtain ⟨-, hH1⟩ := hax K1 L1 hL1K1 hcyc1
  have hsub := (Nat.card_eq_one_iff_unique.1 hH1).1
  have haug : (((⟨π0, hπ0L1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨b, hbL1⟩ :
      fixedModule A (L1 : Subgroup G)) : A) ∈ augmentation A (K1 : Subgroup G) (L1 : Subgroup G) :=
    (QuotientGroup.eq_one_iff (N := (augmentation A (K1 : Subgroup G) (L1 : Subgroup G)).comap
        ((fixedModule A (L1 : Subgroup G)).subtype.comp
          (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker.subtype))
      (⟨_, hy⟩ : (norm A (K1 : Subgroup G) (L1 : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
  obtain ⟨x, hxL1, hxy⟩ := exists_eq_smul_div_of_mem_augmentation_of_generator
    (fun z hz => hL1K1 hz) hτK1 hgen1 haug
  have hπ0x : (π0 : A) = τ • x / x * b := by
    rw [← hxy, Subgroup.coe_div, div_mul_cancel]

  have hσπ : s.elt • (π0 : A) = π0 := π0.2 s.elt (s.elt_mem_field hLK)
  have hσb : s.elt • (b : A) = τ ^ k • (b : A) := by rw [hs_elt, mul_smul, b.2 φ hφL]
  have hcomm : s.elt • τ • x = τ • s.elt • x := by
    have hc : s.elt⁻¹ * τ⁻¹ * s.elt * τ ∈ (L1 : Subgroup G) :=
      hIL (commutator_mem_of_isCyclic (D := D) hcyc s.mem hτK)
    calc s.elt • τ • x = (τ * s.elt) • (s.elt⁻¹ * τ⁻¹ * s.elt * τ) • x := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = τ • s.elt • x := by rw [hxL1 _ hc, mul_smul]
  have e1 : τ • (s.elt • x) / s.elt • x * τ ^ k • (b : A) = τ • x / x * b := by
    have h := hσπ
    rw [hπ0x, smul_mul', smul_div', hcomm, hσb] at h
    exact h

  obtain ⟨c, hcdef⟩ : ∃ c : A, c = ∏ ν : Fin k, τ ^ (ν : ℕ) • (b : A) := ⟨_, rfl⟩
  obtain ⟨z, hzdef⟩ : ∃ z : A, z = x / s.elt • x := ⟨_, rfl⟩
  have hτc : τ • c / c = τ ^ k • (b : A) / b := by rw [hcdef]; exact smul_prod_pow_div τ (b : A) k
  have hkb : τ ^ k • (b : A) / b = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [div_eq_div_iff_mul_eq_mul, mul_comm (τ ^ k • (b : A))]
    exact e1
  have hτz : τ • z / z = τ • x / x / (τ • (s.elt • x) / s.elt • x) := by
    rw [hzdef, smul_div', div_div_div_comm]
  have hτw : τ • (c / z) = c / z := by
    have h : τ • (c / z) / (c / z) = 1 := by
      rw [smul_div', div_div_div_comm, hτc, hτz, hkb, div_self']
    exact div_eq_one.1 h
  have hcL1 : c ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hcdef]
    exact Subgroup.prod_mem _ fun ν _ => hsmulL1 _ (K.pow_mem hτK _) _ hbL1
  have hσxL1 : s.elt • x ∈ fixedModule A (L1 : Subgroup G) := hsmulL1 _ s.mem x hxL1
  have hzL1 : z ∈ fixedModule A (L1 : Subgroup G) := by
    rw [hzdef]
    exact Subgroup.div_mem _ hxL1 hσxL1
  have hwL1 : c / z ∈ fixedModule A (L1 : Subgroup G) := Subgroup.div_mem _ hcL1 hzL1
  have hpw : ∀ m : ℕ, τ ^ m • (c / z) = c / z := by
    intro m
    induction m with
    | zero => rw [pow_zero, one_smul]
    | succ m ih => rw [pow_succ, mul_smul, hτw, ih]
  have hwK1 : c / z ∈ fixedModule A (K1 : Subgroup G) := by
    intro g hg
    obtain ⟨m, hm⟩ := hgen1 g hg
    have e : g = τ ^ m * ((τ ^ m)⁻¹ * g) := by group
    rw [e, mul_smul, hwL1 _ hm, hpw]

  have he1L : relRamificationIndex D.deg L L1 = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    exact hIL (Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hy).2, (Subgroup.mem_inf.1 hy).1⟩)
  have hvb1 : D.valuation L1 ⟨(b : A), hbL1⟩ = Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hL1L b.2, he1L, pow_one]
    exact hvb
  have hvτb : ∀ ν : ℕ, D.valuation L1 ⟨τ ^ ν • (b : A), hsmulL1 _ (K.pow_mem hτK ν) _ hbL1⟩ =
      Multiplicative.ofAdd 1 :=
    fun ν => (valuation_smul_of_map_eq L1 (hmapL1 _ (K.pow_mem hτK ν)) ⟨(b : A), hbL1⟩ _).trans hvb1
  have hvσx : D.valuation L1 ⟨s.elt • x, hσxL1⟩ = D.valuation L1 ⟨x, hxL1⟩ :=
    valuation_smul_of_map_eq L1 (hmapL1 _ s.mem) ⟨x, hxL1⟩ _
  have hweq : (⟨c / z, hwL1⟩ : fixedModule A (L1 : Subgroup G)) =
      (∏ ν : Fin k, (⟨τ ^ (ν : ℕ) • (b : A), hsmulL1 _ (K.pow_mem hτK _) _ hbL1⟩ :
        fixedModule A (L1 : Subgroup G))) /
        ((⟨x, hxL1⟩ : fixedModule A (L1 : Subgroup G)) / ⟨s.elt • x, hσxL1⟩) := by
    ext
    simp [hcdef, hzdef]
  have hvw : D.valuation L1 ⟨c / z, hwL1⟩ = Multiplicative.ofAdd (k : ℤ̂) := by
    rw [hweq, map_div, map_div, map_prod, hvσx, div_self', div_one]
    simp only [hvτb, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ofAdd_nsmul, nsmul_one]

  have hval := D.valuation_of_mem hL1K1 hwK1
  rw [hvw] at hval
  have he1 : 0 < relRamificationIndex D.deg K1 L1 :=
    Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero
  have hk : ((k : ℤ) : ℤ̂) =
      relRamificationIndex D.deg K1 L1 • Multiplicative.toAdd (D.valuation K1 ⟨c / z, hwK1⟩) := by
    have h := congrArg Multiplicative.toAdd hval
    rw [toAdd_ofAdd, toAdd_pow] at h
    rw [Int.cast_natCast]
    exact h
  have hdvd : relRamificationIndex D.deg K1 L1 ∣ k :=
    Int.natCast_dvd_natCast.1 (dvd_of_intCast_eq_nsmul he1 hk)

  have hNker : ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G))).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hconj g (hK1K (Subgroup.mem_inf.1 g.2).2) n hn⟩
  have hτe : τ ^ relRamificationIndex D.deg K1 L1 ∈ (L1 : Subgroup G) := by
    have h := Subgroup.pow_index_mem ((L1 : Subgroup G).subgroupOf (D.deg.ker ⊓ (K1 : Subgroup G)))
      (⟨τ, Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hτker, hτK1⟩⟩ :
        (D.deg.ker ⊓ (K1 : Subgroup G) : Subgroup G))
    rw [Subgroup.mem_subgroupOf, SubgroupClass.coe_pow] at h
    exact h
  obtain ⟨j, hj⟩ := hdvd
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, SubgroupClass.coe_pow, hj, pow_mul]
  exact hL1L (Subgroup.pow_mem _ hτe j)

theorem reciprocity_bijective_of_totallyRamified
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
    (htot : relInertiaDegree D.deg K L = 1) : Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Subgroup.FiniteIndex.index_ne_zero)
  refine (reciprocity_injective_of_totallyRamified hLK hax hcyc htot).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl

end TotallyRamified

section Cyclic

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_surjective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity hLK hax) := by

  obtain ⟨M, hLM, hMK, huM, htotM⟩ : ∃ M : OpenSubgroup G, L ≤ M ∧ M ≤ K ∧
      (K : Subgroup G) ⊓ D.deg.ker ≤ M ∧ relInertiaDegree D.deg M L = 1 :=
    ⟨D.maxUnramified K L, le_maxUnramified hLK, maxUnramified_le, inf_ker_le_maxUnramified,
      relInertiaDegree_maxUnramified⟩
  have hNM : ((L : Subgroup G).subgroupOf M).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      have h := (inferInstance : ((L : Subgroup G).subgroupOf K).Normal).conj_mem ⟨n, hMK n.2⟩
        (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h⟩

  have hcycM : IsCyclic ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) := by
    have := hcyc
    refine isCyclic_of_injective
      (QuotientGroup.map ((L : Subgroup G).subgroupOf M) ((L : Subgroup G).subgroupOf K)
        (Subgroup.inclusion (fun x hx => hMK hx)) ?_) ?_
    · intro x hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_subgroupOf] at hx
      exact hx
    · rw [injective_iff_map_eq_one]
      intro q hq
      induction q using QuotientGroup.induction_on with
      | H g =>
        rw [QuotientGroup.map_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hq
  have hbijLM := reciprocity_bijective_of_totallyRamified hLM hax hcycM htotM

  obtain ⟨φ0, hφ0K, hdφ0⟩ := D.exists_deg_eq K
  obtain ⟨s1, hs1⟩ : ∃ s1 : D.FrobeniusLift K, s1.deg = 1 :=
    ⟨FrobeniusLift.ofDegOne hφ0K hdφ0, rfl⟩
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s1.field L hLK)
  have hr1 := reciprocity_mk_eq_norm hLK hax s1 hπ1
  have hvc : D.valuation K (norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1) =
      Multiplicative.ofAdd 1 := by
    rw [valuation_norm_prime hLK s1 hπ1, hs1, Nat.cast_one]
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>

    obtain ⟨j, hj⟩ : ∃ j : ℕ, (j : ZMod (D.relInertiaDegreePNat hMK)) =
        proj (D.relInertiaDegreePNat hMK) (Multiplicative.toAdd (D.valuation K a)) :=
      ⟨_, ZMod.natCast_zmod_val _⟩
    have hker : D.tateZeroVal hMK ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, map_div, map_pow, hvc, toAdd_div, toAdd_pow,
        toAdd_ofAdd, nsmul_one, map_sub, map_natCast, hj, sub_self, ofAdd_zero]
    have h0 : ((a / norm A (K : Subgroup G) (s1.field L hLK : Subgroup G) π1 ^ j :
        fixedModule A (K : Subgroup G)) : tateZero A (K : Subgroup G) (M : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hMK huM).1 (by rw [hker, map_one])
    obtain ⟨a0, ha0⟩ := (QuotientGroup.eq_one_iff _).1 h0

    obtain ⟨q, hq⟩ := hbijLM.2 (a0 : tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLM q
    obtain ⟨π2, hπ2⟩ := D.exists_prime (s.field L hLM)
    rw [reciprocity_mk_eq_norm hLM hax s hπ2, QuotientGroup.eq] at hq
    obtain ⟨b, hb⟩ := hq

    let s' : D.FrobeniusLift K :=
      { elt := s.elt
        mem := hMK s.mem
        deg := s.deg * relInertiaDegree D.deg K M
        deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hMK))
        deg_eq := by
          rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
            (L := (M : Subgroup G)) (fun x hx => hMK hx), mul_assoc] }
    have hr' := reciprocity_mk_eq_norm hLK hax s' (π := π2) hπ2
    have hnn : norm A (K : Subgroup G) (M : Subgroup G)
        (norm A (M : Subgroup G) (s.field L hLM : Subgroup G) π2) =
          norm A (K : Subgroup G) (s.field L hLM : Subgroup G) π2 :=
      norm_norm (fun x hx => s.field_le hLM hx) (fun x hx => hMK hx) π2
    refine ⟨((⟨s'.elt, s'.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) *
      ((⟨s1.elt, s1.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ j, ?_⟩
    rw [map_mul, map_pow, hr', hr1, ← QuotientGroup.mk_pow, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    refine ⟨b, ?_⟩
    have h1 := congrArg (norm A (K : Subgroup G) (M : Subgroup G)) hb
    rw [norm_norm (fun x hx => hLM hx) (fun x hx => hMK hx), map_mul, map_inv, hnn, ha0] at h1
    rw [h1, div_eq_mul_inv, mul_inv_rev]
    ac_rfl

theorem reciprocity_bijective_of_isCyclic
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Bijective (D.reciprocity hLK hax) := by
  have hcard := (hax K L hLK hcyc).1
  refine (reciprocity_surjective_of_isCyclic hLK hax hcyc).bijective_of_nat_card_le ?_
  rw [hcard]
  exact le_rfl

variable (D) in

noncomputable def reciprocityEquiv
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K ≃* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc)

end Cyclic

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Normal

variable {G : Type*} [Group G]

theorem normal_subgroupOf_of_le {K L M : Subgroup G} (hMK : M ≤ K) [hN : (L.subgroupOf K).Normal] :
    (L.subgroupOf M).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h := hN.conj_mem ⟨n, hMK n.2⟩ (by rw [Subgroup.mem_subgroupOf]; exact hn) ⟨g, hMK g.2⟩
    rw [Subgroup.mem_subgroupOf] at h
    simpa using h⟩

theorem card_quotient_eq_relIndex (K L : Subgroup G) :
    Nat.card (K ⧸ L.subgroupOf K) = L.relIndex K :=
  (Subgroup.index_eq_card _).symm

end Normal

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

def fixedOpen (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G where
  toSubgroup := (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G)) (fun x hx => ⟨⟨x, hLK hx⟩, by
      show ((⟨x, hLK hx⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H
      rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
      exact H.one_mem, rfl⟩) L.isOpen

theorem mem_fixedOpen {H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)} {g : G} :
    g ∈ ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ↔
      ∃ h : g ∈ (K : Subgroup G), ((⟨g, h⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈ H := by
  show g ∈ (H.comap (QuotientGroup.mk' _)).map (K : Subgroup G).subtype ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k.2, hk⟩
  · rintro ⟨h, hH⟩
    exact ⟨⟨g, h⟩, hH, rfl⟩

variable (H : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))

theorem le_fixedOpen : L ≤ fixedOpen hLK H := fun x hx =>
  (mem_fixedOpen hLK).2 ⟨hLK hx, by
    rw [(QuotientGroup.eq_one_iff (⟨x, hLK hx⟩ : (K : Subgroup G))).2 (Subgroup.mem_subgroupOf.2 hx)]
    exact H.one_mem⟩

theorem fixedOpen_le : fixedOpen hLK H ≤ K := fun _ hx => ((mem_fixedOpen hLK).1 hx).1

instance normal_fixedOpen_self :
    ((L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)).Normal :=
  normal_subgroupOf_of_le (K := (K : Subgroup G)) (fun _ hx => ((mem_fixedOpen hLK).1 hx).1)

instance normal_fixedOpen [hH : H.Normal] :
    (((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).subgroupOf K).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨_, hnH⟩ := (mem_fixedOpen hLK).1 hn
    refine (mem_fixedOpen hLK).2 ⟨(g * n * g⁻¹).2, ?_⟩
    exact hH.conj_mem _ hnH (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)⟩

theorem range_galRestrict_fixedOpen [CompactSpace G] :
    (galRestrict (K := K) (L := L) (K' := fixedOpen hLK H) (L' := L) (fixedOpen_le hLK H)
      le_rfl).range = H := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [mk_mem_range_galRestrict_iff (le_fixedOpen hLK H) (fixedOpen_le hLK H), mem_fixedOpen]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨k.2, h⟩⟩

noncomputable def galFixedEquiv [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ⧸
      (L : Subgroup G).subgroupOf ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G) ≃* H :=
  (MonoidHom.ofInjective (galRestrict_injective (K := K) (L := L) (fixedOpen_le hLK H))).trans
    (MulEquiv.subgroupCongr (range_galRestrict_fixedOpen hLK H))

theorem relIndex_fixedOpen [CompactSpace G] :
    (L : Subgroup G).relIndex (fixedOpen hLK H) = Nat.card H := by
  rw [← card_quotient_eq_relIndex]
  exact Nat.card_congr (galFixedEquiv hLK H).toEquiv

theorem relIndex_fixedOpen_eq_index [CompactSpace G] :
    ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G).relIndex K = H.index := by
  have h1 := Subgroup.relIndex_mul_relIndex (H := (L : Subgroup G))
    (K := ((fixedOpen hLK H : OpenSubgroup G) : Subgroup G)) (L := (K : Subgroup G))
    (fun x hx => le_fixedOpen hLK H hx) (fun x hx => fixedOpen_le hLK H hx)
  rw [relIndex_fixedOpen, ← card_quotient_eq_relIndex (K : Subgroup G) (L : Subgroup G),
    ← H.card_mul_index] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

end FixedField

section Restrict

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_surjective {K L M : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((M : Subgroup G).subgroupOf K).Normal] (hLM : L ≤ M) :
    Function.Surjective (galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H τ => exact ⟨(τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K), rfl⟩

omit [CompactSpace G] in

theorem conjOpen_eq_of_normal {K M : OpenSubgroup G} (hMK : M ≤ K)
    [((M : Subgroup G).subgroupOf K).Normal] {g : G} (hg : g ∈ (K : Subgroup G)) :
    conjOpen g M = M := by
  have h := map_conj_eq_of_normal (L := (M : Subgroup G)) (fun _ hy => hMK hy) hg
  apply OpenSubgroup.ext
  intro x
  show x ∈ ((conjOpen g M : OpenSubgroup G) : Subgroup G) ↔ x ∈ (M : Subgroup G)
  rw [coe_conjOpen, h]

theorem Abelianization.lift_injective_of_ker_le {Γ T : Type*} [Group Γ] [CommGroup T] (f : Γ →* T)
    (h : f.ker ≤ commutator Γ) : Function.Injective (Abelianization.lift f) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  induction z using QuotientGroup.induction_on with
  | H q =>
    have hq : Abelianization.lift f (Abelianization.of q) = 1 := hz
    rw [Abelianization.lift_apply_of] at hq
    have := h hq
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at this
    exact this

end Restrict

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_congr {K₁ K₂ L₁ L₂ : OpenSubgroup G} (hK : K₁ = K₂) (hL : L₁ = L₂)
    (h1 : L₁ ≤ K₁) (h2 : L₂ ≤ K₂) [((L₁ : Subgroup G).subgroupOf K₁).Normal]
    [((L₂ : Subgroup G).subgroupOf K₂).Normal] {τ : G} (hτ1 : τ ∈ (K₁ : Subgroup G))
    (hτ2 : τ ∈ (K₂ : Subgroup G)) {a : A} (ha1 : a ∈ fixedModule A (K₁ : Subgroup G))
    (ha2 : a ∈ fixedModule A (K₂ : Subgroup G))
    (h : D.reciprocity h1 hax ((⟨τ, hτ1⟩ : (K₁ : Subgroup G)) :
        (K₁ : Subgroup G) ⧸ (L₁ : Subgroup G).subgroupOf K₁) =
      ((⟨a, ha1⟩ : fixedModule A (K₁ : Subgroup G)) : tateZero A (K₁ : Subgroup G) (L₁ : Subgroup G))) :
    D.reciprocity h2 hax ((⟨τ, hτ2⟩ : (K₂ : Subgroup G)) :
        (K₂ : Subgroup G) ⧸ (L₂ : Subgroup G).subgroupOf K₂) =
      ((⟨a, ha2⟩ : fixedModule A (K₂ : Subgroup G)) : tateZero A (K₂ : Subgroup G) (L₂ : Subgroup G)) := by
  subst hK hL
  exact h

section Tower

variable {K M L : OpenSubgroup G} (hLM : L ≤ M) (hMK : M ≤ K)
  [((L : Subgroup G).subgroupOf K).Normal] [((L : Subgroup G).subgroupOf M).Normal]
  [((M : Subgroup G).subgroupOf K).Normal]

theorem reciprocity_surjective_of_tower (h1 : Function.Surjective (D.reciprocity hLM hax))
    (h2 : Function.Surjective (D.reciprocity hMK hax)) :
    Function.Surjective (D.reciprocity (hLM.trans hMK) hax) := by
  have hLK : L ≤ K := hLM.trans hMK
  intro x
  induction x using QuotientGroup.induction_on with
  | H a =>
    obtain ⟨q', hq'⟩ := h2 (a : tateZero A (K : Subgroup G) (M : Subgroup G))
    obtain ⟨q, rfl⟩ := galRestrict_surjective (K := K) hLM q'
    have e1 := D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (D.reciprocity hLK hax q)
    rw [hq', ← hc, normTateZero_mk, norm_self, MonoidHom.id_apply, QuotientGroup.eq] at e1
    obtain ⟨b, hb⟩ := e1
    obtain ⟨p, hp⟩ := h1 ((b⁻¹ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    have e2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl p
    refine ⟨q * galRestrict hMK le_rfl p, ?_⟩
    rw [map_mul, e2, hp, ← hc, normTateZero_mk, map_inv, hb, ← QuotientGroup.mk_mul]
    congr 1
    group

theorem ker_reciprocity_le_of_tower
    (hcyc : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K))
    (hs : Function.Surjective (D.reciprocity hLM hax))
    (hk : (D.reciprocity hLM hax).ker ≤ commutator ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)) :
    (D.reciprocity (hLM.trans hMK) hax).ker ≤
      commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  have hLK : L ≤ K := hLM.trans hMK
  have hMK' : (M : Subgroup G) ≤ K := fun _ hx => hMK hx
  have hLM' : (L : Subgroup G) ≤ M := fun _ hx => hLM hx
  have hLK' : (L : Subgroup G) ≤ K := fun _ hx => hLK hx
  set ι := galRestrict (K := K) (L := L) (K' := M) (L' := L) hMK le_rfl with hι
  set S := (commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).comap ι with hS

  have hconj : ∀ (g : G) (hg : g ∈ (K : Subgroup G)) (τ : G) (hτ : τ ∈ (M : Subgroup G)) (x : A)
      (hx : x ∈ fixedModule A (M : Subgroup G)),
      D.reciprocity hLM hax ((⟨τ, hτ⟩ : (M : Subgroup G)) :
          (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) →
      D.reciprocity hLM hax ((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' hτ) hτ⟩ :
          (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) =
        ((⟨g • x, smul_mem_fixedModule_of_normal hMK' hg hx⟩ : fixedModule A (M : Subgroup G)) :
          tateZero A (M : Subgroup G) (L : Subgroup G)) := by
    intro g hg τ hτ x hx h
    have e := D.reciprocity_galConj hax g hLM
      ((⟨τ, hτ⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M)
    rw [galConj_mk, h, tateZeroConj_mk] at e
    exact D.reciprocity_congr hax (conjOpen_eq_of_normal hMK hg) (conjOpen_eq_of_normal hLK hg)
      (conjOpen_mono g hLM) hLM _ _ (a := g • x) _ _ e
  intro q hq
  rw [MonoidHom.mem_ker] at hq

  have hq1 : galRestrict (K := K) (L := M) (K' := K) (L' := L) le_rfl hLM q = 1 := by
    apply (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcyc).1
    rw [map_one, D.reciprocity_galRestrict hax hMK hLK le_rfl hLM q, hq, map_one]
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
  set t : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M :=
    ((⟨k, hq1⟩ : (M : Subgroup G)) : (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) with ht
  have hιt : ι t = QuotientGroup.mk k := rfl
  rw [← hιt] at hq ⊢

  have h2 := D.reciprocity_galRestrict hax hLK hLM hMK le_rfl t
  rw [hq] at h2
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hLM hax t)
  rw [← ha, normTateZero_mk] at h2
  obtain ⟨b, hb⟩ := (QuotientGroup.eq_one_iff _).1 h2.symm
  set a' : fixedModule A (M : Subgroup G) := a * (norm A (M : Subgroup G) (L : Subgroup G) b)⁻¹
    with ha'def
  have ha' : norm A (K : Subgroup G) (M : Subgroup G) a' = 1 := by
    rw [ha'def, map_mul, map_inv, norm_norm hLM' hMK' b, hb, mul_inv_cancel]
  have hmk : (QuotientGroup.mk a' : tateZero A (M : Subgroup G) (L : Subgroup G)) =
      D.reciprocity hLM hax t := by
    rw [← ha, QuotientGroup.eq]
    exact ⟨b, by rw [ha'def]; group⟩

  have hsub : Subsingleton (tateNegOne A (K : Subgroup G) (M : Subgroup G)) :=
    (Nat.card_eq_one_iff_unique.1 (hax K M hMK hcyc).2).1
  have haug : (a' : A) ∈ augmentation A (K : Subgroup G) (M : Subgroup G) := by
    have h0 : ((⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker) :
        tateNegOne A (K : Subgroup G) (M : Subgroup G)) = 1 := Subsingleton.elim _ _
    exact (QuotientGroup.eq_one_iff
      (⟨a', ha'⟩ : (norm A (K : Subgroup G) (M : Subgroup G)).ker)).1 h0

  set P : Subgroup A := ((S.map (D.reciprocity hLM hax)).comap
    (QuotientGroup.mk' (norm A (M : Subgroup G) (L : Subgroup G)).range)).map
      (fixedModule A (M : Subgroup G)).subtype with hP
  have hAP : augmentation A (K : Subgroup G) (M : Subgroup G) ≤ P := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, x, hx, rfl⟩
    obtain ⟨ρ, hρ⟩ := hs ((⟨x, hx⟩ : fixedModule A (M : Subgroup G)) :
      tateZero A (M : Subgroup G) (L : Subgroup G))
    obtain ⟨τ, rfl⟩ := QuotientGroup.mk_surjective ρ
    have e := hconj g hg τ τ.2 x hx hρ
    refine ⟨⟨g • x / x, (fixedModule A (M : Subgroup G)).div_mem
      (smul_mem_fixedModule_of_normal hMK' hg hx) hx⟩, ?_, rfl⟩
    refine ⟨((⟨g * τ * g⁻¹, conj_mem_of_normal hg (hMK' τ.2) τ.2⟩ : (M : Subgroup G)) :
      (M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) * (τ : (M : Subgroup G) ⧸ _)⁻¹, ?_, ?_⟩
    · show ι (_ * _) ∈ commutator _
      rw [map_mul, map_inv]
      have hc := Subgroup.commutator_mem_commutator
        (Subgroup.mem_top ((⟨g, hg⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
        (Subgroup.mem_top ((⟨τ, hMK' τ.2⟩ : (K : Subgroup G)) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))
      rw [commutatorElement_def] at hc
      exact hc
    · rw [map_mul, map_inv, e, hρ, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
        QuotientGroup.mk'_apply]
      congr 1
      exact Subtype.ext (div_eq_mul_inv _ _).symm
  obtain ⟨y, hy, hya⟩ := hAP haug
  obtain rfl : y = a' := Subtype.ext hya
  obtain ⟨s, hsS, hrs⟩ := hy
  rw [QuotientGroup.mk'_apply, hmk] at hrs
  have hts : t * s⁻¹ ∈ (D.reciprocity hLM hax).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, mul_inv_cancel]
  have hcomm : ι (t * s⁻¹) ∈ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
    have h := hk hts
    rw [← Abelianization.ker_of, MonoidHom.mem_ker] at h ⊢
    rw [← Abelianization.map_of, h, map_one]
  have e3 : ι t = ι (t * s⁻¹) * ι s := by rw [map_mul, map_inv, inv_mul_cancel_right]
  rw [e3]
  exact Subgroup.mul_mem _ hcomm hsS

end Tower

section PGroup

theorem reciprocity_of_isPGroup {p : ℕ} [hp : Fact p.Prime] (n : ℕ) :
    ∀ {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal],
      (L : Subgroup G).relIndex K = n →
      IsPGroup p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →
      Function.Surjective (D.reciprocity hLK hax) ∧
        (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro K L hLK _ hn hP
  by_cases hcyc : IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  · have hb := reciprocity_bijective_of_isCyclic (D := D) hLK hax hcyc
    refine ⟨hb.2, fun q hq => ?_⟩
    rw [(injective_iff_map_eq_one _).1 hb.1 q hq]
    exact Subgroup.one_mem _
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hcyc (@isCyclic_of_subsingleton _ _ (Nat.card_eq_one_iff_unique.1 hk).1)

  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p
    (pow_dvd_pow p (Nat.sub_le k 1) |>.trans hk.symm.dvd)
  have hpk : p ^ (k - 1) * p = p ^ k := by rw [← pow_succ, Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)]
  have hHi : H.index = p := by
    have h := H.card_mul_index
    rw [hH, hk, ← hpk] at h
    exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.out.pos _) h
  have hmin : (p ^ k).minFac = p := by
    have h2 : (p ^ k).minFac.Prime := Nat.minFac_prime (Nat.one_lt_pow hk0 hp.out.one_lt).ne'
    exact (Nat.prime_dvd_prime_iff_eq h2 hp.out).1 (h2.dvd_of_dvd_pow (Nat.minFac_dvd _))
  have hHn : H.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hHi, hk, hmin])
  set M := fixedOpen hLK H with hM
  have hLM : L ≤ M := le_fixedOpen hLK H
  have hMK : M ≤ K := fixedOpen_le hLK H

  have hcycM : IsCyclic ((K : Subgroup G) ⧸ (M : Subgroup G).subgroupOf K) :=
    isCyclic_of_prime_card (p := p) (by
      rw [card_quotient_eq_relIndex, hM, relIndex_fixedOpen_eq_index, hHi])

  have hPM : IsPGroup p ((M : Subgroup G) ⧸ (L : Subgroup G).subgroupOf M) :=
    (hP.to_subgroup H).of_equiv (galFixedEquiv hLK H).symm
  have hLMn : (L : Subgroup G).relIndex M = p ^ (k - 1) := by
    rw [hM, relIndex_fixedOpen, hH]
  have hlt : p ^ (k - 1) < n := by
    rw [← hn, ← card_quotient_eq_relIndex, hk]
    exact Nat.pow_lt_pow_right hp.out.one_lt (Nat.sub_lt (Nat.pos_of_ne_zero hk0) one_pos)
  obtain ⟨hs, hker⟩ := ih _ hlt hLM hLMn hPM
  exact ⟨D.reciprocity_surjective_of_tower hax hLM hMK hs
      (reciprocity_bijective_of_isCyclic (D := D) hMK hax hcycM).2,
    D.ker_reciprocity_le_of_tower hax hLM hMK hcycM hs hker⟩

end PGroup

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger MulAction

section Transfer

theorem transfer_of_comp_subtype {Γ : Type*} [Group Γ] (H : Subgroup Γ) [H.FiniteIndex] (g : Γ) :
    ((Abelianization.of : Γ →* Abelianization Γ).comp H.subtype).transfer g =
      Abelianization.of g ^ H.index :=
  _root_.UpperTheory.Reformulated.B.Qe30.transfer_of_comp_subtype H g

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

theorem map_verlagerung {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L : Subgroup G).subgroupOf K').Normal] (hK'K : K' ≤ K)
    (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)
        (verlagerung hK'K g) =
      Abelianization.of g ^ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.index := by
  rw [verlagerung, map_transfer, ← transfer_of_comp_subtype]
  have e : (Abelianization.map (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom) =
      (Abelianization.of).comp
        (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range.subtype := by
    refine MonoidHom.ext fun h => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, Abelianization.map_of,
      MonoidHom.comp_apply, Subgroup.coe_subtype]
    congr 1
    have := congrArg Subtype.val
      ((MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).apply_symm_apply h)
    rw [MonoidHom.ofInjective_apply] at this
    exact this
  rw [e]

end Transfer

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

section General

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocity_fixedOpen_sylow {p : ℕ} [Fact p.Prime]
    (P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    Function.Surjective (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax) ∧
      (D.reciprocity (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) hax).ker ≤
        commutator (((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ⧸
          (L : Subgroup G).subgroupOf ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :=
  reciprocity_of_isPGroup hax _ (le_fixedOpen hLK _) rfl
    (P.isPGroup'.of_equiv (galFixedEquiv hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))).symm)

theorem reciprocity_surjective : Function.Surjective (D.reciprocity hLK hax) := by
  classical
  intro x
  by_contra hx
  set R := (D.reciprocity hLK hax).range with hR
  have hxR : x ∉ R := fun h => hx (MonoidHom.mem_range.1 h)
  set y : tateZero A (K : Subgroup G) (L : Subgroup G) ⧸ R := (x : _ ⧸ R) with hy
  have hy1 : y ≠ 1 := fun h => hxR ((QuotientGroup.eq_one_iff x).1 h)
  obtain ⟨p, hp, hpy⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 hy1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  have hMK : ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G) ≤ K :=
    fun _ h => fixedOpen_le hLK _ h
  obtain ⟨hs, -⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P

  have hyP : y ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index = 1 := by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨t, ht⟩ := hs ((⟨a, fixedModule_anti hMK a.2⟩ :
      fixedModule A ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)) :
        tateZero A _ (L : Subgroup G))
    have e := D.reciprocity_galRestrict hax hLK (le_fixedOpen hLK _) (fixedOpen_le hLK _) le_rfl t
    rw [ht, normTateZero_mk] at e
    have hn : norm A (K : Subgroup G) ((fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) : OpenSubgroup G) : Subgroup G)
        ⟨a, fixedModule_anti hMK a.2⟩ = a ^ (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)).index := by
      apply Subtype.ext
      rw [coe_norm_of_mem hMK a.2, relIndex_fixedOpen_eq_index, SubgroupClass.coe_pow]
    rw [hn, QuotientGroup.mk_pow] at e
    rw [hy, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact ⟨_, e⟩
  exact Sylow.not_dvd_index P (hpy.trans (orderOf_dvd_of_pow_eq_one hyP))

theorem ker_reciprocity_le_commutator :
    (D.reciprocity hLK hax).ker ≤ commutator ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  classical
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ
  rw [← Abelianization.ker_of, MonoidHom.mem_ker]
  by_contra h1
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (mt orderOf_eq_one_iff.1 h1)
  have := Fact.mk hp
  let P : Sylow p ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := Classical.arbitrary _
  obtain ⟨-, hk⟩ := reciprocity_fixedOpen_sylow (D := D) hLK hax P
  have hinj := Abelianization.lift_injective_of_ker_le _ hk
  have hv := D.reciprocity_verlagerung hax (le_fixedOpen hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)))
    (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hσ, map_one] at hv
  have hv1 : verlagerung (L := L) (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ = 1 :=
    hinj (by rw [hv, map_one])
  have hmap := map_verlagerung (fixedOpen_le hLK (P : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K))) σ
  rw [hv1, map_one, range_galRestrict_fixedOpen] at hmap
  exact Sylow.not_dvd_index P (hpd.trans (orderOf_dvd_of_pow_eq_one hmap.symm))


variable (D) in

noncomputable def reciprocityAb :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) →*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  Abelianization.lift (D.reciprocity hLK hax)

theorem reciprocityAb_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAb hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  Abelianization.lift_apply_of _ q

theorem reciprocityAb_bijective : Function.Bijective (D.reciprocityAb hLK hax) := by
  refine ⟨Abelianization.lift_injective_of_ker_le _ (ker_reciprocity_le_commutator hLK hax),
    fun x => ?_⟩
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax x
  exact ⟨Abelianization.of q, hq⟩

variable (D) in

noncomputable def reciprocityAbEquiv :
    Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ≃*
      tateZero A (K : Subgroup G) (L : Subgroup G) :=
  MulEquiv.ofBijective _ (reciprocityAb_bijective (D := D) hLK hax)

theorem reciprocityAbEquiv_apply (z : Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :
    D.reciprocityAbEquiv hLK hax z = D.reciprocityAb hLK hax z :=
  rfl

theorem reciprocityAbEquiv_of (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocityAbEquiv hLK hax (Abelianization.of q) = D.reciprocity hLK hax q :=
  reciprocityAb_of hLK hax q

include hLK hax in

theorem card_tateZero (D : ClassFieldData G A) :
    Nat.card (tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Nat.card (Abelianization ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) :=
  (Nat.card_congr (D.reciprocityAbEquiv hLK hax).toEquiv).symm

theorem reciprocity_bijective_of_isMulCommutative
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] :
    Function.Bijective (D.reciprocity hLK hax) := by
  refine ⟨?_, reciprocity_surjective hLK hax⟩
  rw [injective_iff_map_eq_one]
  intro q hq
  have h := ker_reciprocity_le_commutator (D := D) hLK hax hq
  rw [commutator, Subgroup.commutator_eq_bot_iff_le_centralizer.2 (fun x _ y _ => mul_comm' y x)] at h
  exact h

end General

section Squares

variable (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAb_map_galRestrict {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (z : Abelianization ((K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K')) :
    D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) z) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax z) := by
  induction z using QuotientGroup.induction_on with
  | H q =>
    show D.reciprocityAb hLK hax (Abelianization.map (galRestrict hK hL) (Abelianization.of q)) =
      normTateZero hK hL hL'K' hLK (D.reciprocityAb hL'K' hax (Abelianization.of q))
    rw [Abelianization.map_of, reciprocityAb_of, reciprocityAb_of,
      D.reciprocity_galRestrict hax hLK hL'K' hK hL q]

theorem reciprocityAbEquiv_symm_normTateZero {K L K' L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K' : L' ≤ K')
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (x : tateZero A (K' : Subgroup G) (L' : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (normTateZero hK hL hL'K' hLK x) =
      Abelianization.map (galRestrict hK hL) ((D.reciprocityAbEquiv hL'K' hax).symm x) := by
  rw [MulEquiv.symm_apply_eq]
  obtain ⟨z, rfl⟩ := (D.reciprocityAbEquiv hL'K' hax).surjective x
  rw [MulEquiv.symm_apply_apply, reciprocityAbEquiv_apply, reciprocityAbEquiv_apply,
    reciprocityAb_map_galRestrict]



end Squares

section Unramified

variable {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
  (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

theorem reciprocityAbEquiv_symm_of_unramified (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^
        (proj (D.relInertiaDegreePNat hLK) (Multiplicative.toAdd (D.valuation K a))).val := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_pow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_pow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, toAdd_ofAdd,
    map_one, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]

theorem reciprocityAbEquiv_symm_of_unramified_of_valuation (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1)
    (a : fixedModule A (K : Subgroup G)) (m : ℤ)
    (ha : D.valuation K a = Multiplicative.ofAdd (m : ℤ̂)) :
    (D.reciprocityAbEquiv hLK hax).symm (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      Abelianization.of (φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ m := by
  obtain ⟨π, hπ⟩ := D.exists_prime K
  rw [MulEquiv.symm_apply_eq, map_zpow, reciprocityAbEquiv_of,
    reciprocity_frobenius_of_unramified hLK hax hu hφ hπ]
  apply (D.tateZeroVal_bijective hax hLK hu).1
  rw [map_zpow, tateZeroVal_mk, tateZeroVal_mk, valuationMod_apply, valuationMod_apply, hπ, ha,
    toAdd_ofAdd, toAdd_ofAdd, map_one, map_intCast, ← ofAdd_zsmul, zsmul_one]

end Unramified

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

section Abelian

variable {G : Type*} [Group G] [TopologicalSpace G]

def IsAbelianExtension (K L : OpenSubgroup G) : Prop :=
  L ≤ K ∧ commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K

variable {K L : OpenSubgroup G}

theorem IsAbelianExtension.le (h : IsAbelianExtension K L) : L ≤ K :=
  h.1

theorem IsAbelianExtension.commutator_le (h : IsAbelianExtension K L) :
    commutator (K : Subgroup G) ≤ (L : Subgroup G).subgroupOf K :=
  h.2

theorem IsAbelianExtension.normal (h : IsAbelianExtension K L) :
    ((L : Subgroup G).subgroupOf K).Normal :=
  Subgroup.Normal.of_commutator_le _ h.2

theorem IsAbelianExtension.isMulCommutative (h : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  Subgroup.Normal.quotient_commutative_iff_commutator_le.2 h.2

theorem isAbelianExtension_of_isMulCommutative (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    [IsMulCommutative ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)] : IsAbelianExtension K L :=
  ⟨hLK, Subgroup.Normal.quotient_commutative_iff_commutator_le.1 inferInstance⟩

theorem IsAbelianExtension.mono {H : OpenSubgroup G} (h : IsAbelianExtension K L) (hLH : L ≤ H)
    (hHK : H ≤ K) : IsAbelianExtension K H :=
  ⟨hHK, fun _ hx => hLH (h.2 hx)⟩

theorem IsAbelianExtension.inf {L' : OpenSubgroup G} (h : IsAbelianExtension K L)
    (h' : IsAbelianExtension K L') : IsAbelianExtension K (L ⊓ L') :=
  ⟨inf_le_left.trans h.le, fun _ hx => ⟨h.2 hx, h'.2 hx⟩⟩

theorem isAbelianExtension_self (K : OpenSubgroup G) : IsAbelianExtension K K :=
  ⟨le_rfl, fun x _ => x.2⟩

variable [IsTopologicalGroup G]

def maxAbelian (hLK : L ≤ K) : OpenSubgroup G where
  toSubgroup :=
    ((L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G)).map (K : Subgroup G).subtype
  isOpen' := Subgroup.isOpen_mono (H₁ := (L : Subgroup G))
    (fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩) L.isOpen

theorem mem_maxAbelian (hLK : L ≤ K) (x : (K : Subgroup G)) :
    (x : G) ∈ (maxAbelian hLK : Subgroup G) ↔
      x ∈ (L : Subgroup G).subgroupOf K ⊔ commutator (K : Subgroup G) :=
  Subgroup.mem_map_iff_mem Subtype.val_injective

theorem maxAbelian_le (hLK : L ≤ K) : maxAbelian hLK ≤ K :=
  fun _ ⟨x, _, hx⟩ => hx ▸ x.2

theorem le_maxAbelian (hLK : L ≤ K) : L ≤ maxAbelian hLK :=
  fun x hx => ⟨⟨x, hLK hx⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hx), rfl⟩

theorem isAbelianExtension_maxAbelian (hLK : L ≤ K) : IsAbelianExtension K (maxAbelian hLK) :=
  ⟨maxAbelian_le hLK, fun x hx => (mem_maxAbelian hLK x).2 (Subgroup.mem_sup_right hx)⟩

end Abelian

section NormGroup

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  (A : Type*) [CommGroup A] [MulDistribMulAction G A]

noncomputable def normGroup (K L : OpenSubgroup G) : Subgroup (fixedModule A (K : Subgroup G)) :=
  (norm A (K : Subgroup G) (L : Subgroup G)).range

variable {A}

theorem normGroup_mono {K L H : OpenSubgroup G} (hLH : L ≤ H) (hHK : H ≤ K) :
    normGroup A K L ≤ normGroup A K H :=
  range_norm_le_range_norm hLH hHK

end NormGroup

theorem exists_openSubgroup_normal_le {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (L : OpenSubgroup G) :
    ∃ N : OpenSubgroup G, N ≤ L ∧ (N : Subgroup G).Normal := by
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one L.isOpen L.one_mem
  exact ⟨U.toOpenSubgroup, fun x hx => hU hx, U.isNormal'⟩

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A) (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]

section Reciprocity

variable {K L : OpenSubgroup G}

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
theorem mk_eq_one_iff [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔ (x : G) ∈ (L : Subgroup G) :=
  (QuotientGroup.eq_one_iff x).trans Subgroup.mem_subgroupOf

theorem exists_reciprocity_mk_eq (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (a : fixedModule A (K : Subgroup G)) :
    ∃ x : (K : Subgroup G),
      D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
        (a : tateZero A (K : Subgroup G) (L : Subgroup G)) := by
  obtain ⟨q, hq⟩ := reciprocity_surjective (D := D) hLK hax
    (a : tateZero A (K : Subgroup G) (L : Subgroup G))
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨x, hq⟩

theorem reciprocity_mk_of_le {L' : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (hL'K : L' ≤ K) [((L' : Subgroup G).subgroupOf K).Normal]
    (hLL' : L ≤ L') (x : (K : Subgroup G)) (a : fixedModule A (K : Subgroup G))
    (h : D.reciprocity hLK hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    D.reciprocity hL'K hax (x : (K : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L' : Subgroup G)) := by
  have e := D.reciprocity_galRestrict hax hL'K hLK le_rfl hLL'
    (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)
  rw [galRestrict_mk, h, normTateZero_mk, norm_self] at e
  exact e

theorem reciprocity_injective (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] : Function.Injective (D.reciprocity hL.le hax) :=
  haveI := hL.isMulCommutative
  (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax).1

theorem reciprocity_mk_eq_one_iff (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] (x : (K : Subgroup G)) :
    D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) = 1 ↔
      (x : G) ∈ (L : Subgroup G) := by
  rw [← mk_eq_one_iff, ← (D.reciprocity_injective hax hL).eq_iff, map_one]

theorem mem_normGroup_iff_of_reciprocity (hL : IsAbelianExtension K L)
    [((L : Subgroup G).subgroupOf K).Normal] {x : (K : Subgroup G)}
    {a : fixedModule A (K : Subgroup G)}
    (h : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      (a : tateZero A (K : Subgroup G) (L : Subgroup G))) :
    a ∈ normGroup A K L ↔ (x : G) ∈ (L : Subgroup G) := by
  rw [← D.reciprocity_mk_eq_one_iff hax hL, h, QuotientGroup.eq_one_iff]
  rfl

end Reciprocity

section Limitation

variable {K L : OpenSubgroup G}

include D hax

theorem normGroup_maxAbelian (hLK : L ≤ K) :
    normGroup A K (maxAbelian hLK) = normGroup A K L := by
  refine le_antisymm ?_ (normGroup_mono (le_maxAbelian hLK) (maxAbelian_le hLK))
  obtain ⟨N, hNL, hN⟩ := exists_openSubgroup_normal_le L
  have hNK : N ≤ K := hNL.trans hLK
  have hM := isAbelianExtension_maxAbelian hLK
  have := hM.normal
  have := hN
  rintro a ⟨m, rfl⟩
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hNK
    (norm A (K : Subgroup G) (maxAbelian hLK : Subgroup G) m)
  have hxM : (x : G) ∈ (maxAbelian hLK : Subgroup G) :=
    (D.mem_normGroup_iff_of_reciprocity hax hM
      (D.reciprocity_mk_of_le hax hNK hM.le (hNL.trans (le_maxAbelian hLK)) x _ hx)).1 ⟨m, rfl⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.1 ((mem_maxAbelian hLK x).1 hxM)

  have hz1 : D.reciprocity hNK hax (z : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) = 1 :=
    MonoidHom.mem_ker.1
      (Abelianization.commutator_subset_ker ((D.reciprocity hNK hax).comp (QuotientGroup.mk' _)) hz)

  obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (D.reciprocity hNL hax
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L))
  have e := D.reciprocity_galRestrict hax hNK hNL hLK le_rfl
    ((⟨y, hy⟩ : (L : Subgroup G)) : (L : Subgroup G) ⧸ (N : Subgroup G).subgroupOf L)
  rw [galRestrict_mk, ← hb, normTateZero_mk] at e
  have e' : D.reciprocity hNK hax (y : (K : Subgroup G) ⧸ (N : Subgroup G).subgroupOf K) =
      (norm A (K : Subgroup G) (L : Subgroup G) b : tateZero A (K : Subgroup G) (N : Subgroup G)) := e
  rw [QuotientGroup.mk_mul, map_mul, hz1, mul_one, e'] at hx
  obtain ⟨c, hc⟩ := QuotientGroup.eq.1 hx
  refine ⟨b * norm A (L : Subgroup G) (N : Subgroup G) c, ?_⟩
  rw [map_mul, norm_norm hNL hLK, hc, mul_inv_cancel_left]

end Limitation

section Correspondence

variable {K L L' : OpenSubgroup G}

include D hax

theorem normGroup_le_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L ≤ normGroup A K L' ↔ L ≤ L' := by
  refine ⟨fun h => ?_, fun h => normGroup_mono h hL'.le⟩
  have hI := hL.inf hL'
  have := hI.normal
  have := hL.normal
  have := hL'.normal
  intro g hg
  have hgK : g ∈ (K : Subgroup G) := hL.le hg
  obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (D.reciprocity hI.le hax
    ((⟨g, hgK⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ ((L ⊓ L' : OpenSubgroup G) : Subgroup G).subgroupOf K))
  have h1 := D.reciprocity_mk_of_le hax hI.le hL.le inf_le_left ⟨g, hgK⟩ a ha.symm
  have h2 := D.reciprocity_mk_of_le hax hI.le hL'.le inf_le_right ⟨g, hgK⟩ a ha.symm
  exact (D.mem_normGroup_iff_of_reciprocity hax hL' h2).1
    (h ((D.mem_normGroup_iff_of_reciprocity hax hL h1).2 hg))

theorem normGroup_eq_normGroup_iff (hL : IsAbelianExtension K L) (hL' : IsAbelianExtension K L') :
    normGroup A K L = normGroup A K L' ↔ L = L' := by
  rw [le_antisymm_iff, le_antisymm_iff, D.normGroup_le_normGroup_iff hax hL hL',
    D.normGroup_le_normGroup_iff hax hL' hL]

theorem normGroup_injective (K : OpenSubgroup G) :
    Function.Injective fun L : {L : OpenSubgroup G // IsAbelianExtension K L} => normGroup A K L :=
  fun L L' h => Subtype.ext ((D.normGroup_eq_normGroup_iff hax L.2 L'.2).1 h)

theorem exists_normGroup_eq_of_le_of_isAbelianExtension (hL : IsAbelianExtension K L)
    {B : Subgroup (fixedModule A (K : Subgroup G))} (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  have := hL.normal
  set Q : Subgroup ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
    (B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)).comap
      (D.reciprocity hL.le hax) with hQ
  have hH : IsAbelianExtension K (fixedOpen hL.le Q) :=
    hL.mono (le_fixedOpen hL.le Q) (fixedOpen_le hL.le Q)
  have := hH.normal
  refine ⟨fixedOpen hL.le Q, hH, le_fixedOpen hL.le Q, ?_⟩
  ext a
  obtain ⟨x, hx⟩ := D.exists_reciprocity_mk_eq hax hL.le a
  rw [D.mem_normGroup_iff_of_reciprocity hax hH
    (D.reciprocity_mk_of_le hax hL.le hH.le (le_fixedOpen hL.le Q) x a hx), mem_fixedOpen]
  constructor
  · rintro ⟨_, hq⟩
    have hq' : D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
        B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range) := hq
    rw [hx] at hq'
    obtain ⟨b, hbB, hba⟩ := Subgroup.mem_map.1 hq'
    obtain ⟨n, hn⟩ := QuotientGroup.eq.1 hba
    have ha : a = b * (b⁻¹ * a) := (mul_inv_cancel_left b a).symm
    rw [ha, ← hn]
    exact B.mul_mem hbB (hB ⟨n, rfl⟩)
  · intro ha
    refine ⟨x.2, ?_⟩
    show D.reciprocity hL.le hax (x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      B.map (QuotientGroup.mk' (norm A (K : Subgroup G) (L : Subgroup G)).range)
    rw [hx]
    exact ⟨a, ha, rfl⟩

theorem exists_normGroup_eq_of_le (hLK : L ≤ K) {B : Subgroup (fixedModule A (K : Subgroup G))}
    (hB : normGroup A K L ≤ B) :
    ∃ H : OpenSubgroup G, IsAbelianExtension K H ∧ L ≤ H ∧ normGroup A K H = B := by
  rw [← D.normGroup_maxAbelian hax hLK] at hB
  obtain ⟨H, hH, hMH, e⟩ :=
    D.exists_normGroup_eq_of_le_of_isAbelianExtension hax (isAbelianExtension_maxAbelian hLK) hB
  exact ⟨H, hH, (le_maxAbelian hLK).trans hMH, e⟩

theorem index_normGroup (hL : IsAbelianExtension K L) :
    (normGroup A K L).index = (L : Subgroup G).relIndex K := by
  have := hL.normal
  have := hL.isMulCommutative
  rw [Subgroup.index_eq_card, ← card_quotient_eq_relIndex]
  exact (Nat.card_congr
    (Equiv.ofBijective _ (reciprocity_bijective_of_isMulCommutative (D := D) hL.le hax))).symm

end Correspondence

end ClassFieldData

end GroundTheory.LocalField.Abstract
end
