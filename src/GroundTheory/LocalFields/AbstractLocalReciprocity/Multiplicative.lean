import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.UniqueQuotientSubgroupOfSelf
import GroundTheory.LocalFields.AbstractLocalReciprocity.Frobenius
import GroundTheory.LocalFields.AbstractLocalReciprocity.Valuation

section
namespace GroundTheory.LocalField.Abstract

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_of_le {K L : Subgroup G} (hKL : K ≤ L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) : (norm A K L a : A) = a := by
  have : Unique (K ⧸ L.subgroupOf K) :=
    { default := ((1 : K) : K ⧸ L.subgroupOf K)
      uniq := fun q => by
        induction q using QuotientGroup.induction_on with
        | H σ =>
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          exact hKL (by simp) }
  rw [coe_norm, finprod_eq_single _ ((1 : K) : K ⧸ L.subgroupOf K)
    (fun q hq => absurd (Subsingleton.elim q _) hq), cosetSMul_mk]
  simp

theorem coe_norm_congr {K K' L L' : Subgroup G} (hK : K = K') (hL : L = L')
    [(L.subgroupOf K).FiniteIndex] [(L'.subgroupOf K').FiniteIndex] (a : fixedModule A L) :
    (norm A K L a : A) = norm A K' L' ⟨a, hL ▸ a.2⟩ := by
  subst hK
  subst hL
  rfl

theorem smul_norm_of_map_eq {K L : Subgroup G} (g : G) (hK : K.map (MulAut.conj g).toMonoidHom = K)
    (hL : L.map (MulAut.conj g).toMonoidHom = L) [(L.subgroupOf K).FiniteIndex]
    (a : fixedModule A L) :
    g • (norm A K L a : A) = norm A K L ⟨g • (a : A), by
      have := smul_mem_fixedModule a.2 g
      rwa [hL] at this⟩ := by
  have : ((L.map (MulAut.conj g).toMonoidHom).subgroupOf
      (K.map (MulAut.conj g).toMonoidHom)).FiniteIndex := by
    rw [hK, hL]
    infer_instance
  rw [smul_norm g a, coe_norm_congr hK hL]

theorem coe_norm_eq_of_mul_eq {K S Q J : Subgroup G} (hQK : Q ≤ K)
    (hmul : ∀ k ∈ K, ∃ q ∈ Q, q⁻¹ * k ∈ S) (hJ : ∀ q ∈ Q, q ∈ S ↔ q ∈ J)
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf Q).FiniteIndex] (a : fixedModule A S)
    (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) = norm A Q J ⟨a, ha⟩ := by
  let f : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        have h' : ((⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) = ((⟨q', hQK q'.2⟩ : K) : K ⧸ _) := hxy
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at h'
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
        exact (hJ _ hq).1 (by simpa using h')
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨q, hq, hqk⟩ := hmul k k.2
        refine ⟨((⟨q, hq⟩ : Q) : Q ⧸ J.subgroupOf Q), ?_⟩
        show ((⟨q, hQK hq⟩ : K) : K ⧸ S.subgroupOf K) = _
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using hqk
  rw [coe_norm, coe_norm, ← finprod_comp_equiv (Equiv.ofBijective f hf)]
  congr 1
  funext x
  induction x using QuotientGroup.induction_on with
  | H q => rfl

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

section Unramified

variable {G : Type*} [Group G] (d : G →* Multiplicative ℤ̂)

def IsUnramified (K L : Subgroup G) : Prop :=
  relRamificationIndex d K L = 1

variable {d}

theorem isUnramified_iff {K L : Subgroup G} : IsUnramified d K L ↔ K ⊓ d.ker ≤ L := by
  rw [IsUnramified, relRamificationIndex, Subgroup.relIndex_eq_one, inf_comm]

theorem relIndex_eq_relInertiaDegree {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    L.relIndex K = relInertiaDegree d K L := by
  rw [relIndex_eq_mul (d := d) hLK, (isUnramified_iff.2 hu : relRamificationIndex d K L = 1), one_mul]

theorem mem_iff_map_mem_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L)
    {σ : G} (hσ : σ ∈ K) : σ ∈ L ↔ d σ ∈ L.map d := by
  refine ⟨fun h => ⟨σ, h, rfl⟩, ?_⟩
  rintro ⟨τ, hτ, hτσ⟩
  have h : τ⁻¹ * σ ∈ L := hu (Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem (hLK hτ)) hσ,
    MonoidHom.mem_ker.2 (by rw [map_mul, map_inv, hτσ, inv_mul_cancel])⟩)
  simpa using L.mul_mem hτ h

theorem normal_of_unramified {K L : Subgroup G} (hLK : L ≤ K) (hu : K ⊓ d.ker ≤ L) :
    (L.subgroupOf K).Normal := by
  have h : L.subgroupOf K = (L.map d).comap (d.comp K.subtype) := by
    ext σ
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, MonoidHom.comp_apply, Subgroup.coe_subtype]
    exact mem_iff_map_mem_of_unramified hLK hu σ.2
  rw [h]
  exact Subgroup.Normal.comap inferInstance _

end Unramified

namespace ClassFieldData

open ProfiniteInteger

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] (D : ClassFieldData G A)

section Frobenius

variable {K L : OpenSubgroup G}

theorem exists_pow_mul_mem_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) (τ : (K : Subgroup G)) :
    ∃ m : ℕ, ((φ ^ m)⁻¹ * τ : G) ∈ (L : Subgroup G) := by
  set n : ℕ+ := ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩
  set x : ℤ̂ := Multiplicative.toAdd (D.relDeg K τ)
  set m : ℕ := (proj n x).val
  have hx : x - (m : ℤ̂) ∈ multiples n := by
    rw [← proj_eq_zero_iff, map_sub, map_natCast, ZMod.natCast_zmod_val, sub_self]
  obtain ⟨w, hw⟩ := mem_multiples.1 hx
  obtain ⟨ρ, hρ, hρw⟩ := (D.mem_map_relDeg_iff hLK).2 ⟨Multiplicative.ofAdd w, rfl⟩
  refine ⟨m, ?_⟩
  have hdeg : D.relDeg K (ρ⁻¹ * ((φ ^ m)⁻¹ * τ)) = 1 := by
    rw [map_mul, map_mul, map_inv, map_inv, map_pow, hφ, hρw]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_pow, toAdd_ofAdd, toAdd_one]
    have hw' : relInertiaDegree D.deg K L • w = x - m := hw.symm
    rw [hw', nsmul_one]
    abel
  have hker : ((ρ⁻¹ * ((φ ^ m)⁻¹ * τ) : (K : Subgroup G)) : G) ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine Subgroup.mem_inf.2 ⟨Subtype.coe_prop _, MonoidHom.mem_ker.2 ?_⟩
    rw [← relDeg_pow, hdeg, one_pow]
  have h := (L : Subgroup G).mul_mem (Subgroup.mem_subgroupOf.1 hρ) (hu hker)
  simpa using h

theorem zpowers_eq_top_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal]
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) :
    Subgroup.zpowers ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) = ⊤ := by
  refine eq_top_iff.2 fun q _ => ?_
  induction q using QuotientGroup.induction_on with
  | H τ =>
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ τ
    refine ⟨m, ?_⟩
    change ((φ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K)) ^ (m : ℤ) = τ
    rw [zpow_natCast, ← QuotientGroup.mk_pow, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using hm

theorem isCyclic_of_unramified (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    [((L : Subgroup G).subgroupOf K).Normal] :
    IsCyclic ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  exact isCyclic_iff_exists_zpowers_eq_top.2 ⟨_, D.zpowers_eq_top_of_unramified hLK hu hφ⟩

end Frobenius

section TateZero

variable {K L : OpenSubgroup G}

noncomputable def valuationMod (K : OpenSubgroup G) (n : ℕ+) :
    fixedModule A (K : Subgroup G) →* Multiplicative (ZMod n) :=
  (AddMonoidHom.toMultiplicative (proj n).toAddMonoidHom).comp (D.valuation K)

theorem valuationMod_apply (K : OpenSubgroup G) (n : ℕ+) (a : fixedModule A (K : Subgroup G)) :
    D.valuationMod K n a = Multiplicative.ofAdd (proj n (Multiplicative.toAdd (D.valuation K a))) :=
  rfl

theorem valuationMod_surjective (K : OpenSubgroup G) (n : ℕ+) :
    Function.Surjective (D.valuationMod K n) := by
  intro z
  have h : Multiplicative.ofAdd ((Multiplicative.toAdd z).val : ℤ̂) ∈ (D.valuation K).range := by
    rw [range_valuation]
    exact_mod_cast D.intCast_mem_range_val ((Multiplicative.toAdd z).val : ℤ)
  obtain ⟨a, ha⟩ := h
  refine ⟨a, ?_⟩
  rw [valuationMod_apply, ha, toAdd_ofAdd, map_natCast, ZMod.natCast_zmod_val, ofAdd_toAdd]

noncomputable def relInertiaDegreePNat (hLK : L ≤ K) : ℕ+ :=
  ⟨relInertiaDegree D.deg K L, Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hLK)⟩

@[simp] theorem coe_relInertiaDegreePNat (hLK : L ≤ K) :
    (D.relInertiaDegreePNat hLK : ℕ) = relInertiaDegree D.deg K L :=
  rfl

theorem range_norm_le_ker_valuationMod (hLK : L ≤ K) :
    (norm A (K : Subgroup G) (L : Subgroup G)).range ≤
      (D.valuationMod K (D.relInertiaDegreePNat hLK)).ker := by
  rintro _ ⟨a, rfl⟩
  rw [MonoidHom.mem_ker, valuationMod_apply, D.valuation_norm hLK, toAdd_pow, map_nsmul,
    nsmul_eq_mul]
  change Multiplicative.ofAdd (((D.relInertiaDegreePNat hLK : ℕ) : ZMod (D.relInertiaDegreePNat hLK)) *
    _) = 1
  rw [ZMod.natCast_self, zero_mul, ofAdd_zero]

noncomputable def tateZeroVal (hLK : L ≤ K) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      Multiplicative (ZMod (D.relInertiaDegreePNat hLK)) :=
  QuotientGroup.lift _ (D.valuationMod K (D.relInertiaDegreePNat hLK))
    (D.range_norm_le_ker_valuationMod hLK)

theorem tateZeroVal_mk (hLK : L ≤ K) (a : fixedModule A (K : Subgroup G)) :
    D.tateZeroVal hLK (a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      D.valuationMod K (D.relInertiaDegreePNat hLK) a :=
  rfl

theorem tateZeroVal_surjective (hLK : L ≤ K) : Function.Surjective (D.tateZeroVal hLK) := by
  intro z
  obtain ⟨a, ha⟩ := D.valuationMod_surjective K (D.relInertiaDegreePNat hLK) z
  exact ⟨a, ha⟩

theorem tateZeroVal_bijective (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) : Function.Bijective (D.tateZeroVal hLK) := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcyc := D.isCyclic_of_unramified hLK hu
  have hcard := (hax K L hLK hcyc).1
  rw [relIndex_eq_relInertiaDegree hLK hu] at hcard
  have : Finite (tateZero A (K : Subgroup G) (L : Subgroup G)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact D.relInertiaDegree_ne_zero hLK)
  refine (D.tateZeroVal_surjective hLK).bijective_of_nat_card_le ?_
  rw [hcard, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, coe_relInertiaDegreePNat]

noncomputable def tateZeroEquiv (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    tateZero A (K : Subgroup G) (L : Subgroup G) ≃*
      Multiplicative (ZMod ((L : Subgroup G).relIndex K)) :=
  (MulEquiv.ofBijective _ (D.tateZeroVal_bijective hax hLK hu)).trans
    (AddEquiv.toMultiplicative
      (ZMod.ringEquivCongr (m := (D.relInertiaDegreePNat hLK : ℕ))
        (relIndex_eq_relInertiaDegree (d := D.deg) hLK hu).symm).toAddEquiv)

end TateZero

section Units

variable {K L : OpenSubgroup G}

theorem norm_mem_units (hLK : L ≤ K) {a : fixedModule A (L : Subgroup G)} (ha : a ∈ D.units L) :
    norm A (K : Subgroup G) (L : Subgroup G) a ∈ D.units K := by
  rw [D.mem_units, D.valuation_norm hLK, D.mem_units.1 ha, one_pow]

theorem units_eq_map_norm (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) :
    D.units K = (D.units L).map (norm A (K : Subgroup G) (L : Subgroup G)) := by
  refine le_antisymm ?_ ?_
  · intro u hU
    have h1 : D.tateZeroVal hLK (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 := by
      rw [tateZeroVal_mk, valuationMod_apply, D.mem_units.1 hU, toAdd_one, map_zero, ofAdd_zero]
    have h2 : (u : tateZero A (K : Subgroup G) (L : Subgroup G)) = 1 :=
      (D.tateZeroVal_bijective hax hLK hu).1 (by rw [h1, map_one])
    obtain ⟨x, hx⟩ := (QuotientGroup.eq_one_iff u).1 h2
    refine ⟨x, ?_, hx⟩
    show x ∈ D.units L
    rw [D.mem_units]
    have h3 := D.valuation_norm hLK x
    rw [hx, D.mem_units.1 hU] at h3
    exact (ProfiniteInteger.pow_left_inj (D.relInertiaDegree_ne_zero hLK)).1
      (by rw [one_pow]; exact h3.symm)
  · rintro _ ⟨x, hx, rfl⟩
    exact D.norm_mem_units hLK hx

theorem exists_eq_smul_div_of_mem_augmentation (hLK : L ≤ K) (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L)
    {φ : (K : Subgroup G)} (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {x : A}
    (hx : x ∈ augmentation A (K : Subgroup G) (L : Subgroup G)) :
    ∃ b ∈ fixedModule A (L : Subgroup G), x = (φ : G) • b / b := by
  have := normal_of_unramified (d := D.deg) hLK hu

  let S : Subgroup A :=
    { carrier := {y | ∃ b ∈ fixedModule A (L : Subgroup G), y = (φ : G) • b / b}
      one_mem' := ⟨1, Subgroup.one_mem _, by rw [smul_one, div_one]⟩
      mul_mem' := by
        rintro _ _ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩
        exact ⟨b * c, Subgroup.mul_mem _ hb hc, by rw [smul_mul', mul_div_mul_comm]⟩
      inv_mem' := by
        rintro _ ⟨b, hb, rfl⟩
        exact ⟨b⁻¹, Subgroup.inv_mem _ hb, by rw [smul_inv', inv_div_inv, inv_div]⟩ }

  let T : Subgroup (K : Subgroup G) :=
    { carrier := {g | ∀ a ∈ fixedModule A (L : Subgroup G), (g : G) • a / a ∈ S}
      one_mem' := fun a _ => by
        rw [OneMemClass.coe_one, one_smul, div_self']
        exact S.one_mem
      mul_mem' := by
        intro g h hg hh a ha
        have hha : (h : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK h.2 ha
        have e : ((g * h : (K : Subgroup G)) : G) • a / a =
            ((g : G) • ((h : G) • a) / ((h : G) • a)) * ((h : G) • a / a) := by
          rw [Subgroup.coe_mul, mul_smul]
          simp only [div_eq_mul_inv, mul_assoc, inv_mul_cancel_left]
        rw [e]
        exact S.mul_mem (hg _ hha) (hh a ha)
      inv_mem' := by
        intro g hg a ha
        have hga : ((g⁻¹ : (K : Subgroup G)) : G) • a ∈ fixedModule A (L : Subgroup G) :=
          smul_mem_fixedModule_of_normal (L := (L : Subgroup G)) hLK (g⁻¹).2 ha
        have e : ((g⁻¹ : (K : Subgroup G)) : G) • a / a =
            ((g : G) • (((g⁻¹ : (K : Subgroup G)) : G) • a) / (((g⁻¹ : (K : Subgroup G)) : G) • a))⁻¹ := by
          rw [smul_smul, InvMemClass.coe_inv, mul_inv_cancel, one_smul, inv_div]
        rw [e]
        exact S.inv_mem (hg _ hga) }
  have hφT : φ ∈ T := fun a ha => ⟨a, ha, rfl⟩
  have hLT : ∀ ρ : (K : Subgroup G), (ρ : G) ∈ (L : Subgroup G) → ρ ∈ T := fun ρ hρ a ha => by
    rw [ha ρ hρ, div_self']
    exact S.one_mem
  have hTop : ∀ g : (K : Subgroup G), g ∈ T := by
    intro g
    obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hLK hu hφ g
    have hg : g = φ ^ m * ((φ ^ m)⁻¹ * g) := by group
    rw [hg]
    exact T.mul_mem (T.pow_mem hφT m) (hLT _ (by simpa using hm))
  have hle : augmentation A (K : Subgroup G) (L : Subgroup G) ≤ S := by
    rw [augmentation, Subgroup.closure_le]
    rintro _ ⟨g, hg, a, ha, rfl⟩
    exact hTop ⟨g, hg⟩ a ha
  exact hle hx

theorem exists_units_eq_smul_div (hax : ClassFieldAxiom G A) (hLK : L ≤ K)
    (hu : (K : Subgroup G) ⊓ D.deg.ker ≤ L) {φ : (K : Subgroup G)}
    (hφ : D.relDeg K φ = Multiplicative.ofAdd 1) {u : fixedModule A (L : Subgroup G)}
    (hN : norm A (K : Subgroup G) (L : Subgroup G) u = 1) :
    ∃ ε ∈ D.units L, (u : A) = (φ : G) • (ε : A) / ε := by
  have := normal_of_unramified (d := D.deg) hLK hu
  have hcard := (hax K L hLK (D.isCyclic_of_unramified hLK hu)).2
  have hsub := (Nat.card_eq_one_iff_unique.1 hcard).1

  have haug : (u : A) ∈ augmentation A (K : Subgroup G) (L : Subgroup G) := by
    have h := (QuotientGroup.eq_one_iff
      (N := (augmentation A (K : Subgroup G) (L : Subgroup G)).comap
        ((fixedModule A (L : Subgroup G)).subtype.comp
          (norm A (K : Subgroup G) (L : Subgroup G)).ker.subtype))
      (⟨u, hN⟩ : (norm A (K : Subgroup G) (L : Subgroup G)).ker)).1 (Subsingleton.elim _ _)
    exact h
  obtain ⟨b, hb, hub⟩ := D.exists_eq_smul_div_of_mem_augmentation hLK hu hφ haug

  have hval : D.valuation L ⟨b, hb⟩ ∈ (D.valuation K).range := by
    rw [range_valuation, ← D.range_valuation L]
    exact ⟨_, rfl⟩
  obtain ⟨c, hc⟩ := hval
  have he : relRamificationIndex D.deg K L = 1 := isUnramified_iff.2 hu
  refine ⟨⟨b, hb⟩ / ⟨c, fixedModule_anti hLK c.2⟩, ?_, ?_⟩
  · rw [D.mem_units, map_div, D.valuation_of_mem hLK c.2, he, pow_one]
    change D.valuation L ⟨b, hb⟩ / D.valuation K c = 1
    rw [hc, div_self']
  · have hφc : (φ : G) • (c : A) = c := c.2 φ φ.2
    change (u : A) = (φ : G) • ((b : A) / c) / (b / c)
    rw [smul_div', hφc, div_div_div_cancel_right, hub]

end Units

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  (D : ClassFieldData G A)

structure FrobeniusLift (K : OpenSubgroup G) where

  elt : G
  mem : elt ∈ (K : Subgroup G)

  deg : ℕ
  deg_pos : 0 < deg
  deg_eq : D.deg elt = Multiplicative.ofAdd ((deg * inertiaDegree D.deg K : ℕ) : ℤ̂)

variable {D} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in
theorem degree_ne_zero (s : D.FrobeniusLift K) : s.deg * inertiaDegree D.deg K ≠ 0 :=
  mul_ne_zero s.deg_pos.ne' (D.inertiaDegree_ne_zero K)

omit [TotallyDisconnectedSpace G] in

theorem mem_normalizer (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {σ : G}
    (hσ : σ ∈ (K : Subgroup G)) :
    σ ∈ Subgroup.normalizer (((L : Subgroup G) ⊓ D.deg.ker : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  simp only [Subgroup.mem_inf, MonoidHom.mem_ker, map_mul, map_inv]
  constructor
  · rintro ⟨hL, hk⟩
    refine ⟨hconj σ hσ h hL, ?_⟩
    rw [hk, mul_one, mul_inv_cancel]
  · rintro ⟨hL, hk⟩
    refine ⟨?_, ?_⟩
    · have := hconj σ⁻¹ (K.inv_mem hσ) _ hL
      simpa [mul_assoc] using this
    · have := hk
      rwa [mul_comm (D.deg σ), mul_assoc, mul_inv_cancel, mul_one] at this

variable (L) in

noncomputable def field (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) : OpenSubgroup G where
  toSubgroup := frobeniusClosure D.deg L s.elt
  isOpen' := isOpen_frobeniusClosure D.continuous_deg L.isOpen (mem_normalizer hLK s.mem)
    s.degree_ne_zero s.deg_eq

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_field : ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
    frobeniusClosure D.deg L s.elt :=
  rfl

theorem field_le : s.field L hLK ≤ K := by
  intro x hx
  exact frobeniusClosure_le K.isClosed s.mem (inf_le_left.trans hLK) hx

theorem elt_mem_field : s.elt ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) :=
  mem_frobeniusClosure_self

theorem field_inf_ker :
    ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker = (L : Subgroup G) ⊓ D.deg.ker :=
  frobeniusClosure_inf_ker D.continuous_deg L.isOpen (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem inertiaDegree_field :
    inertiaDegree D.deg ((s.field L hLK : OpenSubgroup G) : Subgroup G) =
      s.deg * inertiaDegree D.deg K :=
  inertiaDegree_frobeniusClosure D.continuous_deg (mem_normalizer hLK s.mem) s.degree_ne_zero
    s.deg_eq

theorem relDeg_field :
    D.relDeg (s.field L hLK) ⟨s.elt, s.elt_mem_field hLK⟩ = Multiplicative.ofAdd 1 := by
  refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero (s.field L hLK))).1 ?_
  rw [D.relDeg_pow, inertiaDegree_field, ← ofAdd_nsmul, nsmul_one]
  exact s.deg_eq


end FrobeniusLift

omit [TotallyDisconnectedSpace G] in

theorem exists_prime (K : OpenSubgroup G) :
    ∃ π : fixedModule A (K : Subgroup G), D.valuation K π = Multiplicative.ofAdd 1 := by
  have h := D.intCast_mem_range_val 1
  rw [← D.range_valuation K, Int.cast_one] at h
  exact h

section PrimeNorm

variable (K L) in

noncomputable def primeNorm (S : OpenSubgroup G) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) (D.exists_prime S).choose)

omit [TotallyDisconnectedSpace G] in

theorem norm_mem_range_of_mem_units (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {u : fixedModule A (S : Subgroup G)}
    (hu' : u ∈ D.units S) :
    norm A (K : Subgroup G) (S : Subgroup G) u ∈ (norm A (K : Subgroup G) (L : Subgroup G)).range := by
  set M : OpenSubgroup G := L ⊓ S with hMdef
  have hMS : M ≤ S := inf_le_right
  have hML : M ≤ L := inf_le_left
  have hMu : (S : Subgroup G) ⊓ D.deg.ker ≤ M := fun x hx => ⟨hu hx, hx.1⟩
  rw [D.units_eq_map_norm hax hMS hMu] at hu'
  obtain ⟨w, -, rfl⟩ := hu'
  rw [norm_norm (fun x hx => hMS hx) (fun x hx => hSK hx) w]
  exact ⟨norm A (L : Subgroup G) (M : Subgroup G) w,
    norm_norm (fun x hx => hML hx) (fun x hx => hLK hx) w⟩

omit [TotallyDisconnectedSpace G] in

theorem mk_norm_eq_primeNorm (hax : ClassFieldAxiom G A) {S : OpenSubgroup G} (hSK : S ≤ K)
    (hLK : L ≤ K) (hu : (S : Subgroup G) ⊓ D.deg.ker ≤ L) {π : fixedModule A (S : Subgroup G)}
    (hπ : D.valuation S π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) (S : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.primeNorm K L S := by
  set π0 := (D.exists_prime S).choose with hπ0
  have h0 : D.valuation S π0 = Multiplicative.ofAdd 1 := (D.exists_prime S).choose_spec
  have hu' : π * π0⁻¹ ∈ D.units S := by
    rw [D.mem_units, map_mul, map_inv, hπ, h0, mul_inv_cancel]
  obtain ⟨b, hb⟩ := D.norm_mem_range_of_mem_units hax hSK hLK hu hu'
  rw [primeNorm, ← hπ0, QuotientGroup.eq]
  have : (norm A (K : Subgroup G) (S : Subgroup G) π)⁻¹ * norm A (K : Subgroup G) (S : Subgroup G) π0 =
      (norm A (K : Subgroup G) (S : Subgroup G) (π * π0⁻¹))⁻¹ := by
    rw [map_mul, map_inv, mul_inv_rev, inv_inv, mul_comm]
  rw [this]
  exact Subgroup.inv_mem _ ⟨b, hb⟩

end PrimeNorm

section RecFrob

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

variable (L) in

noncomputable def recFrob (s : D.FrobeniusLift K) : tateZero A (K : Subgroup G) (L : Subgroup G) :=
  D.primeNorm K L (s.field L hLK)

theorem mk_norm_eq_recFrob (hax : ClassFieldAxiom G A) (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    (QuotientGroup.mk (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) :
      tateZero A (K : Subgroup G) (L : Subgroup G)) = D.recFrob L hLK s :=
  D.mk_norm_eq_primeNorm hax (s.field_le hLK) hLK (fun x hx => by
    have := (s.field_inf_ker hLK).le hx
    exact this.1) hπ

end RecFrob

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem coe_norm_eq_prod_smul_norm (d : G →* Multiplicative ℤ̂) {K S J : Subgroup G} {f n : ℕ}
    (hn : 0 < n) (hf : 0 < f) (hSK : S ≤ K)
    (hdS : ∀ s ∈ S, Multiplicative.toAdd (d s) ∈ multiples (n * f))
    (hsurj : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples (n * f) → ∃ s ∈ S, d s = d k)
    (hdK : ∀ k ∈ K, Multiplicative.toAdd (d k) ∈ multiples f)
    (hJ : ∀ q ∈ K ⊓ d.ker, q ∈ S ↔ q ∈ J)
    {φ : G} (hφK : φ ∈ K) (hdφ : d φ = Multiplicative.ofAdd (f : ℤ̂))
    [(S.subgroupOf K).FiniteIndex] [(J.subgroupOf (K ⊓ d.ker)).FiniteIndex]
    (a : fixedModule A S) (ha : (a : A) ∈ fixedModule A J) :
    (norm A K S a : A) =
      ∏ ν : Fin n, φ ^ (ν : ℕ) • (norm A (K ⊓ d.ker) J ⟨a, ha⟩ : A) := by
  classical
  set Q := K ⊓ d.ker with hQ
  have hQK : Q ≤ K := inf_le_left

  let incl : Q ⧸ J.subgroupOf Q → K ⧸ S.subgroupOf K :=
    Quotient.map' (fun q : Q => (⟨q, hQK q.2⟩ : K)) fun q q' h => by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
      have hq : ((q⁻¹ * q' : Q) : G) ∈ Q := (q⁻¹ * q').2
      simpa using (hJ _ hq).2 h
  let φK : K := ⟨φ, hφK⟩
  let F : Fin n × (Q ⧸ J.subgroupOf Q) → K ⧸ S.subgroupOf K := fun p => (φK ^ (p.1 : ℕ)) • incl p.2
  have hFmk : ∀ (ν : Fin n) (q : Q), F (ν, (q : Q ⧸ J.subgroupOf Q)) =
      ((φK ^ (ν : ℕ) * ⟨q, hQK q.2⟩ : K) : K ⧸ S.subgroupOf K) := fun _ _ => rfl

  have hdeg : ∀ (m : ℤ) (q : G), q ∈ Q →
      Multiplicative.toAdd (d (φ ^ m * q)) = ((m * f : ℤ) : ℤ̂) := by
    intro m q hq
    rw [map_mul, map_zpow, hdφ, (MonoidHom.mem_ker).1 hq.2, mul_one, ← ofAdd_zsmul, toAdd_ofAdd,
      zsmul_eq_mul]
    push_cast
    ring
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨ν, x⟩ ⟨μ, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H q =>
      induction y using QuotientGroup.induction_on with
      | H q' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow] at hxy

        have hx : ((φ ^ (ν : ℕ) * (q : G))⁻¹ * (φ ^ (μ : ℕ) * q') : G) =
            (q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q') := by
          rw [zpow_sub, zpow_natCast, zpow_natCast]
          group
        have hdq : Multiplicative.toAdd (d ((q : G)⁻¹ * (φ ^ ((μ : ℤ) - ν) * q'))) =
            ((((μ : ℤ) - ν) * f : ℤ) : ℤ̂) := by
          rw [map_mul, map_inv, (MonoidHom.mem_ker).1 q.2.2, inv_one, one_mul]
          exact hdeg _ _ q'.2
        have hmem := hdS _ hxy
        rw [hx, hdq] at hmem
        have hdvd := (intCast_mem_multiples_iff (Nat.mul_pos hn hf)).1 hmem
        push_cast at hdvd
        have hdvd' : (n : ℤ) ∣ (μ : ℤ) - ν :=
          (mul_dvd_mul_iff_right (by exact_mod_cast hf.ne')).1 hdvd
        have hνμ : ν = μ := by
          have hμ := μ.2
          have hν := ν.2
          have h0 : ((μ : ℤ) - ν) = 0 :=
            Int.eq_zero_of_abs_lt_dvd hdvd' (abs_sub_lt_iff.2 ⟨by omega, by omega⟩)
          exact Fin.ext (by omega)
        subst hνμ
        have hqq : (q : G)⁻¹ * q' ∈ S := by simpa [mul_assoc] using hxy
        have hqQ : (q : G)⁻¹ * q' ∈ Q := Q.mul_mem (Q.inv_mem q.2) q'.2
        refine Prod.ext rfl ?_
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa using (hJ _ hqQ).1 hqq
    · intro y
      induction y using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨w, hw⟩ := mem_multiples.1 (hdK k k.2)
        set N : ℕ+ := ⟨n, hn⟩ with hNdef
        set ν : ℕ := (proj N w).val with hνdef
        have hνn : ν < n := ZMod.val_lt _
        have hw' : w - (ν : ℤ̂) ∈ multiples n := by
          have := (proj_eq_zero_iff (n := N) (x := w - (ν : ℤ̂))).1 (by
            rw [map_sub, map_natCast, hνdef, ZMod.natCast_zmod_val, sub_self])
          simpa [hNdef] using this
        obtain ⟨z, hz⟩ := mem_multiples.1 hw'
        have hdk : Multiplicative.toAdd (d (φ ^ (-(ν : ℤ)) * k)) ∈ multiples (n * f) := by
          rw [map_mul, map_zpow, hdφ, ← ofAdd_zsmul, toAdd_mul, toAdd_ofAdd, hw]
          refine mem_multiples.2 ⟨z, ?_⟩
          have : w = (ν : ℤ̂) + n • z := by rw [← hz]; ring
          rw [this]
          simp only [nsmul_eq_mul, zsmul_eq_mul]
          push_cast
          ring
        obtain ⟨s, hs, hds⟩ := hsurj _ (K.mul_mem (K.zpow_mem hφK _) k.2) hdk
        set q : G := φ ^ (-(ν : ℤ)) * k * s⁻¹ with hqdef
        have hqQ : q ∈ Q := by
          refine ⟨K.mul_mem (K.mul_mem (K.zpow_mem hφK _) k.2) (K.inv_mem (hSK hs)), ?_⟩
          show d q = 1
          rw [hqdef, map_mul, map_inv, ← hds, mul_inv_cancel]
        refine ⟨(⟨ν, hνn⟩, ((⟨q, hqQ⟩ : Q) : Q ⧸ J.subgroupOf Q)), ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubmonoidClass.coe_pow, hqdef]
        have : ((φ ^ ν * (φ ^ (-(ν : ℤ)) * (k : G) * s⁻¹))⁻¹ * k : G) = s := by
          rw [zpow_neg, zpow_natCast]
          group
        rw [this]
        exact hs
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF)]
  let _ := Fintype.ofFinite (Q ⧸ J.subgroupOf Q)
  rw [finprod_eq_prod_of_fintype, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun ν _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype, Finset.smul_prod']
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H q =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk, smul_smul]
    rfl

namespace ClassFieldData

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

omit [TotallyDisconnectedSpace G] in

instance finiteIndex_inf_ker (d : G →* Multiplicative ℤ̂) (K L : OpenSubgroup G) :
    (((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker)).FiniteIndex := by
  have h : ((L : Subgroup G) ⊓ d.ker).subgroupOf ((K : Subgroup G) ⊓ d.ker) =
      (L : Subgroup G).subgroupOf ((K : Subgroup G) ⊓ d.ker) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, and_iff_left_iff_imp]
    exact fun _ => x.2.2
  rw [h]
  infer_instance

omit [TotallyDisconnectedSpace G] in

theorem toAdd_deg_mem_multiples (K : OpenSubgroup G) {k : G} (hk : k ∈ (K : Subgroup G)) :
    Multiplicative.toAdd (D.deg k) ∈ multiples (inertiaDegree D.deg K) := by
  obtain ⟨y, hy⟩ := (D.mem_map_deg_iff K).1 ⟨k, hk, rfl⟩
  refine mem_multiples.2 ⟨Multiplicative.toAdd y, ?_⟩
  rw [← hy, toAdd_pow]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K)

theorem coe_norm_field_eq {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (a : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A (K : Subgroup G) (s.field L hLK : Subgroup G) a : A) =
      ∏ ν : Fin s.deg, φ ^ (ν : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨a, fixedModule_anti le_frobeniusClosure a.2⟩ : A) := by
  have hmap := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s.mem)
    s.deg_eq (L := (L : Subgroup G))
  refine coe_norm_eq_prod_smul_norm D.deg s.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    (fun x hx => s.field_le hLK hx) ?_ ?_ (fun k hk => toAdd_deg_mem_multiples K hk) ?_ hφK hdφ a _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap] at this
    exact this
  · intro k _ hk
    have : D.deg k ∈ AddSubgroup.toSubgroup (multiples (s.deg * inertiaDegree D.deg K)) := hk
    rw [← hmap] at this
    obtain ⟨x, hx, hxk⟩ := this
    exact ⟨x, hx, hxk⟩
  · intro q hq
    constructor
    · intro hqS
      have : q ∈ ((s.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker := ⟨hqS, hq.2⟩
      rw [s.field_inf_ker hLK] at this
      exact this
    · intro hqJ
      exact le_frobeniusClosure hqJ

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

section SlopeTestRemainingChoices

omit [TotallyDisconnectedSpace G] in

def powLift {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) (m : ℕ) (hm : 0 < m) :
    D.FrobeniusLift K where
  elt := φ ^ m
  mem := K.pow_mem hφK m
  deg := m
  deg_pos := hm
  deg_eq := by
    rw [map_pow, hdφ, ← ofAdd_nsmul]
    congr 1
    push_cast
    rw [nsmul_eq_mul]

omit [TotallyDisconnectedSpace G] in

theorem mem_fixedModule_of_smul_eq [IsDiscreteModule G A] (K : OpenSubgroup G) {φ : G}
    (hφK : φ ∈ (K : Subgroup G)) (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    {w : A} (hw : w ∈ fixedModule A ((K : Subgroup G) ⊓ D.deg.ker)) (hφw : φ • w = w) :
    w ∈ fixedModule A (K : Subgroup G) := by
  let S : OpenSubgroup G := ⟨MulAction.stabilizer G w, IsDiscreteModule.isOpen_stabilizer w⟩
  let M : OpenSubgroup G := S ⊓ K
  have hMK : M ≤ K := inf_le_right
  have hu : (K : Subgroup G) ⊓ D.deg.ker ≤ M := fun g hg => ⟨hw g hg, hg.1⟩
  have hrel : D.relDeg K ⟨φ, hφK⟩ = Multiplicative.ofAdd 1 := by
    refine (ProfiniteInteger.pow_left_inj (D.inertiaDegree_ne_zero K)).1 ?_
    rw [D.relDeg_pow, ← ofAdd_nsmul, nsmul_one]
    exact hdφ
  intro τ hτ
  obtain ⟨m, hm⟩ := D.exists_pow_mul_mem_of_unramified hMK hu hrel ⟨τ, hτ⟩
  have h1 : ∀ j : ℕ, (φ ^ j) • w = w := by
    intro j
    induction j with
    | zero => simp
    | succ k ih => rw [pow_succ, mul_smul, hφw, ih]
  have h2 : ((φ ^ m)⁻¹ * τ) • w = w := by
    have h3 : (φ ^ m)⁻¹ * τ ∈ S := by simpa using hm.1
    exact MulAction.mem_stabilizer_iff.1 h3
  calc τ • w = (φ ^ m * ((φ ^ m)⁻¹ * τ)) • w := by group
    _ = w := by rw [mul_smul, h2, h1]

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) :
    ((L : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom = (L : Subgroup G) ⊓ D.deg.ker :=
  Subgroup.mem_normalizer_iff_map_conj_eq.1 (FrobeniusLift.mem_normalizer hLK hg)

omit [TotallyDisconnectedSpace G] in

theorem map_conj_inf_ker_self {g : G} (hg : g ∈ (K : Subgroup G)) :
    ((K : Subgroup G) ⊓ D.deg.ker).map (MulAut.conj g).toMonoidHom =
      (K : Subgroup G) ⊓ D.deg.ker := by
  have : ((K : Subgroup G).subgroupOf K).Normal := by
    rw [Subgroup.subgroupOf_self]
    infer_instance
  exact map_conj_inf_ker le_rfl hg

omit [TotallyDisconnectedSpace G] in

theorem smul_mem_fixedModule_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) {y : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) := by
  have := smul_mem_fixedModule hy g
  rwa [map_conj_inf_ker hLK hg] at this

omit [TotallyDisconnectedSpace G] in

theorem smul_norm_inf_ker (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal] {g : G}
    (hg : g ∈ (K : Subgroup G)) (y : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    g • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) y : A) =
      norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨g • (y : A), smul_mem_fixedModule_inf_ker hLK hg y.2⟩ :=
  smul_norm_of_map_eq g (map_conj_inf_ker_self hg) (map_conj_inf_ker hLK hg) y

omit [TotallyDisconnectedSpace G] in

theorem smul_smul_comm (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] {δ ψ : G}
    (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hψ : ψ ∈ (L : Subgroup G)) {y : A}
    (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) : δ • ψ • y = ψ • δ • y := by
  have hconj : ∀ g ∈ (K : Subgroup G), ∀ x ∈ (L : Subgroup G), g * x * g⁻¹ ∈ (L : Subgroup G) := by
    intro g hg x hx
    have := hN.conj_mem ⟨x, hLK hx⟩ (by simpa [Subgroup.mem_subgroupOf] using hx) ⟨g, hg⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hc : δ⁻¹ * ψ⁻¹ * δ * ψ ∈ (L : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨?_, ?_⟩
    · have h1 : δ⁻¹ * ψ⁻¹ * δ⁻¹⁻¹ ∈ (L : Subgroup G) :=
        hconj δ⁻¹ (K.inv_mem hδ.1) _ (L.inv_mem hψ)
      rw [inv_inv] at h1
      exact L.mul_mem h1 hψ
    · have hdδ : D.deg δ = 1 := hδ.2
      show D.deg (δ⁻¹ * ψ⁻¹ * δ * ψ) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hdδ]
      simp
  calc δ • ψ • y = (ψ * δ * (δ⁻¹ * ψ⁻¹ * δ * ψ)) • y := by rw [← mul_smul]; group
    _ = ψ • δ • y := by rw [mul_smul, hy _ hc, mul_smul]

theorem smul_mem_field [IsDiscreteModule G A] (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (s : D.FrobeniusLift K) {g : G}
    (hgJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      g • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hcomm : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker), s.elt • g • y = g • s.elt • y)
    {y : A} (hy : y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)) :
    g • y ∈ fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G) := by
  rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure] at hy ⊢
  exact ⟨hgJ y hy.1, by rw [hcomm y hy.1, hy.2]⟩

end SlopeTestRemainingChoices

section Helpers

omit [TotallyDisconnectedSpace G] in

theorem normal_inf_ker (hLK : L ≤ K) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((L : Subgroup G) ⊓ D.deg.ker).subgroupOf ((K : Subgroup G) ⊓ D.deg.ker)).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  have h := (Subgroup.mem_normalizer_iff.1 (FrobeniusLift.mem_normalizer (D := D) hLK g.2.1) n).1 hn
  simpa using h

omit [TotallyDisconnectedSpace G] in

theorem prod_range_prod_range_eq {M : Type*} [CommMonoid M] (f : ℕ → M) (g D0 : ℕ) :
    ∏ i ∈ Finset.range g, ∏ j ∈ Finset.range D0, f (D0 * i + j) =
      ∏ m ∈ Finset.range (g * D0), f m := by
  induction g with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Nat.succ_mul, Finset.prod_range_add, mul_comm D0 k]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem field_le_field_of_pow (s1 s2 : D.FrobeniusLift K) (k : ℕ) (h2 : s2.elt = s1.elt ^ k) :
    s2.field L hLK ≤ s1.field L hLK := by
  intro x hx
  refine frobeniusClosure_le (s1.field L hLK).isClosed ?_ le_frobeniusClosure hx
  rw [h2]
  exact Subgroup.pow_mem _ (s1.elt_mem_field hLK) k

theorem coe_norm_field_field (s1 s2 : D.FrobeniusLift K) (k : ℕ) (hk : 0 < k)
    (h2 : s2.elt = s1.elt ^ k) (hdeg : s2.deg = k * s1.deg)
    (z : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) :
    (norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) z : A) =
      ∏ i : Fin k, s1.elt ^ (i : ℕ) • (z : A) := by
  have hmap1 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s1.mem)
    s1.deg_eq (L := (L : Subgroup G))
  have hmap2 := map_frobeniusClosure D.continuous_deg (FrobeniusLift.mem_normalizer hLK s2.mem)
    s2.deg_eq (L := (L : Subgroup G))
  rw [hdeg, mul_assoc] at hmap2
  have hf : 0 < s1.deg * inertiaDegree D.deg K :=
    Nat.mul_pos s1.deg_pos (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
  have key := coe_norm_eq_prod_smul_norm D.deg (K := ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (S := ((s2.field L hLK : OpenSubgroup G) : Subgroup G)) (J := (L : Subgroup G) ⊓ D.deg.ker)
    (f := s1.deg * inertiaDegree D.deg K) (n := k) hk hf
    (fun x hx => field_le_field_of_pow hLK s1 s2 k h2 hx) ?_ ?_ ?_ ?_
    (s1.elt_mem_field hLK) s1.deg_eq z (fixedModule_anti le_frobeniusClosure z.2)
  · rw [key]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1
    exact coe_norm_of_le (fun x hx => (s1.field_inf_ker hLK).le hx) _
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s2.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap2] at this
    exact this
  · intro x _ hx
    have : D.deg x ∈ AddSubgroup.toSubgroup (multiples (k * (s1.deg * inertiaDegree D.deg K))) := hx
    rw [← hmap2] at this
    obtain ⟨y, hy, hyx⟩ := this
    exact ⟨y, hy, hyx⟩
  · intro x hx
    have : D.deg x ∈ (frobeniusClosure D.deg L s1.elt).map D.deg := ⟨x, hx, rfl⟩
    rw [hmap1] at this
    exact this
  · intro q hq
    have hqJ : q ∈ (L : Subgroup G) ⊓ D.deg.ker := (s1.field_inf_ker hLK).le hq
    exact ⟨fun _ => hqJ, fun h => le_frobeniusClosure h⟩

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_prod {ι : Type*} (s : Finset ι) (f : ι → A)
    (hf : ∀ i, f i ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ : A) =
      ∏ i ∈ s, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨f i, hf i⟩ : A) := by
  have h : (⟨∏ i ∈ s, f i, Subgroup.prod_mem _ fun i _ => hf i⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ∏ i ∈ s, ⟨f i, hf i⟩ := by
    ext
    simp
  rw [h, map_prod]
  simp

omit [TotallyDisconnectedSpace G] [((L : Subgroup G).subgroupOf K).Normal] in

theorem coe_norm_inf_ker_mul {y z : A} (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker))
    (hz : z ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) :
    (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨y * z, Subgroup.mul_mem _ hy hz⟩ : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) *
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨z, hz⟩ := by
  have h : (⟨y * z, Subgroup.mul_mem _ hy hz⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
      ⟨y, hy⟩ * ⟨z, hz⟩ := rfl
  rw [h, map_mul]
  rfl

end Helpers

section Key

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem exists_norm_eq_norm_inf_ker (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂))
    (s1 s2 : D.FrobeniusLift K) (h1 : s1.elt = φ ^ s1.deg) (hψL : s1.elt ∈ (L : Subgroup G))
    (h2 : s2.elt = s1.elt ^ ((L : Subgroup G).relIndex K))
    (hdeg : s2.deg = (L : Subgroup G).relIndex K * s1.deg)
    {x a : A} (hx : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (ha : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G))
    (hxu : D.valuation (s1.field L hLK) ⟨x, hx⟩ = 1)
    (hau : D.valuation (s1.field L hLK) ⟨a, ha⟩ = 1)
    {δ : G} (hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker) (hrel : φ • x / x = δ • a / a) :
    ∃ b : fixedModule A (L : Subgroup G),
      (norm A (K : Subgroup G) (L : Subgroup G) b : A) =
        norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ := by
  classical
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  have hP'P : s2.field L hLK ≤ s1.field L hLK := field_le_field_of_pow hLK s1 s2 g h2
  have hP'L : s2.field L hLK ≤ L := fun y hy =>
    frobeniusClosure_le L.isClosed (by rw [h2]; exact L.pow_mem hψL g) inf_le_left hy
  have hu : ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⊓ D.deg.ker ≤ s2.field L hLK :=
    fun y hy => le_frobeniusClosure ((s1.field_inf_ker hLK).le hy)
  have hT := coe_norm_field_field hLK s1 s2 g hg h2 hdeg
  have hrelψ := s1.relDeg_field hLK

  have hφJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hφK hy
  have hφjJ : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      φ ^ j • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun j y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK j) hy
  have hδJ : ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      δ • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => smul_mem_fixedModule_inf_ker hLK hδ.1 hy
  have hcommφ : ∀ (i j : ℕ) (y : A), s1.elt ^ i • φ ^ j • y = φ ^ j • s1.elt ^ i • y := by
    intro i j y
    have hc : Commute (s1.elt ^ i) (φ ^ j) := by
      rw [h1]
      exact (((Commute.refl φ).pow_left _).pow_left _).pow_right _
    rw [smul_smul, smul_smul, hc.eq]
  have hcommδ : ∀ (i : ℕ), ∀ y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker),
      s1.elt ^ i • δ • y = δ • s1.elt ^ i • y :=
    fun i y hy => (smul_smul_comm hLK hδ (L.pow_mem hψL i) hy).symm
  have hφP' : ∀ (j : ℕ), ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      φ ^ j • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro j y hy
    refine smul_mem_field hLK s2 (hφjJ j) (fun z _ => ?_) hy
    rw [h2]
    exact hcommφ g j z
  have hδP' : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      δ • y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    intro y hy
    refine smul_mem_field hLK s2 hδJ (fun z hz => ?_) hy
    rw [h2]
    exact hcommδ g z hz
  have hP'J : ∀ y ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G),
      y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun y hy => fixedModule_anti le_frobeniusClosure hy

  have hxU : (⟨x, hx⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hxu
  rw [D.units_eq_map_norm hax hP'P hu] at hxU
  obtain ⟨x'', -, hx''⟩ := hxU
  have haU : (⟨a, ha⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) ∈
      D.units (s1.field L hLK) := hau
  rw [D.units_eq_map_norm hax hP'P hu] at haU
  obtain ⟨c, -, hc⟩ := haU
  have hxN : x = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) := by
    rw [← hT, hx'']
  have haN : a = ∏ i : Fin g, s1.elt ^ (i : ℕ) • (c : A) := by
    rw [← hT, hc]

  have hφx'' : φ • (x'' : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) := by
    simpa using hφP' 1 _ x''.2
  have hδc : δ • (c : A) ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    hδP' _ c.2
  set y' : fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    ⟨φ • (x'' : A), hφx''⟩ / x'' / (⟨δ • (c : A), hδc⟩ / c) with hy'def
  have hNy' : norm A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)
      ((s2.field L hLK : OpenSubgroup G) : Subgroup G) y' = 1 := by
    apply Subtype.ext
    rw [hT]
    simp only [hy'def, Subgroup.coe_div, OneMemClass.coe_one, smul_div', Finset.prod_div_distrib]
    have e1 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • φ • (x'' : A) = φ • x := by
      rw [hxN, Finset.smul_prod']
      refine Finset.prod_congr rfl fun i _ => ?_
      simpa using hcommφ i 1 (x'' : A)
    have e2 : ∏ i : Fin g, s1.elt ^ (i : ℕ) • δ • (c : A) = δ • a := by
      rw [haN, Finset.smul_prod']
      exact Finset.prod_congr rfl fun i _ => hcommδ i _ (hP'J _ c.2)
    rw [e1, e2, ← hxN, ← haN, hrel, div_self']
  obtain ⟨b, -, hb⟩ := D.exists_units_eq_smul_div hax hP'P hu hrelψ hNy'

  set Tb : A := ∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) with hTbdef
  have hTbP' : Tb ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.prod_mem _ fun j _ => hφP' j _ b.2
  have htele : φ • Tb / Tb = s1.elt • (b : A) / b := by
    rw [hTbdef, Finset.smul_prod', h1]
    simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • (b : A)),
      Fin.prod_univ_eq_prod_range (fun j => φ ^ j • (b : A))]
    have hs := Finset.prod_range_succ (fun j => φ ^ j • (b : A)) s1.deg
    have hs' := Finset.prod_range_succ' (fun j => φ ^ j • (b : A)) s1.deg
    simp only [pow_zero, one_smul] at hs'
    have : ∏ j ∈ Finset.range s1.deg, φ • φ ^ j • (b : A) =
        ∏ j ∈ Finset.range s1.deg, φ ^ (j + 1) • (b : A) := by
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [smul_smul, ← pow_succ']
    rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]
  set x' : A := (x'' : A) / Tb with hx'def
  have hx'P' : x' ∈ fixedModule A ((s2.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ x''.2 hTbP'
  have hx'J := hP'J _ hx'P'
  have hrel' : φ • x' = x' * (δ • (c : A) / c) := by
    have hy'v : (y' : A) = φ • (x'' : A) / x'' / (δ • (c : A) / c) := by
      simp [hy'def]
    have e : φ • (x'' : A) / x'' = (s1.elt • (b : A) / b) * (δ • (c : A) / c) := by
      rw [← hb, hy'v, div_mul_cancel]
    have e2 : φ • Tb = Tb * (s1.elt • (b : A) / b) := by
      rw [← htele, mul_div_cancel]
    rw [hx'def, smul_div', e2]
    have e3 : φ • (x'' : A) = x'' * ((s1.elt • (b : A) / b) * (δ • (c : A) / c)) := by
      rw [← e, mul_div_cancel]
    rw [e3, mul_div_mul_comm, mul_div_cancel_left]

  set w : A := (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x', hx'J⟩ : A)
    with hwdef
  have := normal_inf_ker (D := D) hLK
  have hcJ := hP'J _ c.2
  have hwφ : φ • w = w := by
    rw [hwdef, smul_norm_inf_ker hLK hφK]
    have e : (⟨φ • x', smul_mem_fixedModule_inf_ker hLK hφK hx'J⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨x', hx'J⟩ * (⟨δ • (c : A), hδJ _ hcJ⟩ / ⟨c, hcJ⟩) := by
      ext
      simp [hrel']
    rw [e, map_mul, map_div, norm_smul (K := (K : Subgroup G) ⊓ D.deg.ker)
      (L := (L : Subgroup G) ⊓ D.deg.ker) ⟨δ, hδ⟩ ⟨(c : A), hcJ⟩ (hδJ _ hcJ), div_self', mul_one]
  have hwK : w ∈ fixedModule A (K : Subgroup G) :=
    mem_fixedModule_of_smul_eq K hφK hdφ (norm _ _ _ _).2 hwφ

  have hbJ := hP'J _ b.2
  have hNb := coe_norm_field_eq hLK s2 hφK hdφ b
  refine ⟨⟨w, fixedModule_anti hLK hwK⟩ * norm A (L : Subgroup G)
    ((s2.field L hLK : OpenSubgroup G) : Subgroup G) b, ?_⟩
  have hψK : ∀ i : ℕ, s1.elt ^ i ∈ (K : Subgroup G) := fun i => K.pow_mem s1.mem i
  have hx''eq : (x'' : A) = x' * Tb := by rw [hx'def, div_mul_cancel]
  have hTbJ := hP'J _ hTbP'
  have hNTb : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) =
      ∏ j : Fin s1.deg, φ ^ (j : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨b, hbJ⟩ : A) := by
    have hmemj : ∀ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun j => hφjJ j _ hbJ
    rw [show (⟨Tb, hTbJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ j : Fin s1.deg, φ ^ (j : ℕ) • (b : A), Subgroup.prod_mem _ fun j _ => hmemj j⟩ from rfl,
      coe_norm_inf_ker_prod Finset.univ _ hmemj]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK j)]
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
      ⟨x, fixedModule_anti le_frobeniusClosure hx⟩ : A) =
      w ^ g * ∏ i : Fin g, s1.elt ^ (i : ℕ) •
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
    have hmemi : ∀ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A) ∈
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
      fun i => smul_mem_fixedModule_inf_ker hLK (hψK i) (hP'J _ x''.2)
    have e1 : (⟨x, fixedModule_anti le_frobeniusClosure hx⟩ :
        fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨∏ i : Fin g, s1.elt ^ (i : ℕ) • (x'' : A), Subgroup.prod_mem _ fun i _ => hmemi i⟩ :=
      Subtype.ext hxN
    rw [e1, coe_norm_inf_ker_prod Finset.univ _ hmemi]
    have e2 : ∀ i : Fin g, (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨s1.elt ^ (i : ℕ) • (x'' : A), hmemi i⟩ : A) =
        w * s1.elt ^ (i : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨Tb, hTbJ⟩ : A) := by
      intro i
      have h3 := smul_norm_inf_ker hLK (hψK i) ⟨(x'' : A), hP'J _ x''.2⟩
      rw [← h3]
      have e4 : (⟨(x'' : A), hP'J _ x''.2⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
          ⟨x' * Tb, Subgroup.mul_mem _ hx'J hTbJ⟩ := Subtype.ext hx''eq
      rw [e4, coe_norm_inf_ker_mul hx'J hTbJ, smul_mul', ← hwdef, hwK _ (hψK i)]
    rw [Finset.prod_congr rfl fun i _ => e2 i, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  rw [map_mul, Subgroup.coe_mul, coe_norm_of_mem hLK hwK,
    norm_norm (fun y hy => hP'L hy) (fun y hy => hLK hy) b, hNb, hNx, hNTb]
  congr 1
  simp_rw [Finset.smul_prod', smul_smul, h1, ← pow_mul, ← pow_add]
  rw [Fin.prod_univ_eq_prod_range (fun m => φ ^ m • _) s2.deg, hdeg,
    ← prod_range_prod_range_eq _ g s1.deg]
  simp only [Finset.prod_range]

end Key

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A} {K L : OpenSubgroup G}

namespace FrobeniusLift

omit [TotallyDisconnectedSpace G] in

def mul (s t : D.FrobeniusLift K) : D.FrobeniusLift K where
  elt := s.elt * t.elt
  mem := K.mul_mem s.mem t.mem
  deg := s.deg + t.deg
  deg_pos := Nat.add_pos_left s.deg_pos _
  deg_eq := by
    rw [map_mul, s.deg_eq, t.deg_eq, ← ofAdd_add]
    push_cast
    ring_nf

omit [TotallyDisconnectedSpace G] in

def ofDegOne {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) : D.FrobeniusLift K where
  elt := φ
  mem := hφK
  deg := 1
  deg_pos := Nat.one_pos
  deg_eq := by rw [hdφ, one_mul]

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem field_congr {s t : D.FrobeniusLift K} (h : s.elt = t.elt) :
    s.field L hLK = t.field L hLK := by
  apply OpenSubgroup.toSubgroup_injective
  show frobeniusClosure D.deg L s.elt = frobeniusClosure D.deg L t.elt
  rw [h]

theorem relInertiaDegree_field (s : D.FrobeniusLift K) :
    relInertiaDegree D.deg K (s.field L hLK) = s.deg := by
  have h := inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
    (L := ((s.field L hLK : OpenSubgroup G) : Subgroup G)) (fun x hx => s.field_le hLK hx)
  rw [s.inertiaDegree_field hLK] at h
  exact (Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K)) h).symm

end FrobeniusLift

variable (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]

theorem recFrob_congr {s t : D.FrobeniusLift K} (h : s.elt = t.elt) :
    D.recFrob L hLK s = D.recFrob L hLK t := by
  unfold recFrob
  rw [FrobeniusLift.field_congr hLK h]

theorem valuation_norm_prime (s : D.FrobeniusLift K)
    {π : fixedModule A ((s.field L hLK : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L hLK) π = Multiplicative.ofAdd 1) :
    D.valuation K (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π) =
      Multiplicative.ofAdd (s.deg : ℤ̂) := by
  rw [D.valuation_norm (s.field_le hLK), hπ, FrobeniusLift.relInertiaDegree_field, ← ofAdd_nsmul,
    nsmul_one]

section DegOne

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [((L : Subgroup G).subgroupOf K).Normal] in

theorem smul_prod_pow_div (φ : G) (y : A) (n : ℕ) :
    φ • (∏ ν : Fin n, φ ^ (ν : ℕ) • y) / ∏ ν : Fin n, φ ^ (ν : ℕ) • y = φ ^ n • y / y := by
  rw [Finset.smul_prod']
  simp only [Fin.prod_univ_eq_prod_range (fun j => φ • φ ^ j • y),
    Fin.prod_univ_eq_prod_range (fun j => φ ^ j • y)]
  have hs := Finset.prod_range_succ (fun j => φ ^ j • y) n
  have hs' := Finset.prod_range_succ' (fun j => φ ^ j • y) n
  simp only [pow_zero, one_smul] at hs'
  have : ∏ j ∈ Finset.range n, φ • φ ^ j • y = ∏ j ∈ Finset.range n, φ ^ (j + 1) • y := by
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [smul_smul, ← pow_succ']
  rw [this, div_eq_div_iff_mul_eq_mul, ← hs', hs, mul_comm]

omit [TotallyDisconnectedSpace G] in

theorem valuation_eq_of_inf_ker_eq {S P : OpenSubgroup G}
    (h : (S : Subgroup G) ⊓ D.deg.ker = (P : Subgroup G) ⊓ D.deg.ker) {y : A}
    (hyS : y ∈ fixedModule A (S : Subgroup G)) (hyP : y ∈ fixedModule A (P : Subgroup G)) :
    D.valuation P ⟨y, hyP⟩ = D.valuation S ⟨y, hyS⟩ := by
  set M : OpenSubgroup G := S ⊓ P
  have hMS : M ≤ S := inf_le_left
  have hMP : M ≤ P := inf_le_right
  have heS : relRamificationIndex D.deg S M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨hx.1, (h.le hx).1⟩
  have heP : relRamificationIndex D.deg P M = 1 :=
    isUnramified_iff.2 fun x hx => ⟨(h.ge hx).1, hx.1⟩
  have h1 := D.valuation_of_mem hMS hyS
  have h2 := D.valuation_of_mem hMP hyP
  rw [heS, pow_one] at h1
  rw [heP, pow_one] at h2
  rw [← h1, ← h2]

theorem recFrob_mul_ofDegOne (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (s : D.FrobeniusLift K) {φ : G} (hφK : φ ∈ (K : Subgroup G))
    (hdφ : D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂)) :
    D.recFrob L hLK (s.mul (FrobeniusLift.ofDegOne hφK hdφ)) =
      D.recFrob L hLK s * D.recFrob L hLK (FrobeniusLift.ofDegOne hφK hdφ) := by
  classical
  set t := FrobeniusLift.ofDegOne (D := D) hφK hdφ with htdef
  set u := s.mul t with hudef
  set n := s.deg with hndef
  obtain ⟨π1, hπ1⟩ := D.exists_prime (s.field L hLK)
  obtain ⟨π2, hπ2⟩ := D.exists_prime (t.field L hLK)
  obtain ⟨π3, hπ3⟩ := D.exists_prime (u.field L hLK)
  rw [← D.mk_norm_eq_recFrob hLK hax s hπ1, ← D.mk_norm_eq_recFrob hLK hax t hπ2,
    ← D.mk_norm_eq_recFrob hLK hax u hπ3, ← QuotientGroup.mk_mul, QuotientGroup.eq]

  have hJ : ∀ (v : D.FrobeniusLift K) (y : A),
      y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G) →
        y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun v y hy => fixedModule_anti le_frobeniusClosure hy
  have hφνJ : ∀ (ν : ℕ) (y : A), y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) →
      φ ^ ν • y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    fun ν y hy => smul_mem_fixedModule_inf_ker hLK (K.pow_mem hφK ν) hy
  have hσπ1 : s.elt • (π1 : A) = π1 := π1.2 _ (s.elt_mem_field hLK)
  have hφπ2 : φ • (π2 : A) = π2 := π2.2 _ (t.elt_mem_field hLK)
  have hσφπ3 : (s.elt * φ) • (π3 : A) = π3 := π3.2 _ (u.elt_mem_field hLK)
  set T1 : A := ∏ ν : Fin n, φ ^ (ν : ℕ) • (π1 : A) with hT1
  set T3 : A := ∏ ν : Fin (n + 1), φ ^ (ν : ℕ) • (π3 : A) with hT3
  set x : A := T1 * φ ^ n • (π2 : A) / T3 with hxdef
  set a : A := (π1 : A) / π3 with hadef
  have hT1J : T1 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ s _ π1.2)
  have hT3J : T3 ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.prod_mem _ fun ν _ => hφνJ ν _ (hJ u _ π3.2)
  have hπ2J : φ ^ n • (π2 : A) ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    hφνJ n _ (hJ t _ π2.2)
  have hxJ : x ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker) :=
    Subgroup.div_mem _ (Subgroup.mul_mem _ hT1J hπ2J) hT3J

  have hNprod : ∀ (m : ℕ) (y : A) (hy : y ∈ fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)),
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨∏ ν : Fin m, φ ^ (ν : ℕ) • y, Subgroup.prod_mem _ fun ν _ => hφνJ ν y hy⟩ : A) =
        ∏ ν : Fin m, φ ^ (ν : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨y, hy⟩ : A) := by
    intro m y hy
    rw [coe_norm_inf_ker_prod Finset.univ _ (fun ν : Fin m => hφνJ (ν : ℕ) y hy)]
    refine Finset.prod_congr rfl fun ν _ => ?_
    rw [smul_norm_inf_ker hLK (K.pow_mem hφK ν)]
  have hN1 : (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T1, hT1J⟩ : A) := by
    exact (coe_norm_field_eq hLK s hφK hdφ π1).trans (hNprod _ _ _).symm
  have hN3 : (norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨T3, hT3J⟩ : A) := by
    exact (coe_norm_field_eq hLK u hφK hdφ π3).trans (hNprod _ _ _).symm
  have hN2K := (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2).2
  have hN2 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
      (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
        ⟨φ ^ n • (π2 : A), hπ2J⟩ : A) := by
    have h0 : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
        (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
          ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by
      have h0' : (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) =
          ∏ ν : Fin 1, φ ^ (ν : ℕ) • (norm A ((K : Subgroup G) ⊓ D.deg.ker)
            ((L : Subgroup G) ⊓ D.deg.ker) ⟨(π2 : A), hJ t _ π2.2⟩ : A) :=
        coe_norm_field_eq hLK t hφK hdφ π2
      rw [Fin.prod_univ_one] at h0'
      simpa using h0'
    calc (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A)
        = φ ^ n • (norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 : A) :=
          (hN2K _ (K.pow_mem hφK n)).symm
      _ = φ ^ n • (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨(π2 : A), hJ t _ π2.2⟩ : A) := by rw [h0]
      _ = _ := smul_norm_inf_ker hLK (K.pow_mem hφK n) _
  have hNx : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 : A) *
        norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
          norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 := by
    rw [hN1, hN2, hN3]
    have e : (⟨x, hxJ⟩ : fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) =
        ⟨T1, hT1J⟩ * ⟨φ ^ n • (π2 : A), hπ2J⟩ / ⟨T3, hT3J⟩ := rfl
    rw [e, map_div, map_mul]
    rfl

  have hst : ∀ y : A, IsOpen (MulAction.stabilizer G y : Set G) :=
    fun y => IsDiscreteModule.isOpen_stabilizer y
  have hopen : IsOpen ((L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G)) :=
    ((L.isOpen.inter (hst _)).inter (hst _)).inter (hst _)
  have hone : (1 : G) ∈ (L : Set G) ∩ (MulAction.stabilizer G (π1 : A) : Set G) ∩
      (MulAction.stabilizer G (π2 : A) : Set G) ∩ (MulAction.stabilizer G (π3 : A) : Set G) :=
    ⟨⟨⟨L.one_mem, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩, Subgroup.one_mem _⟩
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hopen hone
  have : Finite (G ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
  set D0 := orderOf (φ : G ⧸ U.toSubgroup) with hD0def
  have hD0 : 0 < D0 := orderOf_pos _
  have hφD0U : φ ^ D0 ∈ U.toSubgroup := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hD0def, pow_orderOf_eq_one]
  obtain ⟨⟨⟨hψL, hψ1⟩, hψ2⟩, hψ3⟩ := hU hφD0U
  have hψπ1 : φ ^ D0 • (π1 : A) = π1 := MulAction.mem_stabilizer_iff.1 hψ1
  have hψπ2 : φ ^ D0 • (π2 : A) = π2 := MulAction.mem_stabilizer_iff.1 hψ2
  have hψπ3 : φ ^ D0 • (π3 : A) = π3 := MulAction.mem_stabilizer_iff.1 hψ3
  set g := (L : Subgroup G).relIndex K with hgdef
  have hg : 0 < g := Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero
    (H := (L : Subgroup G).subgroupOf K))
  set s1 := powLift hφK hdφ D0 hD0 with hs1
  set s2 := powLift hφK hdφ (g * D0) (Nat.mul_pos hg hD0) with hs2
  have hfix : ∀ (ν : ℕ) (y : A), φ ^ D0 • y = y → φ ^ D0 • φ ^ ν • y = φ ^ ν • y := by
    intro ν y hy
    rw [smul_smul, ← pow_add, add_comm, pow_add, mul_smul, hy]
  have hT1ψ : φ ^ D0 • T1 = T1 := by
    rw [hT1, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ1
  have hT3ψ : φ ^ D0 • T3 = T3 := by
    rw [hT3, Finset.smul_prod']
    exact Finset.prod_congr rfl fun ν _ => hfix ν _ hψπ3
  have hxP : x ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    refine ⟨hxJ, ?_⟩
    show φ ^ D0 • x = x
    rw [hxdef, smul_div', smul_mul', hT1ψ, hfix n _ hψπ2, hT3ψ]
  have hπ1P : (π1 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ s _ π1.2, hψπ1⟩
  have hπ3P : (π3 : A) ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) := by
    rw [FrobeniusLift.coe_field, mem_fixedModule_frobeniusClosure]
    exact ⟨hJ u _ π3.2, hψπ3⟩
  have haP : a ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G) :=
    Subgroup.div_mem _ hπ1P hπ3P

  have hπP : ∀ (v : D.FrobeniusLift K) (y : A)
      (hy : y ∈ fixedModule A ((v.field L hLK : OpenSubgroup G) : Subgroup G))
      (hyP : y ∈ fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)),
      D.valuation (s1.field L hLK) ⟨y, hyP⟩ = D.valuation (v.field L hLK) ⟨y, hy⟩ :=
    fun v y hy hyP => valuation_eq_of_inf_ker_eq
      ((v.field_inf_ker hLK).trans (s1.field_inf_ker hLK).symm) hy hyP
  have hau : D.valuation (s1.field L hLK) ⟨a, haP⟩ = 1 := by
    have e : (⟨a, haP⟩ : fixedModule A ((s1.field L hLK : OpenSubgroup G) : Subgroup G)) =
        ⟨(π1 : A), hπ1P⟩ / ⟨(π3 : A), hπ3P⟩ := rfl
    rw [e, map_div, hπP s _ π1.2 hπ1P, hπP u _ π3.2 hπ3P]
    simp [hπ1, hπ3]
  set N : fixedModule A (K : Subgroup G) :=
    norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π1 *
      norm A (K : Subgroup G) ((t.field L hLK : OpenSubgroup G) : Subgroup G) π2 /
        norm A (K : Subgroup G) ((u.field L hLK : OpenSubgroup G) : Subgroup G) π3 with hNdef
  have hNcoe : (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker) ⟨x, hxJ⟩ : A) =
      (N : A) := by
    rw [hNx]
    rfl
  have hvN : D.valuation K N = 1 := by
    rw [hNdef, map_div, map_mul, valuation_norm_prime hLK s hπ1, valuation_norm_prime hLK t hπ2,
      valuation_norm_prime hLK u hπ3, ← ofAdd_add, ← ofAdd_sub]
    show Multiplicative.ofAdd ((s.deg : ℤ̂) + ((1 : ℕ) : ℤ̂) - ((s.deg + 1 : ℕ) : ℤ̂)) = 1
    push_cast
    simp
  have hxu : D.valuation (s1.field L hLK) ⟨x, hxP⟩ = 1 := by
    have hNP : norm A (K : Subgroup G) ((s1.field L hLK : OpenSubgroup G) : Subgroup G) ⟨x, hxP⟩ =
        N ^ D0 := by
      apply Subtype.ext
      rw [coe_norm_field_eq hLK s1 hφK hdφ ⟨x, hxP⟩, SubmonoidClass.coe_pow]
      have h' : ∀ m : Fin s1.deg, φ ^ (m : ℕ) •
          (norm A ((K : Subgroup G) ⊓ D.deg.ker) ((L : Subgroup G) ⊓ D.deg.ker)
            ⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ : A) = (N : A) := by
        intro m
        rw [show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
            fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe]
        exact N.2 _ (K.pow_mem hφK _)
      rw [Finset.prod_congr rfl fun m _ => h' m, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      rfl
    have hv := D.valuation_norm (s1.field_le hLK) ⟨x, hxP⟩
    rw [hNP, map_pow, hvN, one_pow, FrobeniusLift.relInertiaDegree_field] at hv
    exact (ProfiniteInteger.pow_left_inj (n := s1.deg) hD0.ne').1 (by rw [one_pow]; exact hv.symm)

  set δ : G := φ ^ n * s.elt⁻¹ with hδdef
  have hδ : δ ∈ (K : Subgroup G) ⊓ D.deg.ker := by
    refine ⟨K.mul_mem (K.pow_mem hφK n) (K.inv_mem s.mem), ?_⟩
    show D.deg (φ ^ n * s.elt⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hdφ, s.deg_eq, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
    rw [hndef]
    push_cast
    rw [nsmul_eq_mul, add_neg_cancel, ofAdd_zero]
  have hδπ1 : δ • (π1 : A) = φ ^ n • (π1 : A) := by
    rw [hδdef, mul_smul, inv_smul_eq_iff.2 hσπ1.symm]
  have hφπ3 : φ • (π3 : A) = s.elt⁻¹ • (π3 : A) := by
    rw [eq_inv_smul_iff, ← mul_smul]
    exact hσφπ3
  have hδπ3 : δ • (π3 : A) = φ ^ (n + 1) • (π3 : A) := by
    rw [hδdef, mul_smul, ← hφπ3, ← mul_smul, ← pow_succ]
  have e2 : φ • φ ^ n • (π2 : A) = φ ^ n • (π2 : A) := by
    rw [smul_smul, ← pow_succ', pow_succ, mul_smul, hφπ2]
  have L1 : φ • x / x = (φ • T1 / T1) / (φ • T3 / T3) := by
    rw [hxdef, smul_div', smul_mul', e2, div_div_div_comm, mul_div_mul_comm, div_self', mul_one]
  have R1 : δ • a / a = (φ ^ n • (π1 : A) / π1) / (φ ^ (n + 1) • (π3 : A) / π3) := by
    rw [hadef, smul_div', hδπ1, hδπ3, div_div_div_comm]
  have hrel : φ • x / x = δ • a / a := by
    rw [L1, R1, hT1, hT3, smul_prod_pow_div, smul_prod_pow_div]

  obtain ⟨b, hb⟩ := exists_norm_eq_norm_inf_ker hLK hax hφK hdφ s1 s2 rfl hψL
    (by show φ ^ (g * D0) = (φ ^ D0) ^ g; rw [mul_comm, pow_mul]) rfl hxP haP hxu hau hδ hrel
  refine ⟨b, Subtype.ext ?_⟩
  rw [hb, show (⟨x, fixedModule_anti le_frobeniusClosure hxP⟩ :
      fixedModule A ((L : Subgroup G) ⊓ D.deg.ker)) = ⟨x, hxJ⟩ from rfl, hNcoe, hNdef]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_div]
  rw [div_eq_inv_mul]

end DegOne

section General

omit [TotallyDisconnectedSpace G] in

theorem exists_deg_eq (K : OpenSubgroup G) :
    ∃ φ ∈ (K : Subgroup G), D.deg φ = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
  obtain ⟨φ, hφ⟩ := D.relDeg_surjective K (Multiplicative.ofAdd 1)
  refine ⟨φ, φ.2, ?_⟩
  rw [← D.relDeg_pow, hφ, ← ofAdd_nsmul, nsmul_one]

theorem recFrob_mul (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (s t : D.FrobeniusLift K) :
    D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t := by
  obtain ⟨φ, hφK, hdφ⟩ := exists_deg_eq (D := D) K
  suffices h : ∀ (m : ℕ) (s t : D.FrobeniusLift K), t.deg = m + 1 →
      D.recFrob L hLK (s.mul t) = D.recFrob L hLK s * D.recFrob L hLK t by
    obtain ⟨m, hm⟩ : ∃ m, t.deg = m + 1 := ⟨t.deg - 1, by have := t.deg_pos; omega⟩
    exact h m s t hm
  intro m
  induction m with
  | zero =>
    intro s t ht
    have hdt : D.deg t.elt = Multiplicative.ofAdd (inertiaDegree D.deg K : ℤ̂) := by
      rw [t.deg_eq, ht, zero_add, one_mul]
    rw [recFrob_congr hLK (s := s.mul t) (t := s.mul (FrobeniusLift.ofDegOne t.mem hdt)) rfl,
      recFrob_congr hLK (s := t) (t := FrobeniusLift.ofDegOne t.mem hdt) rfl]
    exact recFrob_mul_ofDegOne hLK hax s t.mem hdt
  | succ k ih =>
    intro s t ht
    set φ1 := FrobeniusLift.ofDegOne (D := D) hφK hdφ with hφ1
    let t' : D.FrobeniusLift K :=
      { elt := t.elt * φ⁻¹
        mem := K.mul_mem t.mem (K.inv_mem hφK)
        deg := k + 1
        deg_pos := Nat.succ_pos k
        deg_eq := by
          rw [map_mul, map_inv, t.deg_eq, hdφ, ht, ← ofAdd_neg, ← ofAdd_add]
          push_cast
          ring_nf }
    have h1 : D.recFrob L hLK (s.mul t) = D.recFrob L hLK ((s.mul t').mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne, mul_assoc])
    have h2 : D.recFrob L hLK t = D.recFrob L hLK (t'.mul φ1) :=
      recFrob_congr hLK (by simp [FrobeniusLift.mul, t', φ1, FrobeniusLift.ofDegOne])
    rw [h1, h2, recFrob_mul_ofDegOne hLK hax _ hφK hdφ, recFrob_mul_ofDegOne hLK hax _ hφK hdφ,
      ih s t' rfl, mul_assoc]

end General

end ClassFieldData

end GroundTheory.LocalField.Abstract
end
