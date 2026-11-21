import Mathlib
import GroundTheory.LocalFields.AbstractLocalReciprocity.ReciprocityMap

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger

section Conj

variable {G : Type*} [Group G]

theorem map_conj_apply {M : Type*} [CommGroup M] (f : G →* M) (σ x : G) :
    f (σ * x * σ⁻¹) = f x := by
  rw [map_mul, map_mul, map_inv, mul_right_comm, mul_inv_cancel, one_mul]

theorem mem_map_conj {H : Subgroup G} {σ x : G} :
    x ∈ H.map (MulAut.conj σ).toMonoidHom ↔ σ⁻¹ * x * σ ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨σ⁻¹ * x * σ, h, by simp [mul_assoc]⟩

theorem coe_map_conj (H : Subgroup G) (σ : G) :
    (H.map (MulAut.conj σ).toMonoidHom : Set G) = (fun x => σ⁻¹ * x * σ) ⁻¹' (H : Set G) := by
  ext x
  exact mem_map_conj

theorem inertiaDegree_map_conj (d : G →* Multiplicative ℤ̂) (K : Subgroup G) (σ : G) :
    inertiaDegree d (K.map (MulAut.conj σ).toMonoidHom) = inertiaDegree d K := by
  have h : d.comp (MulAut.conj σ).toMonoidHom = d := MonoidHom.ext fun x => map_conj_apply d σ x
  rw [inertiaDegree, inertiaDegree, Subgroup.map_map, h]

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isClosed_map_conj {H : Subgroup G} (hH : IsClosed (H : Set G)) (σ : G) :
    IsClosed (H.map (MulAut.conj σ).toMonoidHom : Set G) := by
  rw [coe_map_conj]
  exact hH.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem map_conj_frobeniusClosure (d : G →* Multiplicative ℤ̂) (L : Subgroup G) (x ρ : G) :
    (frobeniusClosure d L x).map (MulAut.conj ρ).toMonoidHom =
      frobeniusClosure d (L.map (MulAut.conj ρ).toMonoidHom) (ρ * x * ρ⁻¹) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine frobeniusClosure_le ?_ ?_ ?_
    · exact isClosed_frobeniusClosure.preimage
        ((continuous_const.mul continuous_id).mul continuous_const)
    · exact mem_frobeniusClosure_self
    · intro y hy
      obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
      rw [Subgroup.mem_comap]
      refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨⟨y, hyL, rfl⟩, ?_⟩)
      rw [MonoidHom.mem_ker] at hyk ⊢
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_conj_apply, hyk]
  · refine frobeniusClosure_le (isClosed_map_conj isClosed_frobeniusClosure ρ)
      ⟨x, mem_frobeniusClosure_self, rfl⟩ ?_
    intro y hy
    obtain ⟨hyL, hyk⟩ := Subgroup.mem_inf.1 hy
    rw [mem_map_conj] at hyL ⊢
    refine le_frobeniusClosure (Subgroup.mem_inf.2 ⟨hyL, ?_⟩)
    rw [MonoidHom.mem_ker] at hyk ⊢
    have h : ρ⁻¹ * y * ρ = ρ⁻¹ * y * ρ⁻¹⁻¹ := by rw [inv_inv]
    rw [h, map_conj_apply, hyk]

theorem frobeniusClosure_mono {d : G →* Multiplicative ℤ̂} {L L' : Subgroup G} (h : L' ≤ L) (x : G) :
    frobeniusClosure d L' x ≤ frobeniusClosure d L x :=
  frobeniusClosure_le isClosed_frobeniusClosure mem_frobeniusClosure_self
    ((inf_le_inf_right _ h).trans le_frobeniusClosure)

def conjOpen (σ : G) (K : OpenSubgroup G) : OpenSubgroup G where
  toSubgroup := (K : Subgroup G).map (MulAut.conj σ).toMonoidHom
  isOpen' := by
    show IsOpen (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom : Subgroup G) : Set G)
    rw [coe_map_conj]
    exact K.isOpen.preimage ((continuous_const.mul continuous_id).mul continuous_const)

theorem coe_conjOpen (σ : G) (K : OpenSubgroup G) :
    ((conjOpen σ K : OpenSubgroup G) : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom :=
  rfl

theorem mem_conjOpen {σ x : G} {K : OpenSubgroup G} :
    x ∈ ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ↔ σ⁻¹ * x * σ ∈ (K : Subgroup G) :=
  mem_map_conj

theorem conjOpen_mono (σ : G) {K L : OpenSubgroup G} (h : L ≤ K) : conjOpen σ L ≤ conjOpen σ K :=
  fun _ hx => Subgroup.map_mono (f := (MulAut.conj σ).toMonoidHom) h hx

instance normal_conjOpen (σ : G) (K L : OpenSubgroup G) [hN : ((L : Subgroup G).subgroupOf K).Normal] :
    (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K)).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, mem_conjOpen] at hn ⊢
  have hnK : σ⁻¹ * (n : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 n.2
  have hgK : σ⁻¹ * (g : G) * σ ∈ (K : Subgroup G) := mem_conjOpen.1 g.2
  have := hN.conj_mem ⟨_, hnK⟩ (Subgroup.mem_subgroupOf.2 hn) ⟨_, hgK⟩
  rw [Subgroup.mem_subgroupOf] at this
  convert this using 1
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
  group

end Conj

section Maps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def galRestrict {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) :
    (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K' →* (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
  QuotientGroup.map _ _ (Subgroup.inclusion hK) fun x hx => by
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hL (Subgroup.mem_subgroupOf.1 hx)

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem galRestrict_mk {K L K' L' : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
    [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L) (τ : (K' : Subgroup G)) :
    galRestrict hK hL (τ : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨τ, hK τ.2⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :=
  rfl

noncomputable def normTateZero {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) :
    tateZero A (K' : Subgroup G) (L' : Subgroup G) →* tateZero A (K : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (norm A (K : Subgroup G) (K' : Subgroup G)) (by
    rintro _ ⟨b, rfl⟩
    rw [Subgroup.mem_comap, norm_norm (M := (L' : Subgroup G)) hL'K' hK,
      ← norm_norm (M := (L' : Subgroup G)) hL hLK]
    exact ⟨_, rfl⟩)

theorem normTateZero_mk {K L K' L' : OpenSubgroup G} (hK : K' ≤ K) (hL : L' ≤ L)
    (hL'K' : L' ≤ K') (hLK : L ≤ K) (a : fixedModule A (K' : Subgroup G)) :
    normTateZero hK hL hL'K' hLK (QuotientGroup.mk a : tateZero A (K' : Subgroup G) (L' : Subgroup G)) =
      (QuotientGroup.mk (norm A (K : Subgroup G) (K' : Subgroup G) a) :
        tateZero A (K : Subgroup G) (L : Subgroup G)) :=
  rfl

noncomputable def galConj (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal] :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ⧸
        ((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf (conjOpen σ K) :=
  QuotientGroup.map _ _
    ((K : Subgroup G).equivMapOfInjective _ (MulAut.conj σ).injective).toMonoidHom fun x hx => by
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact ⟨x, Subgroup.mem_subgroupOf.1 hx, rfl⟩

omit [CompactSpace G] in
theorem galConj_mk (σ : G) (K L : OpenSubgroup G) [((L : Subgroup G).subgroupOf K).Normal]
    (τ : (K : Subgroup G)) :
    galConj σ K L (τ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨σ * τ * σ⁻¹, τ, τ.2, rfl⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) :=
  rfl

def conjFixed (σ : G) (K : OpenSubgroup G) :
    fixedModule A (K : Subgroup G) →* fixedModule A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) where
  toFun a := ⟨σ • (a : A), smul_mem_fixedModule a.2 σ⟩
  map_one' := Subtype.ext (smul_one σ)
  map_mul' a b := Subtype.ext (smul_mul' σ (a : A) b)

theorem smul_norm_conjOpen (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (L : Subgroup G)) :
    σ • (norm A (K : Subgroup G) (L : Subgroup G) a : A) =
      norm A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G)
        (conjFixed σ L a) := by
  have : (((L : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((K : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex :=
    (inferInstance : (((conjOpen σ L : OpenSubgroup G) : Subgroup G).subgroupOf
      (conjOpen σ K)).FiniteIndex)
  exact smul_norm σ a

noncomputable def tateZeroConj (σ : G) (K L : OpenSubgroup G) :
    tateZero A (K : Subgroup G) (L : Subgroup G) →*
      tateZero A ((conjOpen σ K : OpenSubgroup G) : Subgroup G) ((conjOpen σ L : OpenSubgroup G) : Subgroup G) :=
  QuotientGroup.map _ _ (conjFixed σ K) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨conjFixed σ L b, Subtype.ext (smul_norm_conjOpen σ K L b).symm⟩)

theorem tateZeroConj_mk (σ : G) (K L : OpenSubgroup G) (a : fixedModule A (K : Subgroup G)) :
    tateZeroConj σ K L (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk (conjFixed σ K a) : tateZero A _ _) :=
  rfl

end Maps

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A] {D : ClassFieldData G A}

theorem valuation_conj (σ : G) {K K' : OpenSubgroup G}
    (hK' : (K' : Subgroup G) = (K : Subgroup G).map (MulAut.conj σ).toMonoidHom)
    (a : fixedModule A (K : Subgroup G)) (b : fixedModule A (K' : Subgroup G))
    (hb : (b : A) = σ • (a : A)) : D.valuation K' b = D.valuation K a := by
  have hf : inertiaDegree D.deg (K' : Subgroup G) = inertiaDegree D.deg (K : Subgroup G) := by
    rw [hK', inertiaDegree_map_conj]
  rw [valuation_eq_iff, hf, valuation_pow D K a]
  congr 1
  apply Subtype.ext
  have htop : (⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulAut.conj σ).surjective
  have : (((K : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((⊤ : Subgroup G).map (MulAut.conj σ).toMonoidHom)).FiniteIndex := by
    rw [← hK', htop]
    infer_instance
  have h1 := smul_norm σ (K := ⊤) a
  rw [(norm A ⊤ (K : Subgroup G) a).2 σ (Subgroup.mem_top σ), coe_norm_congr htop hK'.symm] at h1
  rw [h1]
  exact congrArg (fun x => (norm A ⊤ (K' : Subgroup G) x : A)) (Subtype.ext hb)

variable [TotallyDisconnectedSpace G]

section Restriction

noncomputable def FrobeniusLift.toBase {K K' : OpenSubgroup G} (hK : K' ≤ K) (s : D.FrobeniusLift K') :
    D.FrobeniusLift K where
  elt := s.elt
  mem := hK s.mem
  deg := s.deg * relInertiaDegree D.deg K K'
  deg_pos := Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK))
  deg_eq := by
    rw [s.deg_eq, inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G))
      (L := (K' : Subgroup G)) hK, Nat.mul_assoc]

theorem reciprocity_galRestrict (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    {K L K' L' : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (hL'K' : L' ≤ K') [((L' : Subgroup G).subgroupOf K').Normal] (hK : K' ≤ K) (hL : L' ≤ L)
    (q : (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') :
    D.reciprocity hLK hax (galRestrict hK hL q) =
      normTateZero hK hL hL'K' hLK (D.reciprocity hL'K' hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hL'K' q
  set t := s.toBase hK with htdef
  have ht : t.deg = s.deg * relInertiaDegree D.deg K K' := rfl
  have hle : s.field L' hL'K' ≤ t.field L hLK := fun x hx => frobeniusClosure_mono hL s.elt hx
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L' hL'K')
  have hrel : relInertiaDegree D.deg (t.field L hLK) (s.field L' hL'K') = 1 := by
    have h1 := inertiaDegree_eq_mul D.surjective_deg
      (K := ((t.field L hLK : OpenSubgroup G) : Subgroup G))
      (L := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle
    rw [s.inertiaDegree_field hL'K', t.inertiaDegree_field hLK, ht,
      inertiaDegree_eq_mul D.surjective_deg (K := (K : Subgroup G)) (L := (K' : Subgroup G)) hK] at h1
    have hpos : 0 < s.deg * relInertiaDegree D.deg K K' * inertiaDegree D.deg K :=
      Nat.mul_pos (Nat.mul_pos s.deg_pos (Nat.pos_of_ne_zero (D.relInertiaDegree_ne_zero hK)))
        (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [one_mul]
    exact h1.symm.trans (Nat.mul_assoc _ _ _).symm
  set π0 := norm A ((t.field L hLK : OpenSubgroup G) : Subgroup G)
    ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G) π with hπ0def
  have hπ0 : D.valuation (t.field L hLK) π0 = Multiplicative.ofAdd 1 := by
    rw [hπ0def, D.valuation_norm hle, hrel, pow_one, hπ]
  have e1 : galRestrict hK hL ((⟨s.elt, s.mem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L' : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := rfl
  rw [e1, D.reciprocity_mk_eq_norm hLK hax t hπ0, D.reciprocity_mk_eq_norm hL'K' hax s hπ,
    normTateZero_mk, hπ0def,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) (s.field_le hL'K') hK,
    norm_norm (M := ((s.field L' hL'K' : OpenSubgroup G) : Subgroup G)) hle (t.field_le hLK)]

end Restriction

section Conjugation

def FrobeniusLift.conj (ρ : G) {K : OpenSubgroup G} (s : D.FrobeniusLift K) :
    D.FrobeniusLift (conjOpen ρ K) where
  elt := ρ * s.elt * ρ⁻¹
  mem := ⟨s.elt, s.mem, rfl⟩
  deg := s.deg
  deg_pos := s.deg_pos
  deg_eq := by
    rw [map_conj_apply, s.deg_eq, coe_conjOpen, inertiaDegree_map_conj]

theorem FrobeniusLift.coe_field_conj (ρ : G) {K L : OpenSubgroup G} (hLK : L ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (s : D.FrobeniusLift K) :
    (((s.conj ρ).field (conjOpen ρ L) (conjOpen_mono ρ hLK) : OpenSubgroup G) : Subgroup G) =
      ((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj ρ).toMonoidHom :=
  (map_conj_frobeniusClosure D.deg (L : Subgroup G) s.elt ρ).symm

theorem reciprocity_galConj (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (σ : G)
    {K L : OpenSubgroup G} (hLK : L ≤ K) [((L : Subgroup G).subgroupOf K).Normal]
    (q : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    D.reciprocity (conjOpen_mono σ hLK) hax (galConj σ K L q) =
      tateZeroConj σ K L (D.reciprocity hLK hax q) := by
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK q
  set t := s.conj σ with htdef
  have hfield := s.coe_field_conj σ hLK
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  let π' : fixedModule A (((t.field (conjOpen σ L) (conjOpen_mono σ hLK)) : OpenSubgroup G) :
      Subgroup G) := ⟨σ • (π : A), hfield ▸ smul_mem_fixedModule π.2 σ⟩
  have hπ' : D.valuation (t.field (conjOpen σ L) (conjOpen_mono σ hLK)) π' = Multiplicative.ofAdd 1 := by
    rw [valuation_conj σ hfield π π' rfl, hπ]
  have e1 : galConj σ K L ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) :
      (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) =
      ((⟨t.elt, t.mem⟩ : ((conjOpen σ K : OpenSubgroup G) : Subgroup G)) : _ ⧸ _) := rfl
  rw [e1, D.reciprocity_mk_eq_norm (conjOpen_mono σ hLK) hax t hπ',
    D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroConj_mk]
  congr 1
  apply Subtype.ext
  show _ = σ • (norm A (K : Subgroup G) ((s.field L hLK : OpenSubgroup G) : Subgroup G) π : A)
  rw [smul_norm_conjOpen σ K (s.field L hLK) π]
  have : ((((s.field L hLK : OpenSubgroup G) : Subgroup G).map (MulAut.conj σ).toMonoidHom).subgroupOf
      ((conjOpen σ K : OpenSubgroup G) : Subgroup G)).FiniteIndex := by
    rw [← hfield]
    infer_instance
  exact coe_norm_congr rfl hfield _

end Conjugation

end ClassFieldData

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

section DoubleCoset

variable {G : Type*} [Group G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]

def doubleCosetMap {K K' S M : Subgroup G} (hK'K : K' ≤ K) {τ : G} (hτ : τ ∈ K)
    (hM : ∀ k ∈ K', k ∈ M → τ * k * τ⁻¹ ∈ S) : K' ⧸ M.subgroupOf K' → K ⧸ S.subgroupOf K :=
  Quotient.map' (fun k : K' => (⟨k * τ⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem hτ)⟩ : K)) fun k k' h => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at h ⊢
    have := hM _ (K'.mul_mem (K'.inv_mem k.2) k'.2) (by simpa using h)
    simpa [mul_assoc] using this

theorem coe_norm_eq_prod_norm_inf {K K' S : Subgroup G} (hK'K : K' ≤ K)
    [(S.subgroupOf K).FiniteIndex] {ι : Type*} [Fintype ι] (τ : ι → G) (hτ : ∀ i, τ i ∈ K)
    (M : ι → Subgroup G) [∀ i, ((M i).subgroupOf K').FiniteIndex]
    (hM : ∀ i, ∀ k ∈ K', k ∈ M i ↔ τ i * k * (τ i)⁻¹ ∈ S)
    (hcover : ∀ c ∈ K, ∃ i, ∃ k ∈ K', τ i * k⁻¹ * c ∈ S)
    (hdisj : ∀ i j, ∀ k ∈ K', ∀ k' ∈ K', τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ S → i = j)
    (a : fixedModule A S) (ha : ∀ i, (τ i)⁻¹ • (a : A) ∈ fixedModule A (M i)) :
    (norm A K S a : A) = ∏ i, (norm A K' (M i) ⟨(τ i)⁻¹ • (a : A), ha i⟩ : A) := by
  classical
  let f : ∀ i, K' ⧸ (M i).subgroupOf K' → K ⧸ S.subgroupOf K := fun i =>
    doubleCosetMap hK'K (hτ i) (fun k hk hkM => (hM i k hk).1 hkM)
  let F : (Σ i, K' ⧸ (M i).subgroupOf K') → K ⧸ S.subgroupOf K := fun p => f p.1 p.2
  have hFmk : ∀ i (k : K'), F ⟨i, (k : K' ⧸ (M i).subgroupOf K')⟩ =
      ((⟨k * (τ i)⁻¹, K.mul_mem (hK'K k.2) (K.inv_mem (hτ i))⟩ : K) : K ⧸ S.subgroupOf K) :=
    fun _ _ => rfl
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, x⟩ ⟨j, y⟩ hxy
      induction x using QuotientGroup.induction_on with
      | H k =>
      induction y using QuotientGroup.induction_on with
      | H k' =>
        rw [hFmk, hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
        have hxy' : τ i * (k : G)⁻¹ * k' * (τ j)⁻¹ ∈ S := by simpa [mul_assoc] using hxy
        obtain rfl := hdisj i j k k.2 k' k'.2 hxy'
        have hkk : (k : G)⁻¹ * k' ∈ M i :=
          (hM i _ (K'.mul_mem (K'.inv_mem k.2) k'.2)).2 (by simpa [mul_assoc] using hxy')
        have : ((k : K' ⧸ (M i).subgroupOf K')) = (k' : K' ⧸ (M i).subgroupOf K') := by
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hkk
        rw [this]
    · intro y
      induction y using QuotientGroup.induction_on with
      | H c =>
        obtain ⟨i, k, hk, hc⟩ := hcover c c.2
        refine ⟨⟨i, ((⟨k, hk⟩ : K') : K' ⧸ (M i).subgroupOf K')⟩, ?_⟩
        rw [hFmk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
        simpa [mul_assoc] using hc
  have : ∀ i, Fintype (K' ⧸ (M i).subgroupOf K') := fun i => Fintype.ofFinite _
  let _ := Fintype.ofFinite (K ⧸ S.subgroupOf K)
  rw [coe_norm, ← finprod_comp_equiv (Equiv.ofBijective F hF), finprod_eq_prod_of_fintype,
    Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [coe_norm, finprod_eq_prod_of_fintype]
  refine Finset.prod_congr rfl fun x _ => ?_
  induction x using QuotientGroup.induction_on with
  | H k =>
    rw [Equiv.ofBijective_apply, hFmk, cosetSMul_mk, cosetSMul_mk]
    exact mul_smul _ _ _

theorem conj_mem_of_normal {K L : Subgroup G} [hN : (L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) (hkL : k ∈ L) : τ * k * τ⁻¹ ∈ L := by
  have := hN.conj_mem ⟨k, hk⟩ (Subgroup.mem_subgroupOf.2 hkL) ⟨τ, hτ⟩
  simpa [Subgroup.mem_subgroupOf] using this

theorem conj_mem_iff_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] {τ k : G} (hτ : τ ∈ K)
    (hk : k ∈ K) : τ * k * τ⁻¹ ∈ L ↔ k ∈ L := by
  refine ⟨fun h => ?_, conj_mem_of_normal hτ hk⟩
  have := conj_mem_of_normal (K.inv_mem hτ) (K.mul_mem (K.mul_mem hτ hk) (K.inv_mem hτ)) h
  simpa [mul_assoc] using this

end DoubleCoset

section Inclusion

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {A : Type*} [CommGroup A] [MulDistribMulAction G A]

theorem norm_mem_range_norm_of_le {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (b : fixedModule A (L : Subgroup G)) :
    (⟨norm A (K : Subgroup G) (L : Subgroup G) b,
        fixedModule_anti hK'K (norm A (K : Subgroup G) (L : Subgroup G) b).2⟩ :
        fixedModule A (K' : Subgroup G)) ∈ (norm A (K' : Subgroup G) (L : Subgroup G)).range := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  let _ := Fintype.ofFinite ((K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K)
  let τ : (K : Subgroup G) ⧸ (K' : Subgroup G).subgroupOf K → G := fun i => ((Quotient.out i : K) : G)
  have hτ : ∀ i, τ i ∈ (K : Subgroup G) := fun i => (Quotient.out i : K).2
  have ha : ∀ i, (τ i)⁻¹ • (b : A) ∈ fixedModule A (L : Subgroup G) := fun i =>
    smul_mem_fixedModule_of_normal hLK ((K : Subgroup G).inv_mem (hτ i)) b.2
  have key := coe_norm_eq_prod_norm_inf (A := A) (S := (L : Subgroup G)) hK'K τ hτ
    (fun _ => (L : Subgroup G)) (fun i k hk => (conj_mem_iff_of_normal (hτ i) (hK'K hk)).symm)
    (fun c hc => by
      obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ((K' : Subgroup G).subgroupOf K)
        (⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G))
      refine ⟨((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _), (h : G),
        Subgroup.mem_subgroupOf.1 h.2, ?_⟩
      have : τ ((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : _ ⧸ _) = c⁻¹ * (h : G) := by
        simp only [τ, hh, Subgroup.coe_mul]
      rw [this]
      simp)
    (fun i j k hk k' hk' hy => by
      rw [← QuotientGroup.out_eq' i, ← QuotientGroup.out_eq' j, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have hyK : τ i * k⁻¹ * k' * (τ j)⁻¹ ∈ (K : Subgroup G) := hLK hy
      have hc := conj_mem_of_normal ((K : Subgroup G).inv_mem (hτ j)) ((K : Subgroup G).inv_mem hyK)
        ((L : Subgroup G).inv_mem hy)
      have hmem : k⁻¹ * k' * ((τ j)⁻¹ * (τ i * k⁻¹ * k' * (τ j)⁻¹)⁻¹ * (τ j)⁻¹⁻¹) ∈
          (K' : Subgroup G) :=
        (K' : Subgroup G).mul_mem ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk) hk')
          (hLK' hc)
      convert hmem using 1
      simp only [Subgroup.coe_mul, InvMemClass.coe_inv, τ]
      group)
    b ha
  refine ⟨∏ i, ⟨(τ i)⁻¹ • (b : A), ha i⟩, Subtype.ext ?_⟩
  rw [map_prod]
  simp only [SubmonoidClass.coe_finsetProd]
  exact key.symm

noncomputable def tateZeroIncl {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] :
    tateZero A (K : Subgroup G) (L : Subgroup G) →* tateZero A (K' : Subgroup G) (L : Subgroup G) :=
  QuotientGroup.map _ _ (Subgroup.inclusion (fixedModule_anti (A := A) hK'K)) (by
    rintro _ ⟨b, rfl⟩
    exact norm_mem_range_norm_of_le hLK' hK'K b)

theorem tateZeroIncl_mk {K K' L : OpenSubgroup G} (hLK' : L ≤ K') (hK'K : K' ≤ K)
    [((L : Subgroup G).subgroupOf K).Normal] (a : fixedModule A (K : Subgroup G)) :
    tateZeroIncl hLK' hK'K (QuotientGroup.mk a : tateZero A (K : Subgroup G) (L : Subgroup G)) =
      (QuotientGroup.mk ⟨(a : A), fixedModule_anti hK'K a.2⟩ : tateZero A (K' : Subgroup G) (L : Subgroup G)) :=
  rfl

end Inclusion

end GroundTheory.LocalField.Abstract
end

section
namespace GroundTheory.LocalField.Abstract

open ProfiniteInteger MulAction

section Transfer

theorem map_transfer {Γ : Type*} [Group Γ] {H : Subgroup Γ} [H.FiniteIndex] {B C : Type*} [CommGroup B]
    [CommGroup C] (φ : H →* B) (f : B →* C) (g : Γ) : f (φ.transfer g) = (f.comp φ).transfer g := by
  classical
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers g) (Γ ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot,
    MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot, map_prod]
  rfl

end Transfer

section FixedField

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {d : G →* Multiplicative ℤ̂} {L : Subgroup G} {σ : G}

theorem exists_eq_zpow_mul_of_mem_frobeniusClosure (hL : IsOpen (L : Set G))
    (hσ : σ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {y : G}
    (hy : y ∈ frobeniusClosure d L σ) : ∃ m : ℤ, ∃ l ∈ L, y = σ ^ m * l := by
  have hy' : y ∈ closure ((Subgroup.zpowers σ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact hy
  have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' (L : Set G)) :=
    hL.preimage (continuous_const.mul continuous_id)
  have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' (L : Set G) := by
    show y⁻¹ * y ∈ L
    rw [inv_mul_cancel]
    exact L.one_mem
  obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
  obtain ⟨m, j, hj, rfl⟩ := (mem_zpowers_sup_iff hσ).1 hhS
  refine ⟨m, j * (y⁻¹ * (σ ^ m * j))⁻¹, L.mul_mem hj.1 (L.inv_mem hhO), by group⟩

variable [CompactSpace G] [TotallyDisconnectedSpace G]

theorem frobeniusClosure_pow_eq_inf (hd : Continuous d) (hL : IsOpen (L : Set G)) {K' : Subgroup G}
    (hK' : IsOpen (K' : Set G)) (hLK' : L ≤ K') {ρ : G}
    (hρ : ρ ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G)) {N : ℕ} (hN : N ≠ 0)
    (hdρ : d ρ = Multiplicative.ofAdd (N : ℤ̂)) {f : ℕ} (hf : 0 < f) (hρf : ρ ^ f ∈ K')
    (hdiv : ∀ k : ℤ, ρ ^ k ∈ K' → (f : ℤ) ∣ k) :
    frobeniusClosure d L (ρ ^ f) = K' ⊓ frobeniusClosure d L ρ := by
  have hρf' : ρ ^ f ∈ Subgroup.normalizer ((L ⊓ d.ker : Subgroup G) : Set G) := Subgroup.pow_mem _ hρ f
  have hdρf : d (ρ ^ f) = Multiplicative.ofAdd ((f * N : ℕ) : ℤ̂) := by
    rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul, Nat.cast_mul]
  have hle : frobeniusClosure d L (ρ ^ f) ≤ frobeniusClosure d L ρ :=
    frobeniusClosure_le isClosed_frobeniusClosure (Subgroup.pow_mem _ mem_frobeniusClosure_self f)
      le_frobeniusClosure
  apply le_antisymm
  · refine frobeniusClosure_le ((OpenSubgroup.isClosed ⟨K', hK'⟩).inter isClosed_frobeniusClosure)
      ⟨hρf, Subgroup.pow_mem _ mem_frobeniusClosure_self f⟩ ?_
    exact le_inf (inf_le_left.trans hLK') le_frobeniusClosure
  · intro y hy
    obtain ⟨hyK', hyS⟩ := Subgroup.mem_inf.1 hy
    set M : ℕ+ := ⟨f * N, Nat.mul_pos hf (Nat.pos_of_ne_zero hN)⟩ with hMdef
    set V : Set G := (L : Set G) ∩ d ⁻¹' (Multiplicative.toAdd ⁻¹' (multiples M : Set ℤ̂)) with hVdef
    have hV : IsOpen V := hL.inter ((isOpen_multiples M).preimage (continuous_toAdd.comp hd))
    have hO : IsOpen ((fun z => y⁻¹ * z) ⁻¹' V) := hV.preimage (continuous_const.mul continuous_id)
    have hyO : y ∈ (fun z => y⁻¹ * z) ⁻¹' V := by
      simp only [Set.mem_preimage, inv_mul_cancel, hVdef, Set.mem_inter_iff, map_one, toAdd_one]
      exact ⟨L.one_mem, (multiples M).zero_mem⟩
    have hy' : y ∈ closure ((Subgroup.zpowers ρ ⊔ (L ⊓ d.ker) : Subgroup G) : Set G) := by
      rw [← Subgroup.topologicalClosure_coe]
      exact hyS
    obtain ⟨h, hhO, hhS⟩ := mem_closure_iff.1 hy' _ hO hyO
    have hhS' : h ∈ frobeniusClosure d L ρ := Subgroup.le_topologicalClosure _ hhS
    obtain ⟨k, j, hj, rfl⟩ := (mem_zpowers_sup_iff hρ).1 hhS
    obtain ⟨huL, huM⟩ := hhO
    set u := y⁻¹ * (ρ ^ k * j) with hudef

    have hρk : ρ ^ k ∈ K' := by
      have : ρ ^ k = y * u * j⁻¹ := by rw [hudef]; group
      rw [this]
      exact K'.mul_mem (K'.mul_mem hyK' (hLK' huL)) (K'.inv_mem (hLK' hj.1))
    obtain ⟨k', rfl⟩ := hdiv k hρk
    have hhf : ρ ^ ((f : ℤ) * k') * j ∈ frobeniusClosure d L (ρ ^ f) := by
      refine Subgroup.mul_mem _ ?_ (le_frobeniusClosure hj)
      rw [zpow_mul, zpow_natCast]
      exact Subgroup.zpow_mem _ mem_frobeniusClosure_self k'

    have huS : u ∈ frobeniusClosure d L ρ :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hyS) hhS'
    have hmap := map_frobeniusClosure hd hρf' hdρf
    have hdu : d u ∈ (frobeniusClosure d L (ρ ^ f)).map d := by
      rw [hmap]
      exact huM
    obtain ⟨z, hz, hzu⟩ := hdu
    have hzu' : z⁻¹ * u ∈ frobeniusClosure d L ρ ⊓ d.ker := by
      refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ (hle hz)) huS, ?_⟩
      exact (MonoidHom.mem_ker).2 (by rw [map_mul, map_inv, hzu, inv_mul_cancel])
    rw [frobeniusClosure_inf_ker hd hL hρ hN hdρ] at hzu'
    have hu : u ∈ frobeniusClosure d L (ρ ^ f) := by
      have : u = z * (z⁻¹ * u) := by group
      rw [this]
      exact Subgroup.mul_mem _ hz (le_frobeniusClosure hzu')
    have : y = ρ ^ ((f : ℤ) * k') * j * u⁻¹ := by rw [hudef]; group
    rw [this]
    exact Subgroup.mul_mem _ hhf (Subgroup.inv_mem _ hu)

end FixedField

section Ver

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] in

theorem map_conj_eq_of_normal {K L : Subgroup G} [(L.subgroupOf K).Normal] (hLK : L ≤ K) {τ : G}
    (hτ : τ ∈ K) : L.map (MulAut.conj τ).toMonoidHom = L := by
  ext y
  rw [mem_map_conj]
  constructor
  · intro h
    have := conj_mem_of_normal hτ (hLK h) h
    simpa [mul_assoc] using this
  · intro h
    have := conj_mem_of_normal (K.inv_mem hτ) (hLK h) h
    simpa using this

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem galRestrict_injective (hK'K : K' ≤ K) :
    Function.Injective (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [galRestrict_mk, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hq

omit [IsTopologicalGroup G] [CompactSpace G] in

theorem mk_mem_range_galRestrict_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (k : (K : Subgroup G)) :
    (k : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ∈
      (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range ↔
      (k : G) ∈ (K' : Subgroup G) := by
  constructor
  · rintro ⟨q, hq⟩
    induction q using QuotientGroup.induction_on with
    | H k' =>
      rw [galRestrict_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hq
      have h := (K' : Subgroup G).mul_mem k'.2 (hLK' hq)
      simpa using h
  · intro hk
    exact ⟨((⟨k, hk⟩ : (K' : Subgroup G)) : _ ⧸ _), rfl⟩

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (a b : (K : Subgroup G)) :
    ((a : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
        _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((b : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (a : G)⁻¹ * b ∈ (K' : Subgroup G) := by
  rw [QuotientGroup.eq, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    mk_mem_range_galRestrict_iff hLK' hK'K]
  simp

omit [IsTopologicalGroup G] [CompactSpace G] in
theorem zpow_smul_mk_mk_eq_iff (hLK' : L ≤ K') (hK'K : K' ≤ K) (σ x : (K : Subgroup G)) (k : ℤ) :
    ((σ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ^ k) •
        ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
          _ ⧸ (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range) =
      ((x : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ _) ↔
      (x : G)⁻¹ * (σ : G) ^ k * x ∈ (K' : Subgroup G) := by
  rw [MulAction.Quotient.smul_mk, smul_eq_mul, ← QuotientGroup.mk_zpow, ← QuotientGroup.mk_mul,
    mk_mk_eq_iff hLK' hK'K]
  have e : (((σ ^ k * x : (K : Subgroup G)) : G))⁻¹ * x = ((x : G)⁻¹ * (σ : G) ^ k * x)⁻¹ := by
    simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
    group
  rw [e, Subgroup.inv_mem_iff]

noncomputable def verlagerung (hK'K : K' ≤ K) :
    (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K →*
      Abelianization ((K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') :=
  ((Abelianization.of).comp
    (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom).transfer

end Ver

namespace ClassFieldData

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {A : Type*} [CommGroup A] [MulDistribMulAction G A]
  {D : ClassFieldData G A}

omit [TotallyDisconnectedSpace G] in

theorem exists_frobeniusLift_of_deg {K : OpenSubgroup G} {x : G} (hx : x ∈ (K : Subgroup G)) {N : ℕ}
    (hN : 0 < N) (hd : D.deg x = Multiplicative.ofAdd (N : ℤ̂)) :
    ∃ s : D.FrobeniusLift K, s.elt = x := by
  have hm := toAdd_deg_mem_multiples (D := D) K hx
  rw [hd, toAdd_ofAdd, ← Int.cast_natCast,
    intCast_mem_multiples_iff (Nat.pos_of_ne_zero (D.inertiaDegree_ne_zero K))] at hm
  obtain ⟨m, rfl⟩ := Int.natCast_dvd_natCast.1 hm
  have hm0 : 0 < m := Nat.pos_of_mul_pos_left hN
  exact ⟨⟨x, hx, m, hm0, by rw [hd, Nat.mul_comm]⟩, rfl⟩

section Ver

variable {K K' L : OpenSubgroup G} [((L : Subgroup G).subgroupOf K).Normal]
  [((L : Subgroup G).subgroupOf K').Normal]

theorem reciprocity_mk_conj_pow (hax : ClassFieldAxiom G A) [IsDiscreteModule G A]
    (hLK' : L ≤ K') (hK'K : K' ≤ K) (s : D.FrobeniusLift K) (x : (K : Subgroup G)) {f : ℕ}
    (hf0 : 0 < f) (hf : ∀ k : ℤ, (x : G)⁻¹ * s.elt ^ k * x ∈ (K' : Subgroup G) ↔ (f : ℤ) ∣ k)
    (hmem : (x : G)⁻¹ * s.elt ^ f * x ∈ (K' : Subgroup G))
    {π : fixedModule A ((s.field L (hLK'.trans hK'K) : OpenSubgroup G) : Subgroup G)}
    (hπ : D.valuation (s.field L (hLK'.trans hK'K)) π = Multiplicative.ofAdd 1) :
    D.reciprocity hLK' hax ((⟨_, hmem⟩ : (K' : Subgroup G)) :
      (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L (hLK'.trans hK'K)) : OpenSubgroup G) : Subgroup G)
        ⟨(x : G)⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : G, ρ = (x : G)⁻¹ * s.elt * x := ⟨_, rfl⟩
  have hρK : ρ ∈ (K : Subgroup G) := by
    rw [hρdef]
    exact (K : Subgroup G).mul_mem ((K : Subgroup G).mul_mem ((K : Subgroup G).inv_mem x.2) s.mem) x.2
  have hρn := FrobeniusLift.mem_normalizer (D := D) hLK hρK
  have hdρ : D.deg ρ = Multiplicative.ofAdd ((s.deg * inertiaDegree D.deg K : ℕ) : ℤ̂) := by
    rw [hρdef, map_mul, map_mul, map_inv, mul_comm _ (D.deg s.elt), mul_assoc, inv_mul_cancel,
      mul_one, s.deg_eq]
  have hN : s.deg * inertiaDegree D.deg K ≠ 0 := s.degree_ne_zero
  have hρz : ∀ k : ℤ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_zpow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hρn' : ∀ k : ℕ, ρ ^ k = (x : G)⁻¹ * s.elt ^ k * x := fun k => by
    have := conj_pow (i := k) (a := (x : G)⁻¹) (b := s.elt)
    simpa [hρdef] using this
  have hmemρ : ρ ^ f ∈ (K' : Subgroup G) := by
    rw [hρn']
    exact hmem
  have hdivρ : ∀ k : ℤ, ρ ^ k ∈ (K' : Subgroup G) → (f : ℤ) ∣ k := fun k hk =>
    (hf k).1 (by rwa [hρz] at hk)
  obtain ⟨t, ht⟩ := exists_frobeniusLift_of_deg (D := D) (K := K') hmemρ
    (N := f * (s.deg * inertiaDegree D.deg K)) (Nat.mul_pos hf0 (Nat.pos_of_ne_zero hN))
    (by rw [map_pow, hdρ, ← ofAdd_nsmul, nsmul_eq_mul]; norm_cast)
  have hconjS : ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) =
      frobeniusClosure D.deg L ρ := by
    rw [coe_conjOpen, s.coe_field hLK, map_conj_frobeniusClosure,
      map_conj_eq_of_normal hLK ((K : Subgroup G).inv_mem x.2), inv_inv, hρdef]
  have hkey := frobeniusClosure_pow_eq_inf D.continuous_deg L.isOpen K'.isOpen hLK' hρn hN hdρ hf0
    hmemρ hdivρ
  have htfield : ((t.field L hLK' : OpenSubgroup G) : Subgroup G) =
      ((K' ⊓ conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) := by
    rw [t.coe_field hLK', ht, hkey, ← hconjS]
    rfl
  have hle : t.field L hLK' ≤ conjOpen (x : G)⁻¹ (s.field L hLK) := by
    intro y hy
    have : y ∈ ((t.field L hLK' : OpenSubgroup G) : Subgroup G) := hy
    rw [htfield] at this
    exact (Subgroup.mem_inf.1 this).2
  have ha : (x : G)⁻¹ • (π : A) ∈
      fixedModule A ((conjOpen (x : G)⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G) :=
    smul_mem_fixedModule π.2 _
  have hv1 : D.valuation (conjOpen (x : G)⁻¹ (s.field L hLK)) ⟨_, ha⟩ = Multiplicative.ofAdd 1 := by
    rw [valuation_conj (x : G)⁻¹ rfl π ⟨_, ha⟩ rfl, hπ]
  have hram : relRamificationIndex D.deg (conjOpen (x : G)⁻¹ (s.field L hLK)) (t.field L hLK') = 1 := by
    rw [relRamificationIndex, Subgroup.relIndex_eq_one]
    intro y hy
    obtain ⟨hyk, hyS⟩ := Subgroup.mem_inf.1 hy
    have hy' : y ∈ frobeniusClosure D.deg L ρ ⊓ D.deg.ker := by
      refine ⟨?_, hyk⟩
      rw [← hconjS]
      exact hyS
    rw [frobeniusClosure_inf_ker D.continuous_deg L.isOpen hρn hN hdρ] at hy'
    show y ∈ frobeniusClosure D.deg L t.elt
    rw [ht]
    exact le_frobeniusClosure hy'
  have hπ' : D.valuation (t.field L hLK') ⟨(x : G)⁻¹ • (π : A), fixedModule_anti hle ha⟩ =
      Multiplicative.ofAdd 1 := by
    rw [D.valuation_of_mem hle ha, hv1, hram, pow_one]
  have he : ((⟨_, hmem⟩ : (K' : Subgroup G)) : (K' : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K') =
      ((⟨t.elt, t.mem⟩ : (K' : Subgroup G)) : _ ⧸ _) := by
    congr 1
    apply Subtype.ext
    show _ = t.elt
    rw [ht, hρn']
  rw [he, D.reciprocity_mk_eq_norm hLK' hax t hπ']
  congr 1
  apply Subtype.ext
  exact coe_norm_congr rfl htfield _

theorem reciprocity_verlagerung (hax : ClassFieldAxiom G A) [IsDiscreteModule G A] (hLK' : L ≤ K')
    (hK'K : K' ≤ K) (g : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
    Abelianization.lift (D.reciprocity hLK' hax) (verlagerung hK'K g) =
      tateZeroIncl hLK' hK'K (D.reciprocity (hLK'.trans hK'K) hax g) := by
  classical
  have hLK : L ≤ K := hLK'.trans hK'K
  obtain ⟨s, rfl⟩ := exists_frobeniusLift_mk (D := D) hLK g
  obtain ⟨π, hπ⟩ := D.exists_prime (s.field L hLK)
  rw [D.reciprocity_mk_eq_norm hLK hax s hπ, tateZeroIncl_mk, verlagerung, map_transfer]
  set H := (galRestrict (K := K) (L := L) (K' := K') (L' := L) hK'K le_rfl).range with hH
  set γ : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K :=
    ((⟨s.elt, s.mem⟩ : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) with hγ
  let _ : Fintype (Quotient (orbitRel (Subgroup.zpowers γ)
    (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H))) := Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  let τ : Quotient (orbitRel (Subgroup.zpowers γ)
      (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) → (K : Subgroup G) :=
    fun q => q.out.out.out
  have hqτ : ∀ q, q.out = (((τ q : (K : Subgroup G)) : (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) :
      _ ⧸ H) := fun q => by
    simp only [τ, QuotientGroup.out_eq']
  have hper : ∀ q (k : ℤ), ((τ q : G))⁻¹ * s.elt ^ k * τ q ∈ (K' : Subgroup G) ↔
      (Function.minimalPeriod (γ • ·) q.out : ℤ) ∣ k := fun q k => by
    rw [← zpow_smul_eq_iff_minimalPeriod_dvd, hqτ q, hγ, zpow_smul_mk_mk_eq_iff hLK' hK'K]
  have hpos : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), 0 < Function.minimalPeriod (γ • ·) q.out := fun q =>
    Nat.pos_of_dvd_of_pos (pow_smul_eq_iff_minimalPeriod_dvd.1 (by rw [pow_orderOf_eq_one, one_smul]))
      (orderOf_pos γ)
  have hmemf : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((τ q : G))⁻¹ * s.elt ^ Function.minimalPeriod (γ • ·) q.out * τ q ∈
      (K' : Subgroup G) := fun q => by
    have := (hper q (Function.minimalPeriod (γ • ·) q.out)).2 dvd_rfl
    rwa [zpow_natCast] at this
  have hfac : ∀ q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)), ((Abelianization.lift (D.reciprocity hLK' hax)).comp
      ((Abelianization.of).comp
        (MonoidHom.ofInjective (galRestrict_injective (L := L) hK'K)).symm.toMonoidHom))
        ⟨(q.out.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * q.out.out,
          QuotientGroup.out_conj_pow_minimalPeriod_mem H γ q.out⟩ =
      (QuotientGroup.mk (norm A (K' : Subgroup G)
        ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G)
        ⟨((τ q : G))⁻¹ • (π : A), fixedModule_anti (inf_le_right (a := K'))
          (smul_mem_fixedModule π.2 _)⟩) : tateZero A (K' : Subgroup G) (L : Subgroup G)) := by
    intro q
    refine Eq.trans ?_ (reciprocity_mk_conj_pow hax hLK' hK'K s (τ q) (hpos q) (hper q) (hmemf q) hπ)
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, Abelianization.lift_apply_of]
    congr 1
    rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_eq]
    apply Subtype.ext
    rw [MonoidHom.ofInjective_apply, galRestrict_mk]
    show (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out = _
    have hL : (Quotient.out q.out)⁻¹ * γ ^ Function.minimalPeriod (γ • ·) q.out * Quotient.out q.out =
        ((((τ q)⁻¹ * ⟨s.elt, s.mem⟩ ^ Function.minimalPeriod (γ • ·) q.out * τ q : (K : Subgroup G))) :
          (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_pow]
      simp only [τ, QuotientGroup.out_eq']
      rfl
    rw [hL]
    congr 1
  rw [Finset.prod_congr rfl fun q _ => hfac q, ← QuotientGroup.mk_prod]
  congr 1
  apply Subtype.ext
  rw [SubmonoidClass.coe_finsetProd]
  refine (coe_norm_eq_prod_norm_inf hK'K (fun q => (τ q : G)) (fun q => (τ q).2)
    (fun q => ((K' ⊓ conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) : Subgroup G))
    ?_ ?_ ?_ π (fun q => fixedModule_anti (inf_le_right (a := K'))
      (smul_mem_fixedModule π.2 _))).symm
  · intro q k hk
    show k ∈ (K' : Subgroup G) ⊓ ((conjOpen ((τ q : G))⁻¹ (s.field L hLK) : OpenSubgroup G) :
      Subgroup G) ↔ _
    rw [Subgroup.mem_inf, mem_conjOpen, inv_inv]
    exact ⟨fun h => h.2, fun h => ⟨hk, h⟩⟩
  · intro c hc
    let p : ((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H :=
      (((⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) :
        (K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) : _ ⧸ H)
    let q : Quotient (orbitRel (Subgroup.zpowers γ) (((K : Subgroup G) ⧸ (L : Subgroup G).subgroupOf K) ⧸ H)) := Quotient.mk'' p
    obtain ⟨⟨z, hz⟩, hzp⟩ := orbitRel_apply.1 (Quotient.mk_out' p : orbitRel _ _ q.out p)
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    have hzp' : γ ^ m • p = q.out := hzp
    rw [hqτ q, hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K] at hzp'
    refine ⟨q, _, hzp', ?_⟩
    have e : (τ q : G) * ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m *
        ⟨c⁻¹, (K : Subgroup G).inv_mem hc⟩ : (K : Subgroup G)) : G)⁻¹ * τ q)⁻¹ * c = s.elt ^ m := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      group
    rw [e]
    exact Subgroup.zpow_mem _ (s.elt_mem_field hLK) m
  · intro q q' k hk k' hk' hy
    obtain ⟨m, l, hl, hyeq⟩ := exists_eq_zpow_mul_of_mem_frobeniusClosure L.isOpen
      (FrobeniusLift.mem_normalizer (D := D) hLK s.mem) hy
    rw [← Quotient.out_eq q, ← Quotient.out_eq q']
    apply Quotient.sound
    refine (orbitRel_apply (G := Subgroup.zpowers γ)).2 ⟨⟨γ ^ m, Subgroup.zpow_mem_zpowers γ m⟩, ?_⟩
    show γ ^ m • q'.out = q.out
    rw [hqτ q, hqτ q', hγ, ← QuotientGroup.mk_zpow, MulAction.Quotient.smul_mk, smul_eq_mul,
      ← QuotientGroup.mk_mul, mk_mk_eq_iff hLK' hK'K]
    have hl1 : s.elt ^ m * l * (s.elt ^ m)⁻¹ ∈ (L : Subgroup G) :=
      conj_mem_of_normal ((K : Subgroup G).zpow_mem s.mem m) (hLK hl) hl
    have hl2 := conj_mem_of_normal ((K : Subgroup G).inv_mem (τ q).2) (hLK hl1) hl1
    have hτ' : (τ q' : G) = (s.elt ^ m * l)⁻¹ * ((τ q : G) * k⁻¹ * k') := by
      rw [← hyeq]
      group
    have e : ((((⟨s.elt, s.mem⟩ : (K : Subgroup G)) ^ m * τ q' : (K : Subgroup G)) : G))⁻¹ * τ q =
        k'⁻¹ * k * (((τ q : G))⁻¹ * (s.elt ^ m * l * (s.elt ^ m)⁻¹) * ((τ q : G))⁻¹⁻¹) := by
      simp only [Subgroup.coe_mul, SubgroupClass.coe_zpow]
      rw [hτ']
      group
    rw [e]
    exact (K' : Subgroup G).mul_mem
      ((K' : Subgroup G).mul_mem ((K' : Subgroup G).inv_mem hk') hk) (hLK' hl2)

end Ver

end ClassFieldData

end GroundTheory.LocalField.Abstract
end
