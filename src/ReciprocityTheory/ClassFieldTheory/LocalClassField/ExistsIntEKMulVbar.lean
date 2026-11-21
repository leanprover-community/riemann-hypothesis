import Mathlib
import ReciprocityTheory.NeutralLocalFields.Duality
import ReciprocityTheory.GroupCohomology.InfRes
import ReciprocityTheory.GroupCohomology.CardLenStatement
import ReciprocityTheory.ClassFieldTheory.LocalClassField.KbarRepContAction
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnrDefs
import ReciprocityTheory.ClassFieldTheory.LocalClassField.QZDefs

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

variable {M : Type*} [AddCommGroup M]

abbrev T (D N : M →+ M) : Type _ := D.ker ⧸ (N.range.addSubgroupOf D.ker)

def IsFin (D N : M →+ M) : Prop := Finite (T D N) ∧ Finite (T N D)

noncomputable def q (D N : M →+ M) : ℚ := (Nat.card (T D N) : ℚ) / (Nat.card (T N D) : ℚ)

structure SES {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    (DA NA : A →+ A) (DB NB : B →+ B) (DC NC : C →+ C) (f : A →+ B) (g : B →+ C) : Prop where
  inj : Injective f
  exact : Function.Exact f g
  surj : Surjective g
  fD : ∀ a, f (DA a) = DB (f a)
  fN : ∀ a, f (NA a) = NB (f a)
  gD : ∀ b, g (DB b) = DC (g b)
  gN : ∀ b, g (NB b) = NC (g b)
  DN : ∀ b, DB (NB b) = 0
  ND : ∀ b, NB (DB b) = 0

theorem mk_eq_zero_iff {D N : M →+ M} (x : D.ker) :
    (QuotientAddGroup.mk x : T D N) = 0 ↔ (x : M) ∈ N.range := by
  rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]

theorem mk_eq_mk_iff {D N : M →+ M} (x y : D.ker) :
    (QuotientAddGroup.mk x : T D N) = QuotientAddGroup.mk y ↔ (x : M) - y ∈ N.range := by
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, mk_eq_zero_iff]; rfl

variable {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    {DA NA : A →+ A} {DB NB : B →+ B} {DC NC : C →+ C} {f : A →+ B} {g : B →+ C}

def kerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : DA.ker →+ DB.ker :=
  (f.comp DA.ker.subtype).codRestrict DB.ker (fun a => by
    have ha : DA (a : A) = 0 := a.2
    rw [AddMonoidHom.mem_ker]
    change DB (f a) = 0
    rw [← fD, ha, map_zero])

@[simp] theorem kerMap_coe (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (a : DA.ker) :
    ((kerMap f fD a : DB.ker) : B) = f a := rfl

def Tmap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a)) :
    T DA NA →+ T DB NB :=
  QuotientAddGroup.map _ _ (kerMap f fD) (by
    intro a ha
    rw [AddSubgroup.mem_addSubgroupOf] at ha
    obtain ⟨x, hx⟩ := ha
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    exact ⟨f x, by rw [← fN, hx]; rfl⟩)

@[simp] theorem Tmap_mk (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (a : DA.ker) : Tmap f fD fN (QuotientAddGroup.mk a) = QuotientAddGroup.mk (kerMap f fD a) := rfl

theorem SES.swap (h : SES DA NA DB NB DC NC f g) : SES NA DA NB DB NC DC f g :=
  ⟨h.inj, h.exact, h.surj, h.fN, h.fD, h.gN, h.gD, h.ND, h.DN⟩

theorem SES.DN_C (h : SES DA NA DB NB DC NC f g) (c : C) : DC (NC c) = 0 := by
  obtain ⟨b, rfl⟩ := h.surj c
  rw [← h.gN, ← h.gD, h.DN, map_zero]

theorem ker_Tmap_g (h : SES DA NA DB NB DC NC f g) :
    (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range := by
  ext x
  obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective x
  rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨b', rfl⟩ := h.surj c
    have h1 : g ((b : B) - NB b') = 0 := by rw [map_sub, h.gN, hc, sub_self]
    obtain ⟨a, ha⟩ := (h.exact _).1 h1
    have hb : DB (b : B) = 0 := b.2
    have haD : DA a = 0 := h.inj (by rw [h.fD, ha, map_sub, hb, h.DN, sub_zero, map_zero])
    refine ⟨QuotientAddGroup.mk ⟨a, haD⟩, ?_⟩
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe]
    exact ⟨-b', by rw [map_neg]; change _ = f a - b; rw [ha]; abel⟩
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [Tmap_mk, mk_eq_mk_iff, kerMap_coe] at hy
    obtain ⟨b', hb'⟩ := hy
    refine ⟨- g b', ?_⟩
    have h0 : g (f a) = 0 := (h.exact _).2 ⟨a, rfl⟩
    have := congrArg g hb'
    rw [map_sub, h0, h.gN, zero_sub] at this
    rw [map_neg, this, neg_neg]

def Rel (DB : B →+ B) (f : A →+ B) (g : B →+ C) (c : C) (a : A) : Prop := ∃ b, g b = c ∧ f a = DB b

theorem exists_rel (h : SES DA NA DB NB DC NC f g) (c : DC.ker) : ∃ a : NA.ker, Rel DB f g c a := by
  obtain ⟨b, hb⟩ := h.surj c
  have hc : DC (c : C) = 0 := c.2
  have h1 : g (DB b) = 0 := by rw [h.gD, hb, hc]
  obtain ⟨a, ha⟩ := (h.exact _).1 h1
  exact ⟨⟨a, h.inj (by rw [h.fN, ha, h.ND, map_zero])⟩, b, hb, ha⟩

theorem rel_unique (h : SES DA NA DB NB DC NC f g) {c : C} {a a' : NA.ker} (h1 : Rel DB f g c a)
    (h2 : Rel DB f g c a') : (QuotientAddGroup.mk a : T NA DA) = QuotientAddGroup.mk a' := by
  obtain ⟨b, hb, ha⟩ := h1
  obtain ⟨b', hb', ha'⟩ := h2
  rw [mk_eq_mk_iff]
  obtain ⟨x, hx⟩ := (h.exact (b - b')).1 (by rw [map_sub, hb, hb', sub_self])
  exact ⟨x, h.inj (by rw [h.fD, hx, map_sub, map_sub, ha, ha'])⟩

theorem exists_delta (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a →
      δ (QuotientAddGroup.mk c) = QuotientAddGroup.mk a := by
  classical
  let δ0 : DC.ker →+ T NA DA := AddMonoidHom.mk'
    (fun c => QuotientAddGroup.mk (Classical.choose (exists_rel h c))) (fun c c' => by
      rw [← QuotientAddGroup.mk_add]
      refine rel_unique h (Classical.choose_spec (exists_rel h (c + c'))) ?_
      obtain ⟨b, hb, ha⟩ := Classical.choose_spec (exists_rel h c)
      obtain ⟨b', hb', ha'⟩ := Classical.choose_spec (exists_rel h c')
      exact ⟨b + b', by rw [map_add, hb, hb']; rfl, by
        rw [map_add, ← ha, ← ha', ← map_add]; rfl⟩)
  have hδ0 : ∀ (c : DC.ker) (a : NA.ker), Rel DB f g c a → δ0 c = QuotientAddGroup.mk a :=
    fun c a hca => rel_unique h (Classical.choose_spec (exists_rel h c)) hca
  refine ⟨QuotientAddGroup.lift _ δ0 ?_, fun c a hca => ?_⟩
  · intro c hc
    rw [AddSubgroup.mem_addSubgroupOf] at hc
    obtain ⟨c0, hc0⟩ := hc
    obtain ⟨b0, rfl⟩ := h.surj c0
    rw [AddMonoidHom.mem_ker, hδ0 c 0 ⟨NB b0, by rw [h.gN, hc0], by rw [h.DN]; exact map_zero f⟩]
    rfl
  · rw [QuotientAddGroup.lift_mk]
    exact hδ0 c a hca

theorem half_hexagon (h : SES DA NA DB NB DC NC f g) :
    ∃ δ : T DC NC →+ T NA DA, (Tmap g h.gD h.gN).ker = (Tmap f h.fD h.fN).range ∧
      δ.ker = (Tmap g h.gD h.gN).range ∧ (Tmap f h.fN h.fD).ker = δ.range := by
  obtain ⟨δ, hδ⟩ := exists_delta h
  refine ⟨δ, ker_Tmap_g h, ?_, ?_⟩
  · ext x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
    constructor
    · intro hx
      obtain ⟨a, b, hb, ha⟩ := exists_rel h c
      rw [AddMonoidHom.mem_ker, hδ c a ⟨b, hb, ha⟩, mk_eq_zero_iff] at hx
      obtain ⟨a', ha'⟩ := hx
      have hk : DB (b - f a') = 0 := by rw [map_sub, ← h.fD, ha', ha, sub_self]
      refine ⟨QuotientAddGroup.mk ⟨b - f a', hk⟩, ?_⟩
      rw [Tmap_mk]
      congr 1
      apply Subtype.ext
      rw [kerMap_coe]
      change g (b - f a') = c
      rw [map_sub, (h.exact _).2 ⟨a', rfl⟩, sub_zero, hb]
    · rintro ⟨y, hy⟩
      obtain ⟨b, rfl⟩ := QuotientAddGroup.mk_surjective y
      rw [Tmap_mk] at hy
      have hb : DB (b : B) = 0 := b.2
      rw [AddMonoidHom.mem_ker, ← hy, hδ _ 0 ⟨b, rfl, by rw [hb]; exact map_zero f⟩]
      rfl
  · ext y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [AddMonoidHom.mem_ker, Tmap_mk, mk_eq_zero_iff, kerMap_coe]
    constructor
    · rintro ⟨b, hb⟩
      have hc : DC (g b) = 0 := by rw [← h.gD, hb]; exact (h.exact _).2 ⟨a, rfl⟩
      exact ⟨QuotientAddGroup.mk ⟨g b, hc⟩, hδ _ a ⟨b, rfl, hb.symm⟩⟩
    · rintro ⟨x, hx⟩
      obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective x
      obtain ⟨a', b, hb, ha'⟩ := exists_rel h c
      rw [hδ c a' ⟨b, hb, ha'⟩, mk_eq_mk_iff] at hx
      obtain ⟨a'', ha''⟩ := hx
      refine ⟨b - f a'', ?_⟩
      rw [map_sub, ← h.fD, ha'', map_sub, ha']
      abel

section Count

variable {X Y Z : Type*} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup Z]

theorem card_eq_ker_mul_range (φ : X →+ Y) :
    Nat.card X = Nat.card φ.ker * Nat.card φ.range := by
  rw [← AddSubgroup.index_ker, AddSubgroup.card_mul_index]

theorem finite_of_exact (φ : X →+ Y) (ψ : Y →+ Z) (hex : ψ.ker = φ.range) [Finite X] [Finite Z] :
    Finite Y := by
  apply Nat.finite_of_card_ne_zero
  rw [card_eq_ker_mul_range ψ, hex]
  have : Finite φ.range := Set.finite_range φ
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

theorem card_six {X₁ X₂ X₃ X₄ X₅ X₆ : Type*} [AddCommGroup X₁] [AddCommGroup X₂] [AddCommGroup X₃]
    [AddCommGroup X₄] [AddCommGroup X₅] [AddCommGroup X₆] (f₁ : X₁ →+ X₂) (f₂ : X₂ →+ X₃)
    (f₃ : X₃ →+ X₄) (f₄ : X₄ →+ X₅) (f₅ : X₅ →+ X₆) (f₆ : X₆ →+ X₁) (h₁ : f₂.ker = f₁.range)
    (h₂ : f₃.ker = f₂.range) (h₃ : f₄.ker = f₃.range) (h₄ : f₅.ker = f₄.range)
    (h₅ : f₆.ker = f₅.range) (h₆ : f₁.ker = f₆.range) :
    Nat.card X₁ * Nat.card X₃ * Nat.card X₅ = Nat.card X₂ * Nat.card X₄ * Nat.card X₆ := by
  rw [card_eq_ker_mul_range f₁, card_eq_ker_mul_range f₂, card_eq_ker_mul_range f₃,
    card_eq_ker_mul_range f₄, card_eq_ker_mul_range f₅, card_eq_ker_mul_range f₆, h₁, h₂, h₃, h₄, h₅, h₆]
  ring

end Count

theorem card_hexagon (h : SES DA NA DB NB DC NC f g) :
    Nat.card (T DA NA) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  exact card_six _ _ _ _ _ _ h1 h2 h3 h4 h5 h6

theorem isFin_mid (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    IsFin DB NB := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h1, finite_of_exact _ _ h4⟩

theorem isFin_left (h : SES DA NA DB NB DC NC f g) (hB : IsFin DB NB) (hC : IsFin DC NC) :
    IsFin DA NA := by
  obtain ⟨δ, h1, h2, h3⟩ := half_hexagon h
  obtain ⟨δ', h4, h5, h6⟩ := half_hexagon h.swap
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  exact ⟨finite_of_exact _ _ h6, finite_of_exact _ _ h3⟩

theorem q_mul (h : SES DA NA DB NB DC NC f g) (hA : IsFin DA NA) (hC : IsFin DC NC) :
    q DB NB = q DA NA * q DC NC := by
  have hB := isFin_mid h hA hC
  have key := card_hexagon h
  obtain ⟨_, _⟩ := hA
  obtain ⟨_, _⟩ := hB
  obtain ⟨_, _⟩ := hC
  have e1 : (Nat.card (T NA DA) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e2 : (Nat.card (T NB DB) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have e3 : (Nat.card (T NC DC) : ℚ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have key' : (Nat.card (T DA NA) : ℚ) * Nat.card (T DC NC) * Nat.card (T NB DB) =
      Nat.card (T DB NB) * Nat.card (T NA DA) * Nat.card (T NC DC) := by exact_mod_cast key
  unfold q
  field_simp
  linarith [key']

theorem isFin_of_finite [Finite M] (D N : M →+ M) : IsFin D N := ⟨inferInstance, inferInstance⟩

theorem q_of_finite [Finite M] (D N : M →+ M) (hDN : ∀ x, D (N x) = 0) (hND : ∀ x, N (D x) = 0) :
    q D N = 1 := by
  have h1 : Nat.card D.ker = Nat.card (T D N) * Nat.card N.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (N.range.addSubgroupOf D.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hDN x)).toEquiv
  have h2 : Nat.card N.ker = Nat.card (T N D) * Nat.card D.range := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (D.range.addSubgroupOf N.ker)]
    congr 1
    exact Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (by
      rintro _ ⟨x, rfl⟩; exact hND x)).toEquiv
  have h3 := card_eq_ker_mul_range D
  have h4 := card_eq_ker_mul_range N
  rw [h1] at h3
  rw [h2] at h4
  have h5 : Nat.card (T D N) * (Nat.card N.range * Nat.card D.range) =
      Nat.card (T N D) * (Nat.card N.range * Nat.card D.range) := by
    calc _ = Nat.card M := by rw [h3]; ring
      _ = _ := by rw [h4]; ring
  have h6 : Nat.card (T D N) = Nat.card (T N D) :=
    Nat.eq_of_mul_eq_mul_right (Nat.mul_pos Nat.card_pos Nat.card_pos) h5
  unfold q
  rw [h6]
  exact div_self (Nat.cast_ne_zero.2 Nat.card_pos.ne')

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function

section Abstract

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    {DA NA : A →+ A} {DB NB : B →+ B} {f : A →+ B}

def cokerMap (f : A →+ B) (fD : ∀ a, f (DA a) = DB (f a)) : B ⧸ f.range →+ B ⧸ f.range :=
  QuotientAddGroup.map _ _ DB (by
    rintro _ ⟨a, rfl⟩
    exact ⟨DA a, fD a⟩)

theorem ses_coker (hf : Injective f)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) :
    SES DA NA DB NB (cokerMap f fD) (cokerMap f fN) f (QuotientAddGroup.mk' f.range) where
  inj := hf
  exact := fun b => by
    rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  surj := QuotientAddGroup.mk'_surjective _
  fD := fD
  fN := fN
  gD := fun _ => rfl
  gN := fun _ => rfl
  DN := DN
  ND := ND

theorem isFin_iff_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) : IsFin DA NA ↔ IsFin DB NB :=
  ⟨fun hA => isFin_mid (ses_coker hf fD fN DN ND) hA (isFin_of_finite _ _),
    fun hB => isFin_left (ses_coker hf fD fN DN ND) hB (isFin_of_finite _ _)⟩

theorem q_eq_of_finiteIndex (hf : Injective f) (hfi : f.range.FiniteIndex)
    (fD : ∀ a, f (DA a) = DB (f a)) (fN : ∀ a, f (NA a) = NB (f a))
    (DN : ∀ b, DB (NB b) = 0) (ND : ∀ b, NB (DB b) = 0) (hA : IsFin DA NA) :
    q DA NA = q DB NB := by
  have h := ses_coker hf fD fN DN ND
  rw [q_mul h hA (isFin_of_finite _ _), q_of_finite _ _ h.DN_C h.swap.DN_C, mul_one]

end Abstract

section Cyclic

variable {k G M : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup M] [Module k M]

def dHom (ρ : Representation k G M) (g : G) : M →+ M := (ρ g - 1 : Module.End k M).toAddMonoidHom

def nHom (ρ : Representation k G M) : M →+ M := (ρ.norm : Module.End k M).toAddMonoidHom

@[simp] theorem dHom_apply (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g x = ρ g x - x := rfl

theorem nHom_apply (ρ : Representation k G M) (x : M) : nHom ρ x = ∑ c : G, ρ c x := by
  change ρ.norm x = _
  simp [Representation.norm]

theorem dHom_nHom (ρ : Representation k G M) (g : G) (x : M) : dHom ρ g (nHom ρ x) = 0 := by
  change ρ g (ρ.norm x) - ρ.norm x = 0
  rw [Representation.self_norm_apply, sub_self]

theorem nHom_dHom (ρ : Representation k G M) (g : G) (x : M) : nHom ρ (dHom ρ g x) = 0 := by
  change ρ.norm (ρ g x - x) = 0
  rw [map_sub, Representation.norm_self_apply, sub_self]

theorem mem_ker_dHom_iff (ρ : Representation k G M) (g : G) (hg : ∀ x, x ∈ Subgroup.zpowers g) (x : M) :
    x ∈ (dHom ρ g).ker ↔ ∀ c : G, ρ c x = x := by
  rw [AddMonoidHom.mem_ker, dHom_apply, sub_eq_zero,
    ← Representation.mem_invariants_iff_of_forall_mem_zpowers ρ g hg x]
  rfl

abbrev TateZerothCohomology (ρ : Representation k G M) (g : G) : Type _ := T (dHom ρ g) (nHom ρ)

abbrev H1 (ρ : Representation k G M) (g : G) : Type _ := T (nHom ρ) (dHom ρ g)

def HFin (ρ : Representation k G M) (g : G) : Prop := IsFin (dHom ρ g) (nHom ρ)

noncomputable def h (ρ : Representation k G M) (g : G) : ℚ := q (dHom ρ g) (nHom ρ)

theorem h_eq (ρ : Representation k G M) (g : G) :
    h ρ g = (Nat.card (TateZerothCohomology ρ g) : ℚ) / (Nat.card (H1 ρ g) : ℚ) := rfl

variable {A B C : Type*} [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
  [AddCommGroup C] [Module k C]

theorem map_dHom (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (dHom ρA g a) = dHom ρB g (i a) := by
  rw [dHom_apply, dHom_apply, map_sub, hiG]

theorem map_nHom (ρA : Representation k G A) (ρB : Representation k G B) (i : A →+ B)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (a : A) : i (nHom ρA a) = nHom ρB (i a) := by
  rw [nHom_apply, nHom_apply, map_sum]
  exact Finset.sum_congr rfl fun c _ => hiG c a

theorem ses_of_rep (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b)) :
    SES (dHom ρA g) (nHom ρA) (dHom ρB g) (nHom ρB) (dHom ρC g) (nHom ρC) i p :=
  ⟨hi, hip, hp, map_dHom ρA ρB g i hiG, map_nHom ρA ρB i hiG, map_dHom ρB ρC g p hpG,
    map_nHom ρB ρC p hpG, dHom_nHom ρB g, nHom_dHom ρB g⟩

theorem h_mul (ρA : Representation k G A) (ρB : Representation k G B) (ρC : Representation k G C)
    (g : G) (i : A →+ B) (p : B →+ C) (hi : Injective i) (hip : Function.Exact i p) (hp : Surjective p)
    (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) (hpG : ∀ c b, p (ρB c b) = ρC c (p b))
    (hA : HFin ρA g) (hC : HFin ρC g) : HFin ρB g ∧ h ρB g = h ρA g * h ρC g :=
  have hs := ses_of_rep ρA ρB ρC g i p hi hip hp hiG hpG
  ⟨isFin_mid hs hA hC, q_mul hs hA hC⟩

theorem h_eq_of_finiteIndex (ρA : Representation k G A) (ρB : Representation k G B) (g : G) (i : A →+ B)
    (hi : Injective i) (hfi : i.range.FiniteIndex) (hiG : ∀ c a, i (ρA c a) = ρB c (i a)) :
    (HFin ρA g ↔ HFin ρB g) ∧ (HFin ρA g → h ρA g = h ρB g) :=
  ⟨isFin_iff_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g),
    q_eq_of_finiteIndex hi hfi (map_dHom ρA ρB g i hiG) (map_nHom ρA ρB i hiG) (dHom_nHom ρB g)
      (nHom_dHom ρB g)⟩

theorem h_of_subsingleton (ρ : Representation k G M) (g : G) [Subsingleton (TateZerothCohomology ρ g)]
    [Subsingleton (H1 ρ g)] : HFin ρ g ∧ h ρ g = 1 := by
  refine ⟨⟨inferInstance, inferInstance⟩, ?_⟩
  rw [h_eq, Nat.card_of_subsingleton (0 : TateZerothCohomology ρ g), Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_eq_card_H0hat (ρ : Representation k G M) (g : G) [Subsingleton (H1 ρ g)] :
    h ρ g = Nat.card (TateZerothCohomology ρ g) := by
  rw [h_eq, Nat.card_of_subsingleton (0 : H1 ρ g)]
  norm_num

theorem h_int (ρ : Representation ℤ G ℤ) (hρ : ∀ c x, ρ c x = x) (g : G) :
    HFin ρ g ∧ Nat.card (TateZerothCohomology ρ g) = Nat.card G ∧ Subsingleton (H1 ρ g) ∧ h ρ g = Nat.card G := by
  have hpos : 0 < Nat.card G := Nat.card_pos
  have hD : (dHom ρ g).ker = ⊤ := by
    ext x; simp [AddMonoidHom.mem_ker, hρ]
  have hNx : ∀ x, nHom ρ x = (Nat.card G : ℤ) * x := fun x => by
    rw [nHom_apply]; simp [hρ]
  have hN : (nHom ρ).range = AddSubgroup.zmultiples (Nat.card G : ℤ) := by
    ext x
    rw [Int.mem_zmultiples_iff]
    constructor
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
    · rintro ⟨y, rfl⟩; exact ⟨y, hNx y⟩
  have h0 : Nat.card (TateZerothCohomology ρ g) = Nat.card G := by
    change ((nHom ρ).range.addSubgroupOf (dHom ρ g).ker).index = _
    change (nHom ρ).range.relIndex (dHom ρ g).ker = _
    rw [hD, AddSubgroup.relIndex_top_right, hN, Int.index_zmultiples]
    simp
  have h1 : Subsingleton (H1 ρ g) := by
    have : Subsingleton (nHom ρ).ker := ⟨fun x y => by
      have hx : nHom ρ x = 0 := x.2
      have hy : nHom ρ y = 0 := y.2
      rw [hNx] at hx hy
      apply Subtype.ext
      have hne : (Nat.card G : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
      rw [(mul_eq_zero.1 hx).resolve_left hne, (mul_eq_zero.1 hy).resolve_left hne]⟩
    exact (QuotientAddGroup.mk_surjective).subsingleton
  refine ⟨⟨Nat.finite_of_card_ne_zero (by rw [h0]; exact hpos.ne'), inferInstance⟩, h0, h1, ?_⟩
  rw [h_eq_card_H0hat, h0]

end Cyclic

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand

open Function CategoryTheory

universe u

variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G] {M : Type u} [AddCommGroup M] [Module k M]

theorem nonempty_of_surjective {X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (H : AddSubgroup X)
    (φ : X →+ Y) (hφ : Surjective φ) (hk : ∀ x, φ x = 0 ↔ x ∈ H) : Nonempty (Y ≃+ X ⧸ H) := by
  have : φ.ker = H := by ext x; rw [AddMonoidHom.mem_ker, hk]
  subst this
  exact ⟨(QuotientAddGroup.quotientKerEquivOfSurjective φ hφ).symm⟩

theorem nonempty_groupCohomology_even (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi0 : i ≠ 0) (hi : Even i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ TateZerothCohomology ρ g) := by
  have : NeZero i := ⟨hi0⟩
  let π := Rep.FiniteCyclicGroup.groupCohomologyπEven (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπEven]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπEven_eq_zero_iff (Rep.of ρ) g hg i hi x

theorem nonempty_groupCohomology_odd (ρ : Representation k G M) (g : G)
    (hg : ∀ x, x ∈ Subgroup.zpowers g) (i : ℕ) (hi : Odd i) :
    Nonempty (groupCohomology (Rep.of ρ) i ≃+ H1 ρ g) := by
  let π := Rep.FiniteCyclicGroup.groupCohomologyπOdd (Rep.of ρ) g hg i hi
  have hπ : Surjective π.hom := by
    rw [← ModuleCat.epi_iff_surjective]
    dsimp only [π, Rep.FiniteCyclicGroup.groupCohomologyπOdd]
    exact epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)) (epi_comp' inferInstance inferInstance)
  refine nonempty_of_surjective _ (π.hom.toAddMonoidHom) hπ ?_
  intro x
  exact Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff (Rep.of ρ) g hg i hi x

end ReciprocityTheory.DiscreteGroups.LocalClassField.Herbrand
end

section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField

open _root_.Neutral.B1 ReciprocityTheory.Coh

noncomputable section

variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))

def fK : ℕ := Nat.log p (qK p K)

def vbar : KbarMult p →+ ℝ where
  toFun x := - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖
  map_zero' := by
    show - Real.logb p ‖((1 : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = 0
    simp
  map_add' x y := by
    show - Real.logb p ‖((Additive.toMul x * Additive.toMul y : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = _
    rw [Units.val_mul, norm_mul, Real.logb_mul (norm_ne_zero_iff.2 (Units.ne_zero _))
      (norm_ne_zero_iff.2 (Units.ne_zero _))]
    ring

theorem vbar_apply (x : KbarMult p) :
    vbar p x = - Real.logb p ‖((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ := rfl

def multOf : AddSubgroup (KbarMult p) where
  carrier := {x | ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K}
  zero_mem' := K.one_mem
  add_mem' := fun {x y} hx hy => K.mul_mem hx hy
  neg_mem' := fun {x} hx => by
    show (((Additive.toMul x : (PadicAlgCl p)ˣ)⁻¹ : (PadicAlgCl p)ˣ) : PadicAlgCl p) ∈ K
    rw [Units.val_inv_eq_inv_val]
    exact K.inv_mem hx

def ofK : Additive Kˣ →+ KbarMult p :=
  MonoidHom.toAdditive (Units.map (algebraMap K (PadicAlgCl p) : K →* PadicAlgCl p))

theorem ofK_mem (x : Additive Kˣ) : ofK p K x ∈ multOf p K := (Additive.toMul x : Kˣ).1.2

def valueGroup : AddSubgroup ℝ := (multOf p K).map (vbar p)

def eK : ℕ := (AddSubgroup.zmultiples (1 : ℝ)).relIndex (valueGroup p K)

theorem exists_int_eK_mul_vbar (x : KbarMult p) (hx : x ∈ multOf p K) :
    ∃ n : ℤ, (n : ℝ) = eK p K * vbar p x := by
  have h : eK p K • vbar p x ∈ AddSubgroup.zmultiples (1 : ℝ) :=
    AddSubgroup.nsmul_relIndex_mem _ (AddSubgroup.mem_map_of_mem _ hx)
  obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.1 h
  refine ⟨k, ?_⟩
  have hk' : (k : ℝ) = (eK p K) • vbar p x := by simpa using hk
  rw [hk', nsmul_eq_mul]

def vOnFun (x : multOf p K) : ℤ := (exists_int_eK_mul_vbar p K x.1 x.2).choose

theorem vOnFun_spec (x : multOf p K) : (vOnFun p K x : ℝ) = eK p K * vbar p x.1 :=
  (exists_int_eK_mul_vbar p K x.1 x.2).choose_spec

def vOn : multOf p K →+ ℤ where
  toFun := vOnFun p K
  map_zero' := by
    apply Int.cast_injective (α := ℝ)
    rw [vOnFun_spec]; simp
  map_add' x y := by
    apply Int.cast_injective (α := ℝ)
    rw [Int.cast_add, vOnFun_spec, vOnFun_spec, vOnFun_spec, AddSubgroup.coe_add, map_add, mul_add]

theorem vOn_spec (x : multOf p K) : (vOn p K x : ℝ) = eK p K * vbar p x.1 := vOnFun_spec p K x

def vK (x : Kˣ) : ℤ := vOn p K ⟨ofK p K (Additive.ofMul x), ofK_mem p K _⟩

def Ubar : Submodule ℤ (KbarMult p) := AddSubgroup.toIntSubmodule (vbar p).ker

theorem mem_Ubar_iff (x : KbarMult p) : x ∈ Ubar p ↔ vbar p x = 0 := Iff.rfl

def UK : Subgroup Kˣ where
  carrier := {x | ‖((x : K) : PadicAlgCl p)‖ = 1}
  one_mem' := by
    show ‖(((1 : Kˣ) : K) : PadicAlgCl p)‖ = 1
    simp
  mul_mem' := fun {x y} hx hy => by
    have hx' : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx
    have hy' : ‖((y : K) : PadicAlgCl p)‖ = 1 := hy
    show ‖(((x * y : Kˣ) : K) : PadicAlgCl p)‖ = 1
    rw [Units.val_mul, MulMemClass.coe_mul, norm_mul, hx', hy', one_mul]
  inv_mem' := fun {x} hx => by
    have hx' : ‖((x : K) : PadicAlgCl p)‖ = 1 := hx
    show ‖(((x⁻¹ : Kˣ) : K) : PadicAlgCl p)‖ = 1
    rw [Units.val_inv_eq_inv_val, IntermediateField.coe_inv, norm_inv, hx', inv_one]

def subG : Subgroup (GK p K) where
  carrier := {σ | ∀ x ∈ L, σ x = x}
  one_mem' := fun _ _ => rfl
  mul_mem' := fun {σ τ} hσ hτ x hx => by
    show σ (τ x) = x
    rw [hτ x hx, hσ x hx]
  inv_mem' := fun {σ} hσ x hx => by
    rw [AlgEquiv.aut_inv, AlgEquiv.symm_apply_eq]; exact (hσ x hx).symm

theorem mem_subG_iff (σ : GK p K) : σ ∈ subG p K L ↔ ∀ x ∈ L, σ x = x := Iff.rfl

def degLK : ℕ := (subG p K L).index

abbrev GalLK : Type := GK p K ⧸ subG p K L

variable {p K L} in

def resGK (h : K ≤ L) : GK p L →* GK p K where
  toFun σ := { σ.toRingEquiv with commutes' := fun x => σ.commutes ⟨x.1, h x.2⟩ }
  map_one' := rfl
  map_mul' _ _ := rfl

variable {p K L} in
theorem resGK_apply (h : K ≤ L) (σ : GK p L) (x : PadicAlgCl p) : resGK h σ x = σ x := rfl

variable {p K L} in
theorem resGK_continuous (h : K ≤ L) : Continuous (resGK h) := by
  have hint : Algebra.IsIntegral L (PadicAlgCl p) := Algebra.IsIntegral.tower_top (R := ℚ_[p])
  apply continuous_of_continuousAt_one
  rw [ContinuousAt, map_one]
  refine Filter.tendsto_def.2 fun s hs => ?_
  rw [krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨E, hE, hEs⟩ := hs
  let b := Module.finBasis K E
  have hopen : IsOpen (⋂ i, {σ : GK p L | σ (b i : PadicAlgCl p) = b i}) :=
    isOpen_iInter_of_finite fun i => stabilizer_isOpen_of_isIntegral (K := L) (b i : PadicAlgCl p)
  refine Filter.mem_of_superset (hopen.mem_nhds (Set.mem_iInter.2 fun i => rfl)) fun σ hσ => hEs ?_
  rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hx' : x = ∑ i, b.repr ⟨x, hx⟩ i • (b i : PadicAlgCl p) := by
    have := congrArg E.val (b.sum_repr ⟨x, hx⟩)
    rw [map_sum] at this
    exact this.symm
  rw [hx']
  show resGK h σ _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Algebra.smul_def, map_mul, AlgEquiv.commutes]
  exact congrArg _ (Set.mem_iInter.1 hσ i)

variable {p K L} in

theorem subG_normal_of_stable (h : ∀ (σ : GK p K), ∀ x ∈ L, σ x ∈ L) : (subG p K L).Normal := by
  refine ⟨fun n hn g x hx => ?_⟩
  show g (n (g⁻¹ x)) = x
  rw [hn _ (h g⁻¹ x hx)]
  show (g * g⁻¹) x = x
  rw [mul_inv_cancel]; rfl

theorem norm_map_GK (σ : GK p K) (x : PadicAlgCl p) : ‖σ x‖ = ‖x‖ :=
  (spectralNorm_eq_of_equiv (σ.restrictScalars ℚ_[p]) x).symm

theorem vbar_kbarRep (σ : GK p K) (x : KbarMult p) : vbar p (kbarRep p K σ x) = vbar p x := by
  rw [vbar_apply, vbar_apply]
  show - Real.logb p ‖σ ((Additive.toMul x : (PadicAlgCl p)ˣ) : PadicAlgCl p)‖ = _
  rw [norm_map_GK]

def MaximalUnramifiedExtension : IntermediateField ℚ_[p] (PadicAlgCl p) := ⨆ n : ℕ, Kn p K (n + 1)

theorem Kn_stable (n : ℕ) (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ Kn p K n) : σ x ∈ Kn p K n := by
  have h : Kn p K n ≤ (Kn p K n).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) := by
    refine sup_le (fun y hy => ?_) (IntermediateField.adjoin_le_iff.2 fun ζ hζ => ?_)
    · show σ y ∈ Kn p K n
      rw [show σ y = y from σ.commutes ⟨y, hy⟩]
      exact (le_sup_left : K ≤ Kn p K n) hy
    · show σ ζ ∈ Kn p K n
      refine (le_sup_right : _ ≤ Kn p K n) (IntermediateField.subset_adjoin _ _ ?_)
      show (σ ζ) ^ (qK p K ^ n - 1) = 1
      rw [← map_pow, show ζ ^ (qK p K ^ n - 1) = 1 from hζ, map_one]
  exact h hx

theorem Kur_stable (σ : GK p K) (x : PadicAlgCl p) (hx : x ∈ MaximalUnramifiedExtension p K) : σ x ∈ MaximalUnramifiedExtension p K := by
  have h : MaximalUnramifiedExtension p K ≤ (MaximalUnramifiedExtension p K).comap ((σ.restrictScalars ℚ_[p] : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
      PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p) :=
    iSup_le fun n y hy => (le_iSup (fun n : ℕ => Kn p K (n + 1)) n) (Kn_stable p K (n + 1) σ y hy)
  exact h hx

scoped instance subG_Kn_normal (n : ℕ) : (subG p K (Kn p K n)).Normal := subG_normal_of_stable (Kn_stable p K n)

scoped instance subG_Kur_normal : (subG p K (MaximalUnramifiedExtension p K)).Normal := subG_normal_of_stable (Kur_stable p K)

def IsFrob (σ : GK p K) : Prop := ∀ x : PadicAlgCl p, ‖x‖ ≤ 1 → ‖σ x - x ^ qK p K‖ < 1

def frobK : GK p K := Classical.epsilon (IsFrob p K)

def frobLK : GalLK p K L := QuotientGroup.mk (frobK p K)

def ubarRep : Representation ℤ (GK p K) (Ubar p) where
  toFun σ := (kbarRep p K σ).restrict (p := Ubar p) (q := Ubar p)
    (fun x hx => (vbar_kbarRep p K σ x).trans hx)
  map_one' := LinearMap.ext fun x => Subtype.ext (by
    show kbarRep p K 1 x.1 = x.1
    rw [map_one]; rfl)
  map_mul' σ τ := LinearMap.ext fun x => Subtype.ext (by
    show kbarRep p K (σ * τ) x.1 = kbarRep p K σ (kbarRep p K τ x.1)
    rw [map_mul]; rfl)

scoped instance : TopologicalSpace (Ubar p) := instTopologicalSpaceSubtype

scoped instance : DiscreteTopology (Ubar p) := inferInstanceAs (DiscreteTopology ((Ubar p : Set (KbarMult p))))

scoped instance : IsTopologicalAddGroup (Ubar p) := inferInstance

def ubarT : TRep ℤ (GK p K) where
  V := Ubar p
  rho := ubarRep p K
  cont := by
    exact Continuous.subtype_mk ((kbarT p K).cont.comp (f := fun x : GK p K × Ubar p => (x.1, x.2.1))
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

scoped instance : DiscreteTopology (ubarT p K).V := inferInstanceAs (DiscreteTopology (Ubar p))

def ubarIncl : Pair (ubarT p K) (kbarT p K) :=
  Pair.ofMap (M := ubarT p K) (M' := kbarT p K) (Ubar p).subtype continuous_subtype_val (fun _ _ => rfl)

def mkLin {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G'] {A : TRep ℤ G}
    {B : TRep ℤ G'} (f : A.V →+ B.V) : A.V →ₗ[ℤ] B.V where
  toFun := f
  map_add' := f.map_add
  map_smul' n x := by simp

abbrev layer [(subG p K L).Normal] : TRep ℤ (GalLK p K L) := InflationRestrictionInvariants.invQ (kbarT p K) (subG p K L)

abbrev layerInf [(subG p K L).Normal] : Pair (layer p K L) (kbarT p K) := InflationRestrictionInvariants.invP (kbarT p K) (subG p K L)

abbrev layerU [(subG p K L).Normal] : TRep ℤ (GalLK p K L) := InflationRestrictionInvariants.invQ (ubarT p K) (subG p K L)

scoped instance [(subG p K L).Normal] : DiscreteTopology (layer p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (kbarT p K) (subG p K L)).2.1.discreteTopology

scoped instance [(subG p K L).Normal] : DiscreteTopology (layerU p K L).V :=
  (InflationRestrictionInvariants.invariants_isInvRep (ubarT p K) (subG p K L)).2.1.discreteTopology

def layerUIncl [(subG p K L).Normal] : Pair (layerU p K L) (layer p K L) :=
  Pair.ofMap (M := layerU p K L) (M' := layer p K L)
    (mkLin (A := layerU p K L) (B := layer p K L)
      { toFun := fun x => ⟨(ubarIncl p K).u x.1, fun g => congrArg (ubarIncl p K).u (x.2 g)⟩
        map_zero' := rfl
        map_add' := fun _ _ => rfl })
    continuous_of_discreteTopology
    (fun g x => by
      induction g using QuotientGroup.induction_on with
      | H σ => rfl)

variable {p K} in

def layerInfl {L L' : IntermediateField ℚ_[p] (PadicAlgCl p)} (h : L ≤ L') [(subG p K L).Normal]
    [(subG p K L').Normal] : Pair (layer p K L) (layer p K L') where
  φ := QuotientGroup.map (subG p K L') (subG p K L) (MonoidHom.id _) (fun _ hσ x hx => hσ x (h hx))
  u := mkLin (A := layer p K L) (B := layer p K L')
    { toFun := fun x => ⟨x.1, fun g => x.2 ⟨g.1, fun y hy => g.2 y (h hy)⟩⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  φ_cont := (QuotientGroup.isOpenQuotientMap_mk.isQuotientMap.continuous_iff).2 continuous_quot_mk
  u_cont := continuous_of_discreteTopology
  equiv g m := by
    induction g using QuotientGroup.induction_on with
    | H σ => rfl

open Classical in

def vLayerMap [(subG p K L).Normal] : (layer p K L).V →+ ℤ :=
  if h : ∃ f : (layer p K L).V →+ ℤ, ∀ x, (f x : ℝ) = eK p L * vbar p x.1 then h.choose else 0

theorem vLayerMap_rho [(subG p K L).Normal] (g : GalLK p K L) (x : (layer p K L).V) :
    vLayerMap p K L ((layer p K L).rho g x) = vLayerMap p K L x := by
  induction g using QuotientGroup.induction_on with
  | H σ =>
    unfold vLayerMap
    split_ifs with h
    · apply Int.cast_injective (α := ℝ)
      rw [h.choose_spec, h.choose_spec]
      exact congrArg _ (vbar_kbarRep p K σ x.1)
    · rfl

def vLayer [(subG p K L).Normal] : Pair (layer p K L) (trivRep (GalLK p K L) ℤ) :=
  Pair.ofMap (M := layer p K L) (M' := trivRep (GalLK p K L) ℤ)
    (mkLin (A := layer p K L) (B := trivRep (GalLK p K L) ℤ) (vLayerMap p K L))
    continuous_of_discreteTopology (fun g x => vLayerMap_rho p K L g x)

abbrev Br : Type := (kbarT p K).H 2

def BrLK [(subG p K L).Normal] : Submodule ℤ (Br p K) := LinearMap.range ((layerInf p K L).hom.H 2)

variable {p K L} in

def resPair (h : K ≤ L) : Pair (kbarT p K) (kbarT p L) where
  φ := resGK h
  u := LinearMap.id
  φ_cont := resGK_continuous h
  u_cont := continuous_id
  equiv _ _ := rfl

variable {p K L} in

def BrKer (h : K ≤ L) : Submodule ℤ (Br p K) := LinearMap.ker ((resPair h).hom.H 2)

abbrev urT : TRep ℤ (GalLK p K (MaximalUnramifiedExtension p K)) := layer p K (MaximalUnramifiedExtension p K)

def IsInv (f : (urT p K).H 2 →+ QZ) : Prop :=
  ∀ (π : (urT p K).V) (t : GalLK p K (MaximalUnramifiedExtension p K) → ℚ) (m : (Fin 2 → GalLK p K (MaximalUnramifiedExtension p K)) → ℤ)
    (z : (urT p K).coch.X 2) (hz : (urT p K).coch.d 2 z = 0),
    π.1 ∈ multOf p K → (eK p K : ℝ) * vbar p π.1 = 1 → IsLocallyConstant t →
    (∀ g, (m g : ℚ) = t (g 0) + t (g 1) - t (g 0 * g 1)) → (∀ g, z.1 g = m g • π) →
    f ((urT p K).coch.cls 2 z hz) = QuotientAddGroup.mk (t (frobLK p K (MaximalUnramifiedExtension p K)))

open Classical in

def invUr : (urT p K).H 2 →+ QZ := if h : ∃ f, IsInv p K f then h.choose else 0

end

end ReciprocityTheory.DiscreteGroups.LocalClassField
end
