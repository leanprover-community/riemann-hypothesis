import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.ConjugateLevelLeMaximalCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.LatAdapted
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.CMInst
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelStructures.K2uGrpHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.LocIdxLift
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.MassComputations.NLevelHolds

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge

theorem relIndex_eq_of_le_of_dec {G : Type*} [Group G] (U A B : Subgroup G) (hBA : B ≤ A)
    (hdec : ∀ a ∈ A, ∃ u ∈ U, ∃ b ∈ B, a = u * b) : U.relIndex A = U.relIndex B := by
  unfold Subgroup.relIndex
  rw [Subgroup.index, Subgroup.index]
  symm
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' (Subgroup.inclusion hBA) ?_) ⟨?_, ?_⟩)
  · intro x y h
    rw [QuotientGroup.leftRel_apply] at h ⊢
    simpa [Subgroup.mem_subgroupOf] using h
  · intro p q h
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
    have h' : (QuotientGroup.mk (Subgroup.inclusion hBA x) : A ⧸ U.subgroupOf A) =
        QuotientGroup.mk (Subgroup.inclusion hBA y) := h
    rw [QuotientGroup.eq] at h' ⊢
    simpa [Subgroup.mem_subgroupOf] using h'
  · intro p
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨u, hu, b, hb, hab⟩ := hdec (a : G)⁻¹ (A.inv_mem a.2)
    refine ⟨QuotientGroup.mk ⟨b⁻¹, B.inv_mem hb⟩, ?_⟩
    show (QuotientGroup.mk (Subgroup.inclusion hBA ⟨b⁻¹, B.inv_mem hb⟩) : A ⧸ U.subgroupOf A) = QuotientGroup.mk a
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha : (a : G) = b⁻¹ * u⁻¹ := by rw [← mul_inv_rev, ← hab, inv_inv]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_inv]
    rw [ha, ← mul_assoc, mul_inv_cancel, one_mul]
    exact U.inv_mem hu

theorem closure_val_preimage_eq_subgroupOf {G : Type*} [Group G] (S V : Subgroup G) :
    Subgroup.closure (Subtype.val ⁻¹' (V : Set G) : Set S) = V.subgroupOf S := by
  rw [show (Subtype.val ⁻¹' (V : Set G) : Set S) = (V.subgroupOf S : Set S) from
    (Subgroup.coe_subgroupOf V S).symm, Subgroup.closure_eq]

theorem relIndex_traces {G : Type*} [Group G] (S U K : Subgroup G) :
    (Subgroup.closure (Subtype.val ⁻¹' (U : Set G) : Set S)).relIndex
      (Subgroup.closure (Subtype.val ⁻¹' (K : Set G) : Set S)) = U.relIndex (K ⊓ S) := by
  rw [closure_val_preimage_eq_subgroupOf, closure_val_preimage_eq_subgroupOf, ← Subgroup.inf_subgroupOf_right K S,
    Subgroup.relIndex_subgroupOf inf_le_right]

theorem Hsub_le_Ssub {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ} (P : Frame E n r) :
    Hsub R σ J P ≤ Ssub R σ J P := by
  intro g hg
  rw [Hsub, mem_stabT] at hg
  show UniC R σ J (F0 P) g
  intro b
  have h := hg (Fin.castAdd r b)
  simp only [tupH, Fin.append_left] at h
  rw [h, sub_self]
  exact Submodule.zero_mem _

variable {D : D7}

def KvSubT (X : HidaSetting D) (p : TypX X) : Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1
  one_mem' := (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).one_mem
  mul_mem' := fun ha hb => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).mul_mem ha hb
  inv_mem' := fun ha => (Kloc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))).inv_mem ha

theorem finiteAdelic_map_mul (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x y : X.B.I.Gf) :
    finHA X hb (x * y) = finHA X hb x * finHA X hb y := by
  unfold finHA
  rw [show ((1 : _), x * y) = ((1, x) * (1, y) : X.B.I.GA) from by simp, map_mul, map_mul, Prod.snd_mul]

theorem finiteAdelic_map_inv (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf) :
    finHA X hb x⁻¹ = (finHA X hb x)⁻¹ := by
  unfold finHA
  rw [show ((1 : _), x⁻¹) = ((1, x)⁻¹ : X.B.I.GA) from by simp, map_inv, map_inv, Prod.snd_inv]

theorem finiteAdelic_map_one (X : HidaSetting D) (hb : AdBridgeIso X.B.I) : finHA X hb 1 = 1 := by
  unfold finHA
  rw [show ((1 : _), (1 : X.B.I.Gf)) = (1 : X.B.I.GA) from rfl, map_one, map_one, Prod.snd_one]

theorem mem_local_component_iff (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (w : D.what₂.Word) (p : TypX X)
    (z : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) :
    z ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1 ↔
      ∃ k ∈ X.K2, haMap X.B.I.cm.sig X.B.I.J (evalV X.B.I.F p.1)
        (finHA X hb (X.xu w) * finHA X hb k * (finHA X hb (X.xu w))⁻¹) = z := by
  simp only [compSet, K2u, levelUnitary, Set.mem_image]
  constructor
  · rintro ⟨y, ⟨y', ⟨k, hk, rfl⟩, rfl⟩, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨_, ⟨_, ⟨k, hk, rfl⟩, rfl⟩, rfl⟩

def conjugateLevelLocalSubgroup (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (w : D.what₂.Word) (p : TypX X) :
    Subgroup (HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J) where
  carrier := compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1
  one_mem' := by
    refine (mem_local_component_iff X hb w p _).2 ⟨1, hK.1, ?_⟩
    rw [finiteAdelic_map_one, mul_one, mul_inv_cancel, map_one]
  mul_mem' := by
    intro a b ha hb'
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    obtain ⟨k2, hk2, e2⟩ := (mem_local_component_iff X hb w p _).1 hb'
    refine (mem_local_component_iff X hb w p _).2 ⟨k1 * k2, hK.2.1 _ hk1 _ hk2, ?_⟩
    rw [← e1, ← e2, ← map_mul, finiteAdelic_map_mul]
    congr 1
    group
  inv_mem' := by
    intro a ha
    obtain ⟨k1, hk1, e1⟩ := (mem_local_component_iff X hb w p _).1 ha
    refine (mem_local_component_iff X hb w p _).2 ⟨k1⁻¹, hK.2.2.1 _ hk1, ?_⟩
    rw [← e1, ← map_inv, finiteAdelic_map_inv]
    congr 1
    group

def LeviRat : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ n h, n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧
      h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) ∧ s = n * h

def LeviIntH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (n h : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    n * h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
    h ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1

def UnipotentIntegralInLevel : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I), X.LevelSubgroupCharacter → X.MeasTie hb → X.LevelSubgroupNormalized →
    ∀ (w : D.what₂.Word) (p : TypX X) (n : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
      n ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
      n ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) p.1 →
      n ∈ compSet X.B.I.cm.sig X.B.I.J (K2u X hb w) p.1

theorem locLevi_of (ha : LeviRat) (hbI : LeviIntH) (hc : UnipotentIntegralInLevel) : LocLevi := by
  intro D X hb hK hM hL w p
  have e1 : idxS X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxS
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  have e2 : idxHp X hb w p = (conjugateLevelLocalSubgroup X hb hK w p).relIndex
      (KvSubT X p ⊓ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w)) := by
    unfold idxHp
    exact relIndex_traces _ (conjugateLevelLocalSubgroup X hb hK w p) (KvSubT X p)
  rw [e1, e2]
  apply relIndex_eq_of_le_of_dec
  · exact inf_le_inf_left _ (Hsub_le_Ssub _ _ _ _)
  · rintro a ⟨haK, haS⟩
    obtain ⟨n, h, hn, hh, rfl⟩ := ha X w p a haS
    have hhK := hbI X w p n h hn hh haK
    have hnK : n ∈ KvSubT X p := by
      have e : n = (n * h) * h⁻¹ := by group
      rw [e]
      exact (KvSubT X p).mul_mem haK ((KvSubT X p).inv_mem hhK)
    exact ⟨n, hc X hb hK hM hL w p n hn hnK, h, ⟨hhK, hh⟩, rfl⟩

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)

theorem hermForm_add_right_bis (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y + z) = hR R σ J x y + hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hermForm_sub_right (x y z : Fin n → R ⊗[F] E) :
    hR R σ J x (y - z) = hR R σ J x y - hR R σ J x z := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem hermForm_smul_right_alt (c : R ⊗[F] E) (x y : Fin n → R ⊗[F] E) :
    hR R σ J x (c • y) = c * hR R σ J x y := by
  simp only [hR, Formalism.UG.hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hermForm_sum_right_alt {ι : Type} (s : Finset ι) (d : ι → R ⊗[F] E) (v : ι → Fin n → R ⊗[F] E)
    (x : Fin n → R ⊗[F] E) : hR R σ J x (∑ i ∈ s, d i • v i) = ∑ i ∈ s, d i * hR R σ J x (v i) := by
  classical
  induction s using Finset.induction_on
  · simp only [Finset.sum_empty, hR, Formalism.UG.hform, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  · rename_i a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hermForm_add_right_bis, hermForm_smul_right_alt, ih]

theorem conjTensor_incl (a : E) : sigR R σ (inclR R a) = inclR R (σ a) := by
  simp [sigR, inclR]

theorem hermForm_rational_vectors (x y : Fin n → E) :
    hR R σ J (ratV (F := F) R x) (ratV (F := F) R y) = inclR R (hE σ J x y) := by
  simp [hR, hE, Formalism.UG.hform, ratV, JR, conjTensor_incl, map_sum, map_mul]

theorem mem_tensor_span_iff {r : ℕ} (Y : Fin r → Fin n → E) (y : Fin n → R ⊗[F] E)
    (hy : y ∈ spanR (F := F) R Y Set.univ) : ∃ d : Fin r → R ⊗[F] E, y = ∑ i, d i • ratV (F := F) R (Y i) := by
  simp only [spanR, Set.image_univ] at hy
  rw [Submodule.mem_span_range_iff_exists_fun] at hy
  obtain ⟨d, hd⟩ := hy
  exact ⟨d, hd.symm⟩

def WbR {r : ℕ} (P : Frame E n r) (w : Fin n → R ⊗[F] E) : Prop :=
  ∀ i, hR R σ J (ratV (F := F) R (P.e i)) w = 0 ∧ hR R σ J (ratV (F := F) R (P.f i)) w = 0

def WbSub {r : ℕ} (P : Frame E n r) : Submodule (R ⊗[F] E) (Fin n → R ⊗[F] E) where
  carrier := {w | WbR R σ J P w}
  add_mem' := by
    intro a b ha hb i
    rw [hermForm_add_right_bis, hermForm_add_right_bis, (ha i).1, (hb i).1, (ha i).2, (hb i).2]
    simp
  zero_mem' := by
    intro i
    have h := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.e i)) 0
    have h' := hermForm_smul_right_alt R σ J 0 (ratV (F := F) R (P.f i)) 0
    simp only [zero_smul, zero_mul] at h h'
    exact ⟨h, h'⟩
  smul_mem' := by
    intro c w hw i
    rw [hermForm_smul_right_alt, hermForm_smul_right_alt, (hw i).1, (hw i).2]
    simp

variable {R σ J}

theorem witt_decomposition_unique {r : ℕ} (P : Frame E n r) (hee : ∀ a b, hE σ J (P.e a) (P.e b) = 0)
    (hef : ∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if a = b then 1 else 0)
    {x a w b c : Fin n → R ⊗[F] E} (hx : x ∈ spanR (F := F) R P.e Set.univ)
    (ha : a ∈ spanR (F := F) R P.e Set.univ) (hc : c ∈ spanR (F := F) R P.f Set.univ)
    (hw : WbR R σ J P w) (hb : WbR R σ J P b) (h : x + w = a + b + c) : w = b := by
  classical
  have hax : a - x ∈ spanR (F := F) R P.e Set.univ := Submodule.sub_mem _ ha hx
  obtain ⟨g, hg⟩ := mem_tensor_span_iff (R := R) P.e (a - x) hax
  obtain ⟨d, hd⟩ := mem_tensor_span_iff (R := R) P.f c hc
  have hw' : w = a + b + c - x := by
    rw [← h]
    abel
  have hwb : w - b = (a - x) + c := by
    rw [hw']
    abel
  have hd0 : ∀ k, d k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.e k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).1, (hb k).1, sub_self]
    have h2 : hR R σ J (ratV (F := F) R (P.e k)) (a - x) = 0 := by
      rw [hg, hermForm_sum_right_alt]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [hermForm_rational_vectors, hee, map_zero, mul_zero]
    have h3 : hR R σ J (ratV (F := F) R (P.e k)) c = d k := by
      rw [hd, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hef, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hef, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hermForm_add_right_bis, h2, h3, zero_add] at h1
    exact h1
  have hc0 : c = 0 := by
    rw [hd]
    exact Finset.sum_eq_zero fun i _ => by rw [hd0 i, zero_smul]
  have hg0 : ∀ k, g k = 0 := by
    intro k
    have h1 : hR R σ J (ratV (F := F) R (P.f k)) (w - b) = 0 := by
      rw [hermForm_sub_right, (hw k).2, (hb k).2, sub_self]
    have h3 : hR R σ J (ratV (F := F) R (P.f k)) (a - x) = g k := by
      rw [hg, hermForm_sum_right_alt, Finset.sum_eq_single k]
      · rw [hermForm_rational_vectors, hfe, if_pos rfl, map_one, mul_one]
      · intro i _ hik
        rw [hermForm_rational_vectors, hfe, if_neg (Ne.symm hik), map_zero, mul_zero]
      · intro hk
        exact absurd (Finset.mem_univ k) hk
    rw [hwb, hc0, add_zero, h3] at h1
    exact h1
  have hax0 : a - x = 0 := by
    rw [hg]
    exact Finset.sum_eq_zero fun i _ => by rw [hg0 i, zero_smul]
  have hwb0 : w - b = 0 := by
    rw [hwb, hax0, hc0, add_zero]
  exact sub_eq_zero.mp hwb0

end Alg

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Grp

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hermForm_base_conj_symm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → E) :
    σ (hE σ J x y) = hE σ J y x := by
  unfold hE Formalism.UG.hform
  simp only [map_sum, map_mul, AlgHom.coe_toRingHom, hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hJ a b]
  ring

theorem rational_vector_mem_span {r : ℕ} (Y : Fin r → Fin n → E) (x : Fin n → E)
    (hx : x ∈ Submodule.span E (Set.range Y)) : ratV (F := F) R x ∈ spanR (F := F) R Y Set.univ := by
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, rfl⟩ := hu
    exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
  | zero =>
    have e0 : ratV (F := F) R (0 : Fin n → E) = 0 := funext fun i => map_zero _
    rw [e0]
    exact Submodule.zero_mem _
  | add u w _ _ hu hw =>
    have e0 : ratV (F := F) R (u + w) = ratV (F := F) R u + ratV (F := F) R w :=
      funext fun i => map_add _ _ _
    rw [e0]
    exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    have e0 : ratV (F := F) R (c • u) = inclR (F := F) R c • ratV (F := F) R u :=
      funext fun i => by
        first
          | (simp only [ratV, Pi.smul_apply, smul_eq_mul]; exact map_mul _ _ _)
          | (simp [ratV, map_mul]; rfl)
    rw [e0]
    exact Submodule.smul_mem _ _ hu

theorem rational_vector_in_complement {r : ℕ} (P : Frame E n r) (x : Fin n → E) (hx : ∀ a, hE σ J (P.e a) x = 0 ∧ hE σ J (P.f a) x = 0) :
    WbR R σ J P (ratV (F := F) R x) := fun i => ⟨by rw [hermForm_rational_vectors, (hx i).1, map_zero], by rw [hermForm_rational_vectors, (hx i).2, map_zero]⟩

theorem stabilizer_fixes_isotropic_e {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.e a)) = ratV (F := F) R (P.e a) := by
  have hfix : h • ratTup (F := F) R (tupH P) = ratTup (F := F) R (tupH P) := hh
  have h1 : lin R σ J h (ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a))) =
      ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a)) := congrFun hfix _
  have e1 : ratTup (F := F) R (tupH P) (Fin.castAdd r (Fin.castSucc a)) = ratV (F := F) R (P.e a) := by
    funext i
    simp [ratTup, tupH, F0, ratV]
  rwa [e1] at h1

theorem stabilizer_fixes_isotropic_f {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (a : Fin r) :
    lin R σ J h (ratV (F := F) R (P.f a)) = ratV (F := F) R (P.f a) := by
  have hfix : h • ratTup (F := F) R (tupH P) = ratTup (F := F) R (tupH P) := hh
  have h1 : lin R σ J h (ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a)) =
      ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a) := congrFun hfix _
  have e1 : ratTup (F := F) R (tupH P) (Fin.natAdd (r + 1) a) = ratV (F := F) R (P.f a) := by
    funext i
    simp [ratTup, tupH, F0, ratV]
  rwa [e1] at h1

theorem stabilizer_fixes_span {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) (Y : Fin r → Fin n → E)
    (hY : ∀ a, lin R σ J h (ratV (F := F) R (Y a)) = ratV (F := F) R (Y a))
    (y : Fin n → R ⊗[F] E) (hy : y ∈ spanR (F := F) R Y Set.univ) : lin R σ J h y = y := by
  induction hy using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, _, rfl⟩ := hu
    exact hY a
  | zero => exact map_zero _
  | add u w _ _ hu hw => rw [map_add, hu, hw]
  | smul c u _ hu => rw [map_smul, hu]

theorem stabilizer_preserves_complement {r : ℕ} (P : Frame E n r) {h : HA R σ J} (hh : h ∈ Hsub R σ J P) {w : Fin n → R ⊗[F] E}
    (hw : WbR R σ J P w) : WbR R σ J P (lin R σ J h w) := fun i => ⟨by rw [← stabilizer_fixes_isotropic_e P hh i, hR_lin]; exact (hw i).1,
    by rw [← stabilizer_fixes_isotropic_f P hh i, hR_lin]; exact (hw i).2⟩

end Grp

section Lat

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
  {J : Matrix (Fin n) (Fin n) E} (v : HeightOneSpectrum (𝓞 F))

theorem localLattice_union (A B : Set (Fin n → E)) :
    latLoc (E := E) v (A ∪ B) = latLoc v A ⊔ latLoc v B := by
  unfold latLoc
  rw [Set.image_union, Submodule.span_union]

theorem localLattice_le_span {r : ℕ} (Y : Fin r → Fin n → E) (A : Set (Fin n → E))
    (hA : ∀ x ∈ A, x ∈ Submodule.span E (Set.range Y)) :
    latLoc (E := E) v A ≤ (spanR (F := F) (Fv F v) Y Set.univ).restrictScalars (v.adicCompletionIntegers F) := by
  unfold latLoc
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact rational_vector_mem_span (F := F) Y x (hA x hx)

theorem localLattice_le_complement {r : ℕ} (P : Frame E n r) (A : Set (Fin n → E))
    (hA : ∀ w ∈ A, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0) :
    latLoc (E := E) v A ≤ (WbSub (Fv F v) σ J P).restrictScalars (v.adicCompletionIntegers F) := by
  unfold latLoc
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  exact rational_vector_in_complement (σ := σ) (J := J) P x (hA x hx)

theorem witt_decomposition_lattice {r : ℕ} (P : Frame E n r) (hee : ∀ a b, hE σ J (P.e a) (P.e b) = 0)
    (hef : ∀ a b, hE σ J (P.e a) (P.f b) = if a = b then 1 else 0)
    (hfe : ∀ a b, hE σ J (P.f a) (P.e b) = if a = b then 1 else 0)
    (A B C : Set (Fin n → E)) (hA : ∀ x ∈ A, x ∈ Submodule.span E (Set.range P.e))
    (hC : ∀ y ∈ C, y ∈ Submodule.span E (Set.range P.f))
    (hB : ∀ w ∈ B, ∀ a, hE σ J (P.e a) w = 0 ∧ hE σ J (P.f a) w = 0)
    {m x w : Fin n → Fv F v ⊗[F] E} (hm : m ∈ latLoc (E := E) v (A ∪ B ∪ C))
    (hx : x ∈ spanR (F := F) (Fv F v) P.e Set.univ) (hw : WbR (Fv F v) σ J P w) (h : m = x + w) :
    w ∈ latLoc (E := E) v B := by
  rw [localLattice_union, localLattice_union] at hm
  obtain ⟨ab, hab, c, hc, rfl⟩ := Submodule.mem_sup.1 hm
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hab
  have ha' := localLattice_le_span v P.e A hA ha
  have hb' := localLattice_le_complement (σ := σ) (J := J) v P B hB hb
  have hc' := localLattice_le_span v P.f C hC hc
  have hwb := witt_decomposition_unique (P := P) (hee := hee) (hef := hef) (hfe := hfe) (hx := hx) (ha := ha')
    (hc := hc') (hw := hw) (hb := hb') (h := h.symm)
  rw [hwb]
  exact hb

theorem lin_mem_localLattice (g : HA (Fv F v) σ J) (A : Set (Fin n → E))
    (hg : ∀ y ∈ A, lin (Fv F v) σ J g (ratV (F := F) (Fv F v) y) ∈ latLoc (E := E) v A)
    (m : Fin n → Fv F v ⊗[F] E) (hm : m ∈ latLoc (E := E) v A) : lin (Fv F v) σ J g m ∈ latLoc (E := E) v A := by
  unfold latLoc at hm ⊢
  induction hm using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨y, hy, rfl⟩ := hu
    exact hg y hy
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add u w _ _ hu hw => rw [map_add]; exact Submodule.add_mem _ hu hw
  | smul c u _ hu =>
    rw [LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ hu

end Lat

variable {D : D7}

theorem leviIntH : LeviIntH := by
  intro D X w p n h hn hh hK
  classical
  have hstd := FrameW.frameOf_isStd X w
  have hee := hstd.1
  have hef := hstd.2.2.1
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => by simp [FrameW.sig_apply]
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := (cmInst_holds X).2.1
  have hfe : ∀ a b, hE X.B.I.cm.sig X.B.I.J ((frameOf X w).f a) ((frameOf X w).e b) = if a = b then 1 else 0 := by
    intro a b
    rw [← hermForm_base_conj_symm hσ hJ, hef b a]
    split_ifs with h1 h2 h2 <;> simp_all
  have had := LatW.adapted X w
  set M := latLoc (E := X.B.I.E) p.1 (LatW.LX X ∪ LatW.LW X ∪ LatW.LY X) with hM
  have hML : latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) = M := (LatW.latLoc_eq X p.1).symm
  have hK' : ∀ x, x ∈ M ↔ lin _ X.B.I.cm.sig X.B.I.J (n * h) x ∈ M := by
    rw [← hML]; exact fun x => hK x
  have hKi : (n * h)⁻¹ ∈ KvSubT X p := (KvSubT X p).inv_mem hK
  have hKi' : ∀ x, x ∈ M ↔ lin _ X.B.I.cm.sig X.B.I.J (n * h)⁻¹ x ∈ M := by
    rw [← hML]; exact fun x => hKi x
  have hgen : ∀ y ∈ LatW.LX X ∪ LatW.LW X ∪ LatW.LY X, ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y ∈ M :=
    fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  have hWgen : ∀ y ∈ LatW.LW X, ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y ∈ M :=
    fun y hy => hgen y (Or.inl (Or.inr hy))
  have hLWM : ∀ u, u ∈ latLoc (E := X.B.I.E) p.1 (LatW.LW X) → u ∈ M := by
    intro u hu
    exact (Submodule.span_mono (Set.image_mono (fun y hy => Or.inl (Or.inr hy)))) hu
  have hdec : ∀ {m x w' : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E}, m ∈ M →
      x ∈ spanR (F := X.B.I.F) (Fv X.B.I.F p.1) (frameOf X w).e Set.univ →
      WbR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) w' → m = x + w' →
      w' ∈ latLoc (E := X.B.I.E) p.1 (LatW.LW X) := fun hm hx hw he =>
    witt_decomposition_lattice p.1 (frameOf X w) hee hef hfe (LatW.LX X) (LatW.LW X) (LatW.LY X) had.1 had.2.1 had.2.2 hm hx hw he
  have hh' : h⁻¹ ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) := inv_mem hh
  have hn' : n⁻¹ ∈ Nsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) := inv_mem hn

  have hXY : ∀ g ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w), ∀ y ∈ LatW.LX X ∪ LatW.LY X,
      lin _ X.B.I.cm.sig X.B.I.J g (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) = ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y := by
    intro g hg y hy
    rcases hy with hy | hy
    · exact stabilizer_fixes_span (frameOf X w) hg _ (stabilizer_fixes_isotropic_e (frameOf X w) hg) _ (rational_vector_mem_span _ y (had.1 y hy))
    · exact stabilizer_fixes_span (frameOf X w) hg _ (stabilizer_fixes_isotropic_f (frameOf X w) hg) _ (rational_vector_mem_span _ y (had.2.1 y hy))

  have hW1 : ∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M := by
    intro y hy
    set u := lin _ X.B.I.cm.sig X.B.I.J h (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y)
    have hu : WbR _ X.B.I.cm.sig X.B.I.J (frameOf X w) u := stabilizer_preserves_complement (frameOf X w) hh (rational_vector_in_complement _ y (had.2.2 y hy))
    have hnu := hn.2 u (fun a => (hu a).1)
    have hm : lin _ X.B.I.cm.sig X.B.I.J n u ∈ M := by
      have := (hK' _).1 (hWgen y hy)
      rwa [lin_mul] at this
    exact hLWM u (hdec hm hnu hu (sub_add_cancel _ _).symm)

  have hW2 : ∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J h⁻¹ (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M := by
    intro y hy
    set y' := ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y
    have hy' : WbR _ X.B.I.cm.sig X.B.I.J (frameOf X w) y' := rational_vector_in_complement _ y (had.2.2 y hy)
    have hx' := hn'.2 y' (fun a => (hy' a).1)
    set x' := lin _ X.B.I.cm.sig X.B.I.J n⁻¹ y' - y'
    have hfix : lin _ X.B.I.cm.sig X.B.I.J h⁻¹ x' = x' :=
      stabilizer_fixes_span (frameOf X w) hh' _ (stabilizer_fixes_isotropic_e (frameOf X w) hh') _ hx'
    have hm : x' + lin _ X.B.I.cm.sig X.B.I.J h⁻¹ y' ∈ M := by
      have := (hKi' _).1 (hWgen y hy)
      rw [mul_inv_rev, lin_mul] at this
      have e : lin _ X.B.I.cm.sig X.B.I.J n⁻¹ y' = y' + x' := by simp [x']
      rw [e, map_add, hfix, add_comm] at this
      exact this
    exact hLWM _ (hdec hm hx' (stabilizer_preserves_complement (frameOf X w) hh' hy') rfl)
  have hall : ∀ g ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w),
      (∀ y ∈ LatW.LW X, lin _ X.B.I.cm.sig X.B.I.J g (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) y) ∈ M) →
      ∀ m ∈ M, lin _ X.B.I.cm.sig X.B.I.J g m ∈ M := by
    intro g hgH hgW m hm
    refine lin_mem_localLattice p.1 g _ ?_ m hm
    intro y hy
    rcases hy with (hy | hy) | hy
    · rw [hXY g hgH y (Or.inl hy)]; exact hgen y (Or.inl (Or.inl hy))
    · exact hgW y hy
    · rw [hXY g hgH y (Or.inr hy)]; exact hgen y (Or.inr hy)
  show ∀ x, x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) ↔
    lin _ X.B.I.cm.sig X.B.I.J h x ∈ latLoc (E := X.B.I.E) p.1 (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
  rw [hML]
  intro x
  constructor
  · exact hall h hh hW1 x
  · intro hx
    have := hall h⁻¹ hh' hW2 _ hx
    rwa [lin_inv_lin] at this

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

def LeviComp : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (w : D.what₂.Word) (p : TypX X) (s : HA (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J),
    s ∈ Ssub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) →
    ∃ h ∈ Hsub (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w),
      ∀ u, InXperp (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (frameOf X w) u →
        lin _ X.B.I.cm.sig X.B.I.J s u - lin _ X.B.I.cm.sig X.B.I.J h u ∈
          spanR (F := X.B.I.F) (Fv X.B.I.F p.1) (frameOf X w).e Set.univ

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem parabolic_unipotent_on_flag {r : ℕ} (P : Frame E n r) {s : HA R σ J} (hs : s ∈ Ssub R σ J P) (b : Fin r) :
    lin R σ J s (ratV (F := F) R (P.e b)) - ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e {a | a < b} := by
  have h := hs (Fin.castSucc b)
  have e : F0 P (Fin.castSucc b) = P.e b := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  have hne : a ≠ Fin.last r := fun hl => by
    rw [hl] at ha
    exact absurd ha (not_lt.2 (Fin.castSucc_lt_last b).le)
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 hne
  have ha' : a' < b := Fin.castSucc_lt_castSucc_iff.1 ha
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e {a | a < b}
  rw [e']
  exact Submodule.subset_span ⟨a', ha', rfl⟩

theorem mul_inv_mem_Nsub_of_same_perp_action {r : ℕ} (P : Frame E n r) {s h : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hh : h ∈ Hsub R σ J P)
    (hsh : ∀ u, InXperp R σ J P u → lin R σ J s u - lin R σ J h u ∈ spanR (F := F) R P.e Set.univ) :
    s * h⁻¹ ∈ Nsub R σ J P := by
  have hh' : h⁻¹ ∈ Hsub R σ J P := inv_mem hh
  refine ⟨fun b => ?_, fun v hv => ?_⟩
  · rw [lin_mul, stabilizer_fixes_isotropic_e P hh' b]
    exact parabolic_unipotent_on_flag P hs b
  · have hu : InXperp R σ J P (lin R σ J h⁻¹ v) := by
      intro a
      rw [← stabilizer_fixes_isotropic_e P hh' a, hR_lin]
      exact hv a
    have := hsh _ hu
    rw [lin_lin_inv] at this
    rw [lin_mul]
    exact this

end Gen

theorem leviRat_of (hc : LeviComp) : LeviRat := by
  intro D X w p s hs
  obtain ⟨h, hh, hsh⟩ := hc X w p s hs
  exact ⟨s * h⁻¹, h, mul_inv_mem_Nsub_of_same_perp_action (frameOf X w) hs hh hsh, hh, by group⟩

theorem locLevi_of_comp (hc : LeviComp) (hN : UnipotentIntegralInLevel) : LocLevi :=
  locLevi_of (leviRat_of hc) leviIntH hN

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Proj

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem conjTensor_involutive (hσ : ∀ x, σ (σ x) = x) (a : R ⊗[F] E) : sigR R σ (sigR R σ a) = a := by
  induction a using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem hermForm_conj_symm (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (x y : Fin n → R ⊗[F] E) :
    sigR R σ (hR R σ J x y) = hR R σ J y x := by
  unfold hR Formalism.UG.hform
  simp only [map_sum, map_mul, conjTensor_involutive hσ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have hJ' : sigR R σ (JR R J j i) = JR R J i j := by
    simp only [JR, Matrix.map_apply, conjTensor_incl, hJ]
  rw [hJ']
  ring

theorem hR_sum_smul_left' {ι : Type} (s : Finset ι) (d : ι → R ⊗[F] E) (v : ι → Fin n → R ⊗[F] E)
    (y : Fin n → R ⊗[F] E) : hR R σ J (∑ i ∈ s, d i • v i) y = ∑ i ∈ s, sigR R σ (d i) * hR R σ J (v i) y := by
  induction s using Finset.cons_induction with
  | empty => simp [hR_zero_left]
  | cons a s ha ih => rw [Finset.sum_cons, Finset.sum_cons, hR_add_left, hR_smul_left, ih]

def hl (x : Fin n → R ⊗[F] E) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] R ⊗[F] E where
  toFun := hR R σ J x
  map_add' := hermForm_add_right_bis R σ J x
  map_smul' := fun c y => by rw [hermForm_smul_right_alt]; rfl

variable {r : ℕ} (P : Frame E n r) (c : R ⊗[F] E)

def piRest : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  (∑ a, (hl (σ := σ) (J := J) (ratV (F := F) R (P.f a))).smulRight (ratV (F := F) R (P.e a))) +
  (∑ a, (hl (σ := σ) (J := J) (ratV (F := F) R (P.e a))).smulRight (ratV (F := F) R (P.f a))) +
  c • (hl (σ := σ) (J := J) (ratV (F := F) R P.z)).smulRight (ratV (F := F) R P.z)

def piW : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) := LinearMap.id - piRest (σ := σ) (J := J) P c

theorem piRest_apply (v : Fin n → R ⊗[F] E) : piRest (σ := σ) (J := J) P c v =
    (∑ a, hR R σ J (ratV (F := F) R (P.f a)) v • ratV (F := F) R (P.e a)) +
    (∑ a, hR R σ J (ratV (F := F) R (P.e a)) v • ratV (F := F) R (P.f a)) +
    (c * hR R σ J (ratV (F := F) R P.z) v) • ratV (F := F) R P.z := by
  simp [piRest, hl, smul_smul]

theorem piW_add_rest (v : Fin n → R ⊗[F] E) :
    piW (σ := σ) (J := J) P c v + piRest (σ := σ) (J := J) P c v = v := by
  simp [piW]

structure FrameTab (T : F) : Prop where
  ee : ∀ a b, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.e b)) = 0
  ef : ∀ a b, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R (P.f b)) = if a = b then 1 else 0
  fe : ∀ a b, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.e b)) = if a = b then 1 else 0
  ff : ∀ a b, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R (P.f b)) = 0
  ez : ∀ a, hR R σ J (ratV (F := F) R (P.e a)) (ratV (F := F) R P.z) = 0
  fz : ∀ a, hR R σ J (ratV (F := F) R (P.f a)) (ratV (F := F) R P.z) = 0
  ze : ∀ a, hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R (P.e a)) = 0
  zf : ∀ a, hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R (P.f a)) = 0
  zz : c * hR R σ J (ratV (F := F) R P.z) (ratV (F := F) R P.z) = 1
  hσ : ∀ x, σ (σ x) = x
  hJ : ∀ i j, σ (J j i) = J i j

def InW (v : Fin n → R ⊗[F] E) : Prop :=
  (∀ a, hR R σ J (ratV (F := F) R (P.e a)) v = 0) ∧ (∀ a, hR R σ J (ratV (F := F) R (P.f a)) v = 0) ∧
    hR R σ J (ratV (F := F) R P.z) v = 0

variable {P c} {T : F}

theorem piW_inW (ht : FrameTab (σ := σ) (J := J) P c T) (v : Fin n → R ⊗[F] E) :
    InW (σ := σ) (J := J) P (piW (σ := σ) (J := J) P c v) := by
  have key : (∀ b, hR R σ J (ratV (F := F) R (P.e b)) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R (P.e b)) v) ∧
      (∀ b, hR R σ J (ratV (F := F) R (P.f b)) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R (P.f b)) v) ∧
      hR R σ J (ratV (F := F) R P.z) (piRest (σ := σ) (J := J) P c v) =
        hR R σ J (ratV (F := F) R P.z) v := by
    refine ⟨fun b => ?_, fun b => ?_, ?_⟩ <;>
      rw [piRest_apply, hermForm_add_right_bis, hermForm_add_right_bis, hermForm_sum_right_alt, hermForm_sum_right_alt,
        hermForm_smul_right_alt]
    · simp [ht.ee, ht.ef, ht.ez]
    · simp [ht.fe, ht.ff, ht.fz]
    · simp only [ht.ze, ht.zf, mul_zero, Finset.sum_const_zero, zero_add]
      linear_combination (hR R σ J (ratV (F := F) R P.z) v) * ht.zz
  obtain ⟨h1, h2, h3⟩ := key
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;>
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, hermForm_sub_right, h1, h2, h3, sub_self]

theorem piRest_inW (ht : FrameTab (σ := σ) (J := J) P c T) {v : Fin n → R ⊗[F] E}
    (hv : InW (σ := σ) (J := J) P v) : piRest (σ := σ) (J := J) P c v = 0 := by
  rw [piRest_apply]
  simp [hv.1, hv.2.1, hv.2.2]

theorem piW_inW_eq (ht : FrameTab (σ := σ) (J := J) P c T) {v : Fin n → R ⊗[F] E}
    (hv : InW (σ := σ) (J := J) P v) : piW (σ := σ) (J := J) P c v = v := by
  simp [piW, piRest_inW ht hv]

theorem piRest_e (ht : FrameTab (σ := σ) (J := J) P c T) (b : Fin r) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
  rw [piRest_apply]
  simp [ht.fe, ht.ee, ht.ze]

theorem piRest_f (ht : FrameTab (σ := σ) (J := J) P c T) (b : Fin r) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  rw [piRest_apply]
  simp [ht.ff, ht.ef, ht.zf]

theorem piRest_of_frameTab (ht : FrameTab (σ := σ) (J := J) P c T) :
    piRest (σ := σ) (J := J) P c (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  rw [piRest_apply]
  simp [ht.fz, ht.ez, ht.zz]

theorem piW_X (ht : FrameTab (σ := σ) (J := J) P c T) {x : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) : piW (σ := σ) (J := J) P c x = 0 := by
  have h : spanR (F := F) R P.e Set.univ ≤ LinearMap.ker (piW (σ := σ) (J := J) P c) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨b, -, rfl⟩
    simp [piW, piRest_e ht b]
  exact h hx

theorem inW_left (ht : FrameTab (σ := σ) (J := J) P c T) {a : Fin n → R ⊗[F] E}
    (ha : InW (σ := σ) (J := J) P a) (y : Fin n → R ⊗[F] E) :
    hR R σ J a (piRest (σ := σ) (J := J) P c y) = 0 := by
  have h1 : ∀ i, hR R σ J a (ratV (F := F) R (P.e i)) = 0 := fun i => by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.1 i, map_zero]
  have h2 : ∀ i, hR R σ J a (ratV (F := F) R (P.f i)) = 0 := fun i => by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.2.1 i, map_zero]
  have h3 : hR R σ J a (ratV (F := F) R P.z) = 0 := by
    rw [← hermForm_conj_symm ht.hσ ht.hJ, ha.2.2, map_zero]
  rw [piRest_apply, hermForm_add_right_bis, hermForm_add_right_bis, hermForm_sum_right_alt, hermForm_sum_right_alt,
    hermForm_smul_right_alt]
  simp [h1, h2, h3]

theorem inW_right (ht : FrameTab (σ := σ) (J := J) P c T) {a : Fin n → R ⊗[F] E}
    (ha : InW (σ := σ) (J := J) P a) (y : Fin n → R ⊗[F] E) :
    hR R σ J (piRest (σ := σ) (J := J) P c y) a = 0 := by
  rw [piRest_apply, hR_add_left, hR_add_left, hR_sum_smul_left', hR_sum_smul_left', hR_smul_left]
  simp [ha.1, ha.2.1, ha.2.2]

theorem X_left {x : Fin n → R ⊗[F] E} (hx : x ∈ spanR (F := F) R P.e Set.univ) {a : Fin n → R ⊗[F] E}
    (ha : ∀ b, hR R σ J (ratV (F := F) R (P.e b)) a = 0) : hR R σ J x a = 0 := by
  exact hR_span_perp (R := R) (σ := σ) (J := J) P a ha x hx

end Proj

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Levi

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r} {c : R ⊗[F] E} {T : F}

theorem parabolic_preserves_isotropic {s : HA R σ J} (hs : s ∈ Ssub R σ J P) {x : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) : lin R σ J s x ∈ spanR (F := F) R P.e Set.univ := by
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e x hx
  rw [map_sum]
  refine Submodule.sum_mem _ fun b _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  have h1 := Submodule.span_mono (Set.image_mono (Set.subset_univ _)) (parabolic_unipotent_on_flag P hs b)
  have h2 := Submodule.add_mem _ h1 (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩ :
    ratV (F := F) R (P.e b) ∈ spanR (F := F) R P.e Set.univ)
  rwa [sub_add_cancel] at h2

theorem parabolic_fixes_modulo_span {s : HA R σ J} (hs : s ∈ Ssub R σ J P) :
    lin R σ J s (ratV (F := F) R P.z) - ratV (F := F) R P.z ∈ spanR (F := F) R P.e Set.univ := by
  have h := hs (Fin.last r)
  have e : F0 P (Fin.last r) = P.z := by simp [F0]
  rw [e] at h
  refine (Submodule.span_le.2 ?_) h
  rintro _ ⟨a, ha, rfl⟩
  obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 (Fin.ne_last_of_lt ha)
  show ratV (F := F) R (F0 P (Fin.castSucc a')) ∈ spanR (F := F) R P.e Set.univ
  have e' : F0 P (Fin.castSucc a') = P.e a' := by simp [F0]
  rw [e']
  exact Submodule.subset_span ⟨a', Set.mem_univ _, rfl⟩

theorem isotropic_span_hermForm_zero (ht : FrameTab (σ := σ) (J := J) P c T) {x y : Fin n → R ⊗[F] E}
    (hx : x ∈ spanR (F := F) R P.e Set.univ) (hy : y ∈ spanR (F := F) R P.e Set.univ) : hR R σ J x y = 0 := by
  refine X_left hx fun b => ?_
  obtain ⟨d, rfl⟩ := mem_tensor_span_iff R P.e y hy
  rw [hermForm_sum_right_alt]
  simp [ht.ee]

theorem parabolic_maps_complement (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    {a : Fin n → R ⊗[F] E} (ha : InW (σ := σ) (J := J) P a) :
    piRest (σ := σ) (J := J) P c (lin R σ J s a) ∈ spanR (F := F) R P.e Set.univ := by
  have h1 : ∀ b, hR R σ J (ratV (F := F) R (P.e b)) (lin R σ J s a) = 0 := fun b => by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R (P.e b)), hR_lin]
    exact X_left (parabolic_preserves_isotropic hs' (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)) ha.1
  have h3 : hR R σ J (ratV (F := F) R P.z) (lin R σ J s a) = 0 := by
    rw [← lin_lin_inv R σ J s (ratV (F := F) R P.z), hR_lin]
    have e : lin R σ J s⁻¹ (ratV (F := F) R P.z) =
        ratV (F := F) R P.z + (lin R σ J s⁻¹ (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by abel
    rw [e, hR_add_left, ha.2.2, X_left (parabolic_fixes_modulo_span hs') ha.1, add_zero]
  rw [piRest_apply]
  simp only [h1, h3, zero_smul, Finset.sum_const_zero, add_zero, mul_zero]
  exact Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)

variable (P c)

def Lh (s : HA R σ J) : (Fin n → R ⊗[F] E) →ₗ[R ⊗[F] E] (Fin n → R ⊗[F] E) :=
  piW (σ := σ) (J := J) P c ∘ₗ lin R σ J s ∘ₗ piW (σ := σ) (J := J) P c + piRest (σ := σ) (J := J) P c

variable {P c}

theorem Lh_apply (s : HA R σ J) (v : Fin n → R ⊗[F] E) : Lh P c s v =
    piW (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c v)) + piRest (σ := σ) (J := J) P c v := rfl

theorem piW_piRest (ht : FrameTab (σ := σ) (J := J) P c T) (v : Fin n → R ⊗[F] E) :
    piW (σ := σ) (J := J) P c (piRest (σ := σ) (J := J) P c v) = 0 := by
  have e : piRest (σ := σ) (J := J) P c v = v - piW (σ := σ) (J := J) P c v :=
    eq_sub_of_add_eq' (piW_add_rest (σ := σ) (J := J) P c v)
  rw [e, map_sub, piW_inW_eq ht (piW_inW ht v), sub_self]

theorem Lh_unitary (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs' : s⁻¹ ∈ Ssub R σ J P)
    (u v : Fin n → R ⊗[F] E) : hR R σ J (Lh P c s u) (Lh P c s v) = hR R σ J u v := by
  set pu := piW (σ := σ) (J := J) P c u
  set pv := piW (σ := σ) (J := J) P c v
  have hpu := piW_inW (c := c) ht u
  have hpv := piW_inW (c := c) ht v

  have hmid : hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) =
      hR R σ J pu pv := by
    have eA := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pu)
    have eB := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s pv)
    have hxa := parabolic_maps_complement ht hs' hpu
    have hxb := parabolic_maps_complement ht hs' hpv
    have key : hR R σ J (lin R σ J s pu) (lin R σ J s pv) =
        hR R σ J (piW (σ := σ) (J := J) P c (lin R σ J s pu)) (piW (σ := σ) (J := J) P c (lin R σ J s pv)) := by
      conv_lhs => rw [← eA, ← eB]
      rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis,
        inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _), isotropic_span_hermForm_zero ht hxa hxb]
      ring
    rw [← key, hR_lin]
  rw [Lh_apply, Lh_apply, hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, hmid,
    inW_left ht (piW_inW ht _), inW_right ht (piW_inW ht _)]
  conv_rhs => rw [← piW_add_rest (σ := σ) (J := J) P c u, ← piW_add_rest (σ := σ) (J := J) P c v]
  rw [hR_add_left, hermForm_add_right_bis, hermForm_add_right_bis, inW_left ht hpu, inW_right ht hpv]

theorem Lh_inv (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (v : Fin n → R ⊗[F] E) : Lh P c s (Lh P c s⁻¹ v) = v := by
  set w := piW (σ := σ) (J := J) P c v
  have hw := piW_inW (c := c) ht v
  set p := piW (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
  have hp := piW_inW (c := c) ht (lin R σ J s⁻¹ w)
  have e1 : Lh P c s⁻¹ v = p + piRest (σ := σ) (J := J) P c v := rfl
  have e2 : piW (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = p := by
    rw [map_add, piW_inW_eq ht hp, piW_piRest ht, add_zero]
  have e3 : piRest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v) = piRest (σ := σ) (J := J) P c v := by
    have := piW_add_rest (σ := σ) (J := J) P c (p + piRest (σ := σ) (J := J) P c v)
    rw [e2] at this
    exact add_left_cancel this
  have hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P := by rw [inv_inv]; exact hs
  have hx := parabolic_maps_complement ht hs'' hw
  have e4 : lin R σ J s p = w - lin R σ J s (piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)) := by
    have := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w)
    have e5 : p = lin R σ J s⁻¹ w - piRest (σ := σ) (J := J) P c (lin R σ J s⁻¹ w) :=
      eq_sub_of_add_eq this
    rw [e5, map_sub, lin_lin_inv R σ J s w]
  rw [e1, Lh_apply, e2, e3, e4, map_sub, piW_inW_eq ht hw, piW_X ht (parabolic_preserves_isotropic hs hx), sub_zero]
  exact piW_add_rest (σ := σ) (J := J) P c v

end Levi

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct

section Pack

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {P : Frame E n r} {c : R ⊗[F] E} {T : F}

theorem Lh_fix_e (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) (b : Fin r) :
    Lh P c s (ratV (F := F) R (P.e b)) = ratV (F := F) R (P.e b) := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R (P.e b)) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_e ht b, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_e ht b]

theorem Lh_fix_f (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) (b : Fin r) :
    Lh P c s (ratV (F := F) R (P.f b)) = ratV (F := F) R (P.f b) := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R (P.f b)) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_f ht b, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_f ht b]

theorem levi_fixes_anisotropic (ht : FrameTab (σ := σ) (J := J) P c T) (s : HA R σ J) :
    Lh P c s (ratV (F := F) R P.z) = ratV (F := F) R P.z := by
  have h0 : piW (σ := σ) (J := J) P c (ratV (F := F) R P.z) = 0 := by
    simp only [piW, LinearMap.sub_apply, LinearMap.id_apply, piRest_of_frameTab ht, sub_self]
  simp only [Lh_apply, h0, map_zero, zero_add, piRest_of_frameTab ht]

def gL (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : GL (Fin n) (R ⊗[F] E) where
  val := LinearMap.toMatrix' (Lh P c s)
  inv := LinearMap.toMatrix' (Lh P c s⁻¹)
  val_inv := by
    rw [← LinearMap.toMatrix'_comp]
    have : Lh P c s ∘ₗ Lh P c s⁻¹ = LinearMap.id := LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      exact Lh_inv ht hs hs' v
    rw [this, LinearMap.toMatrix'_id]
  inv_val := by
    rw [← LinearMap.toMatrix'_comp]
    have hs'' : s⁻¹⁻¹ ∈ Ssub R σ J P := by rw [inv_inv]; exact hs
    have : Lh P c s⁻¹ ∘ₗ Lh P c s = LinearMap.id := LinearMap.ext fun v => by
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      have := Lh_inv ht hs' hs'' v
      rwa [inv_inv] at this
    rw [this, LinearMap.toMatrix'_id]

theorem gL_mem (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : gL ht hs hs' ∈ HR R σ J := by
  change Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lh P c s)) * JR R J * LinearMap.toMatrix' (Lh P c s) = JR R J
  have key : ∀ x y, Formalism.UG.hform (sigR R σ)
      (Formalism.UG.cT (sigR R σ) (LinearMap.toMatrix' (Lh P c s)) * JR R J * LinearMap.toMatrix' (Lh P c s)) x y =
      Formalism.UG.hform (sigR R σ) (JR R J) x y := by
    intro x y
    rw [← Formalism.UG.P.hform_mulVec, LinearMap.toMatrix'_mulVec, LinearMap.toMatrix'_mulVec]
    exact Lh_unitary ht hs' x y
  ext i j
  have := key (Pi.single i 1) (Pi.single j 1)
  have hsg : ∀ k, sigR R σ ((Pi.single i (1 : R ⊗[F] E) : Fin n → R ⊗[F] E) k) =
      (Pi.single i (1 : R ⊗[F] E) : Fin n → R ⊗[F] E) k := fun k => by
    by_cases hk : k = i <;> simp [Pi.single_apply, hk]
  simp only [Formalism.UG.hform, hsg] at this
  simpa [Pi.single_apply] using this

def hOf (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : HA R σ J := (⟨gL ht hs hs', gL_mem ht hs hs'⟩ : ↥(HR R σ J))

theorem lin_hOf (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (v : Fin n → R ⊗[F] E) : lin R σ J (hOf ht hs hs') v = Lh P c s v := by
  change Matrix.mulVec (LinearMap.toMatrix' (Lh P c s)) v = _
  exact LinearMap.toMatrix'_mulVec _ _

theorem hOf_mem (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) : hOf ht hs hs' ∈ Hsub R σ J P := by
  rw [Hsub, mem_stabT]
  intro b
  rw [lin_hOf]
  induction b using Fin.addCases with
  | left i =>
    simp only [tupH, Fin.append_left]
    induction i using Fin.lastCases with
    | last => simp only [F0, Fin.snoc_last]; exact levi_fixes_anisotropic ht s
    | cast j => simp only [F0, Fin.snoc_castSucc]; exact Lh_fix_e ht s j
  | right j =>
    simp only [tupH, Fin.append_right]
    exact Lh_fix_f ht s j

theorem levi_diff (ht : FrameTab (σ := σ) (J := J) P c T) {s : HA R σ J} (hs : s ∈ Ssub R σ J P)
    (hs' : s⁻¹ ∈ Ssub R σ J P) (u : Fin n → R ⊗[F] E) (hu : InXperp R σ J P u) :
    lin R σ J s u - Lh P c s u ∈ spanR (F := F) R P.e Set.univ := by
  have hr : piRest (σ := σ) (J := J) P c u = (∑ a, hR R σ J (ratV (F := F) R (P.f a)) u • ratV (F := F) R (P.e a)) +
      (c * hR R σ J (ratV (F := F) R P.z) u) • ratV (F := F) R P.z := by
    rw [piRest_apply]
    simp [hu _]
  set xu := ∑ a, hR R σ J (ratV (F := F) R (P.f a)) u • ratV (F := F) R (P.e a)
  have hxu : xu ∈ spanR (F := F) R P.e Set.univ :=
    Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, Set.mem_univ _, rfl⟩)
  set γ := c * hR R σ J (ratV (F := F) R P.z) u
  have e1 : lin R σ J s u = lin R σ J s (piW (σ := σ) (J := J) P c u) + lin R σ J s (piRest (σ := σ) (J := J) P c u) := by
    rw [← map_add, piW_add_rest]
  have e2 := piW_add_rest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u))
  have e3 : piRest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) =
      lin R σ J s (piW (σ := σ) (J := J) P c u) - piW (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) :=
    eq_sub_of_add_eq' e2
  have key : lin R σ J s u - Lh P c s u =
      piRest (σ := σ) (J := J) P c (lin R σ J s (piW (σ := σ) (J := J) P c u)) + (lin R σ J s xu - xu) +
        γ • (lin R σ J s (ratV (F := F) R P.z) - ratV (F := F) R P.z) := by
    rw [e3, Lh_apply, e1, hr, map_add, map_smul, smul_sub]
    abel
  rw [key]
  exact Submodule.add_mem _ (Submodule.add_mem _ (parabolic_maps_complement ht hs' (piW_inW ht u))
    (Submodule.sub_mem _ (parabolic_preserves_isotropic hs hxu) hxu)) (Submodule.smul_mem _ _ (parabolic_fixes_modulo_span hs))

end Pack

variable {D : D7}

theorem leviComp_holds : LeviComp := by
  intro D X w p s hs
  obtain ⟨hee, hff, hef, hez, hfz, hzz, hT⟩ := FrameW.frameOf_isStd X w
  have hσ : ∀ x, X.B.I.cm.sig (X.B.I.cm.sig x) = x := fun x => by simp [FrameW.sig_apply]
  have hJ : ∀ i j, X.B.I.cm.sig (X.B.I.J j i) = X.B.I.J i j := (cmInst_holds X).2.1
  set T : X.B.I.F := (((D.mem w).A.T : ℕ) : X.B.I.F)
  have hne : algebraMap X.B.I.F X.B.I.E (-T) ≠ 0 := by
    rw [map_neg, neg_ne_zero]
    exact fun h => hT ((algebraMap X.B.I.F X.B.I.E).injective (by rw [h, map_zero]))
  set c : Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E :=
    inclR (F := X.B.I.F) (Fv X.B.I.F p.1) ((algebraMap X.B.I.F X.B.I.E (-T))⁻¹)
  have ht : FrameTab (σ := X.B.I.cm.sig) (J := X.B.I.J) (frameOf X w) c T :=
    { ee := fun a b => by rw [hermForm_rational_vectors, hee, map_zero]
      ef := fun a b => by rw [hermForm_rational_vectors, hef]; split_ifs <;> simp
      fe := fun a b => by
        rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hef b a]
        split_ifs with h1 h2 h2 <;> simp_all
      ff := fun a b => by rw [hermForm_rational_vectors, hff, map_zero]
      ez := fun a => by rw [hermForm_rational_vectors, hez, map_zero]
      fz := fun a => by rw [hermForm_rational_vectors, hfz, map_zero]
      ze := fun a => by rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hez, map_zero, map_zero]
      zf := fun a => by rw [hermForm_rational_vectors, ← hermForm_base_conj_symm hσ hJ, hfz, map_zero, map_zero]
      zz := by rw [hermForm_rational_vectors, hzz, ← map_mul, inv_mul_cancel₀ hne, map_one]
      hσ := hσ
      hJ := hJ }
  have hs' := inv_mem hs
  exact ⟨hOf ht hs hs', hOf_mem ht hs hs', fun u hu => by rw [lin_hOf]; exact levi_diff ht hs hs' u hu⟩

theorem locLevi_of_NO (hN : UnipotentIntegralInLevel) : LocLevi := locLevi_of_comp leviComp_holds hN

end MassDataLevelSSteps
end
end

section
noncomputable section

namespace MassDataLevelSSteps

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.TypedSets MeasureTheory NumberField
  IsDedekindDomain Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
open scoped TensorProduct
open Matrix

section Lift

variable (I : Formalism.MainNotions.S.AutInst)

def liftS (p : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) : I.E ⊗[I.F] Af I.F :=
  (Algebra.TensorProduct.comm I.F I.E (Af I.F)).symm (PI.MassDataKppVolLemmas.thetaP I p c)

theorem psiV_liftS (p v : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I v (liftS I p c) = PI.MassDataKppVolLemmas.tV I v (PI.MassDataKppVolLemmas.thetaP I p c) := by
  unfold liftS PI.FinKW.psiV
  rw [AlgHom.comp_apply]
  erw [AlgEquiv.apply_symm_apply]
  rfl

theorem psiV_liftS_same (p : HeightOneSpectrum (𝓞 I.F)) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I p (liftS I p c) = c := by
  rw [psiV_liftS]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp only [PI.MassDataKppVolLemmas.thetaP, TensorProduct.map_tmul, LinearMap.id_apply, PI.MassDataKppVolLemmas.tV]
    simp [PI.MassDataKppVolLemmas.sL, tensMap]
    rw [show evalV I.F p (singleV I.F p a) = a from PI.MassDataKppVolLemmas.Comp_single_same I p a]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem psiV_liftS_ne (p v : HeightOneSpectrum (𝓞 I.F)) (h : v ≠ p) (c : Fv I.F p ⊗[I.F] I.E) :
    PI.FinKW.psiV I v (liftS I p c) = 0 := by
  rw [psiV_liftS]
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a e =>
    simp [PI.MassDataKppVolLemmas.thetaP, PI.MassDataKppVolLemmas.tV, PI.MassDataKppVolLemmas.sL, tensMap]
    rw [show evalV I.F v (singleV I.F p a) = 0 from PI.MassDataKppVolLemmas.Comp_single_ne I p v h a,
      TensorProduct.zero_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, add_zero]

theorem vecV_incl (v : HeightOneSpectrum (𝓞 I.F)) (x : Fin I.n → I.E) :
    PI.FinKW.vecV I v (incl I x) = ratV (F := I.F) (Fv I.F v) x := by
  funext i
  simp [PI.FinKW.vecV, incl, ratV, PI.FinKW.psiV, Formalism.UG.inclE, inclR]

theorem vecV_add (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.vecV I v (x + y) = PI.FinKW.vecV I v x + PI.FinKW.vecV I v y := by
  funext i
  exact map_add (PI.FinKW.psiV I v) (x i) (y i)

theorem vecV_smul (v : HeightOneSpectrum (𝓞 I.F)) (c : I.E ⊗[I.F] Af I.F) (x : VA I) :
    PI.FinKW.vecV I v (c • x) = PI.FinKW.psiV I v c • PI.FinKW.vecV I v x := by
  funext i
  exact map_mul (PI.FinKW.psiV I v) c (x i)

theorem vecV_zero (v : HeightOneSpectrum (𝓞 I.F)) : PI.FinKW.vecV I v (0 : VA I) = 0 := by
  funext i
  exact map_zero (PI.FinKW.psiV I v)

theorem span_lift (p : HeightOneSpectrum (𝓞 I.F)) {m : ℕ} (Y : Fin m → Fin I.n → I.E) (s : Set (Fin m))
    (u : Fin I.n → Fv I.F p ⊗[I.F] I.E) (hu : u ∈ spanR (F := I.F) (Fv I.F p) Y s) :
    ∃ U : VA I, U ∈ Submodule.span (I.E ⊗[I.F] Af I.F) ((fun a => incl I (Y a)) '' s) ∧
      PI.FinKW.vecV I p U = u ∧ ∀ v, v ≠ p → PI.FinKW.vecV I v U = 0 := by
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    refine ⟨liftS I p 1 • incl I (Y a), Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, ha, rfl⟩), ?_, ?_⟩
    · rw [vecV_smul, psiV_liftS_same, one_smul, vecV_incl]
    · intro v hv
      rw [vecV_smul, psiV_liftS_ne I p v hv, zero_smul]
  | zero => exact ⟨0, Submodule.zero_mem _, vecV_zero I p, fun v _ => vecV_zero I v⟩
  | add x y _ _ hx hy =>
    obtain ⟨U, hU, h1, h2⟩ := hx
    obtain ⟨U', hU', h1', h2'⟩ := hy
    refine ⟨U + U', Submodule.add_mem _ hU hU', ?_, fun v hv => ?_⟩
    · rw [vecV_add, h1, h1']
    · rw [vecV_add, h2 v hv, h2' v hv, add_zero]
  | smul c x _ hx =>
    obtain ⟨U, hU, h1, h2⟩ := hx
    refine ⟨liftS I p c • U, Submodule.smul_mem _ _ hU, ?_, fun v hv => ?_⟩
    · rw [vecV_smul, psiV_liftS_same, h1]
    · rw [vecV_smul, h2 v hv, smul_zero]

theorem mulVec_mem_span (p : HeightOneSpectrum (𝓞 I.F)) (M : Matrix (Fin I.n) (Fin I.n) (I.E ⊗[I.F] Af I.F))
    (hM : ∀ v, v ≠ p → M.map (PI.FinKW.psiV I v) = 0) {m : ℕ} (Y : Fin m → Fin I.n → I.E) (s : Set (Fin m))
    (w : VA I)
    (h : (M.map (PI.FinKW.psiV I p)) *ᵥ PI.FinKW.vecV I p w ∈ spanR (F := I.F) (Fv I.F p) Y s) :
    M *ᵥ w ∈ Submodule.span (I.E ⊗[I.F] Af I.F) ((fun a => incl I (Y a)) '' s) := by
  obtain ⟨U, hU, h1, h2⟩ := span_lift I p Y s _ h
  have e : M *ᵥ w = U := by
    funext i
    rw [← sub_eq_zero]
    apply PI.FinKW.local_vector_injective I
    intro v
    rw [map_sub]
    have e1 : PI.FinKW.psiV I v ((M *ᵥ w) i) = ((M.map (PI.FinKW.psiV I v)) *ᵥ PI.FinKW.vecV I v w) i :=
      congrFun (PI.MassDataKppVolLemmas.LocIdxLift_vecV_mulVec I v M w) i
    have e2 : PI.FinKW.psiV I v (U i) = PI.FinKW.vecV I v U i := rfl
    rw [e1, e2]
    by_cases hv : v = p
    · subst hv
      rw [h1, sub_self]
    · rw [hM v hv, h2 v hv, Matrix.zero_mulVec]
      simp
  rw [e]
  exact hU

theorem psiV_sigR (v : HeightOneSpectrum (𝓞 I.F)) (t : I.E ⊗[I.F] Af I.F) :
    PI.FinKW.psiV I v (Formalism.UG.sigR I.cm.sig (Af I.F) t) = sigR (Fv I.F v) I.cm.sig (PI.FinKW.psiV I v t) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [PI.FinKW.psiV, Formalism.UG.sigR, sigR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem psiV_inclE (v : HeightOneSpectrum (𝓞 I.F)) (a : I.E) :
    PI.FinKW.psiV I v (Formalism.UG.inclE (F := I.F) (Af I.F) a) = inclR (Fv I.F v) a := by
  simp [PI.FinKW.psiV, Formalism.UG.inclE, inclR]

theorem psiV_hA (v : HeightOneSpectrum (𝓞 I.F)) (x y : VA I) :
    PI.FinKW.psiV I v (hA I x y) =
      hR (Fv I.F v) I.cm.sig I.J (PI.FinKW.vecV I v x) (PI.FinKW.vecV I v y) := by
  simp [hA, hR, Formalism.UG.hform, JR, PI.FinKW.vecV, map_sum, map_mul, psiV_sigR, psiV_inclE, dotProduct,
    mulVec, Matrix.map_apply]

end Lift

theorem unipotent_integral_in_level : UnipotentIntegralInLevel := by
  intro D X hb hK hT hL w p n hn hnK
  obtain ⟨hn1, hn2⟩ := hn
  obtain ⟨y, hy⟩ := PI.MassDataKppVolLemmas.Bridge_tf_surjective X.B.I hb
    (PI.MassDataKppVolLemmas.liftHA X.B.I p.1 n)
  have hcomp : ∀ v, v ≠ p.1 → PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y) = 1 :=
    fun v h => by rw [hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_ne X.B.I p.1 v h]
  have hsame : PI.MassDataKppVolLemmas.piV X.B.I p.1 (PI.MassDataKppVolLemmas.tf X.B.I hb y) = n := by
    rw [hy, PI.MassDataKppVolLemmas.LocIdxLift_piV_same]

  have hyK : y ∈ X.B.I.Kset := by
    rw [← PI.MassDataKppVolLemmas.Bridge_mem_Kf_iff X.B.I hb, Kf, Subgroup.mem_iInf]
    intro v
    show HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
      (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) ∈
        Kloc v (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))
    by_cases h : v = p.1
    · subst h; rw [hsame]; exact hnK
    · rw [hcomp v h]; exact (Kloc v _).one_mem

  have hmat : ∀ v, (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) =
      ((HA.mat (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J
        (PI.MassDataKppVolLemmas.piV X.B.I v (PI.MassDataKppVolLemmas.tf X.B.I hb y)) :
          GL (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) -
        1 : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E)) := by
    intro v
    rw [Matrix.map_sub _ (map_sub _), PI.MassDataKppVolLemmas.LocIdxLift_psiV_fmat X.B.I hb,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hM0 : ∀ v, v ≠ p.1 → (X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I v) = 0 := by
    intro v hv
    rw [hmat v, hcomp v hv]
    exact sub_self _
  have hMp : ∀ x : Fin X.B.I.n → Fv X.B.I.F p.1 ⊗[X.B.I.F] X.B.I.E,
      ((X.B.I.fmat y - 1).map (PI.FinKW.psiV X.B.I p.1)) *ᵥ x = lin (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J n x - x := by
    intro x
    rw [hmat p.1, hsame, Matrix.sub_mulVec, Matrix.one_mulVec]
    rfl
  have hstd := FrameW.frameOf_isStd X w

  have hyN : y ∈ X.NfinU w := by
    refine ⟨fun a => ?_, ?_, fun y' hy' => ?_⟩
    · refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp, vecV_incl]
      exact hn1 a
    · rw [← Set.image_univ]
      refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp, vecV_incl]
      refine hn2 _ (fun a => ?_)
      rw [hermForm_rational_vectors]
      have h0 : hE X.B.I.cm.sig X.B.I.J ((frameOf X w).e a) (X.zR w) = 0 := hstd.2.2.2.1 a
      rw [h0, map_zero]
    · rw [← Set.image_univ]
      refine mulVec_mem_span X.B.I p.1 _ hM0 X.eR _ _ ?_
      rw [hMp]
      refine hn2 _ (fun a => ?_)
      show hR (Fv X.B.I.F p.1) X.B.I.cm.sig X.B.I.J (ratV (F := X.B.I.F) (Fv X.B.I.F p.1) (X.eR a))
        (PI.FinKW.vecV X.B.I p.1 y') = 0
      rw [← vecV_incl, ← psiV_hA, hy' a, map_zero]
  have hN := MassDataMassesW.NLev.nLevel_holds X w y hyN hyK
  refine ⟨finHA X hb y, ⟨finHA X hb ((X.xu w)⁻¹ * y * X.xu w), ⟨_, hN, rfl⟩, ?_⟩, hsame⟩
  show finHA X hb (X.xu w) * finHA X hb ((X.xu w)⁻¹ * y * X.xu w) * (finHA X hb (X.xu w))⁻¹ = finHA X hb y
  rw [finHA_mul, finHA_mul, finHA_inv]
  group

theorem locLevi_holds : LocLevi := locLevi_of_NO unipotent_integral_in_level

end MassDataLevelSSteps
end
end
