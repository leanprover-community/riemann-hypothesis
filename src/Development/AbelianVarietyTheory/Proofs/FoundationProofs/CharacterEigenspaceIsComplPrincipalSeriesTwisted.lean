import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.OrderedConst
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CharacterAverageTwistedSpanEqZero

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem avg_eig : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V,
    ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  intro G V _ _ _ _ _ π hπ H θ hD w
  classical
  let Hs : Subgroup G :=
    { carrier := H
      mul_mem' := fun {a b} ha hb => hD.mul a ha b hb
      one_mem' := hD.one
      inv_mem' := fun {a} ha => hD.inv a ha }
  have hθinv : ∀ a ∈ H, θ a⁻¹ * θ a = 1 := fun a ha => by
    rw [← hD.val_mul _ (hD.inv a ha) _ ha, inv_mul_cancel, hD.val_one]
  have hθ0 : ∀ a ∈ H, θ a ≠ 0 := fun a ha h0 => by
    have := hθinv a ha; rw [h0, mul_zero] at this; exact zero_ne_one this
  have hπmul : ∀ a b : G, π (a * b) w = π a (π b w) := fun a b => by rw [map_mul]; rfl
  let T : Subgroup Hs :=
    { carrier := {j | π j w = θ j • w}
      one_mem' := by simp [hD.val_one]
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq, Subgroup.coe_mul] at ha hb ⊢
        rw [hπmul, hb, map_smul, ha, smul_smul, hD.val_mul _ a.2 _ b.2, mul_comm]
      inv_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq, InvMemClass.coe_inv] at ha ⊢
        have h1 : w = θ a • π (a : G)⁻¹ w := by
          rw [← map_smul, ← ha, ← hπmul, inv_mul_cancel, map_one]; rfl
        have h2 : θ (a : G)⁻¹ = (θ a)⁻¹ := eq_inv_of_mul_eq_one_left (hθinv a a.2)
        rw [h2]
        conv_rhs => rw [h1]
        rw [smul_smul, inv_mul_cancel₀ (hθ0 a a.2), one_smul] }
  haveI : CompactSpace Hs := isCompact_iff_compactSpace.mp hD.compact
  have hopen : IsOpen (T : Set Hs) := by
    apply Subgroup.isOpen_of_mem_nhds T (g := 1)
    rw [nhds_subtype_eq_comap, Filter.mem_comap]
    obtain ⟨U, hU, hUθ⟩ := hD.near
    refine ⟨U ∩ {g | π g w = w}, Filter.inter_mem hU ((hπ w).mem_nhds (by simp)), ?_⟩
    rintro j ⟨hjU, hjw⟩
    show π j w = θ j • w
    rw [hjw, hUθ _ hjU j.2, one_smul]
  haveI : Finite (Hs ⧸ T) := Subgroup.quotient_finite_of_isOpen T hopen
  haveI : Fintype (Hs ⧸ T) := Fintype.ofFinite _
  let f : Hs → V := fun j => (θ j)⁻¹ • π j w
  have hf : ∀ a b : Hs, (a : Hs ⧸ T) = b → f a = f b := by
    intro a b hab
    rw [QuotientGroup.eq] at hab
    have hb : b = a * (a⁻¹ * b) := by group
    generalize a⁻¹ * b = s at hab hb
    subst hb
    have hs : π s w = θ s • w := hab
    simp only [f, Subgroup.coe_mul]
    rw [hπmul, hs, map_smul, smul_smul, hD.val_mul _ a.2 _ s.2, mul_inv, mul_assoc,
      inv_mul_cancel₀ (hθ0 s s.2), mul_one]
  have hact : ∀ h a : Hs, π h (f a) = θ h • f (h * a) := by
    intro h a
    simp only [f, Subgroup.coe_mul]
    rw [map_smul, hπmul, smul_smul, hD.val_mul _ h.2 _ a.2, mul_inv, ← mul_assoc,
      mul_inv_cancel₀ (hθ0 h h.2), one_mul]
  let rep : Hs ⧸ T → Hs := fun q => if q = ((1 : Hs) : Hs ⧸ T) then 1 else q.out
  have hrep : ∀ q, ((rep q : Hs) : Hs ⧸ T) = q := by
    intro q
    simp only [rep]
    split_ifs with hq
    · exact hq.symm
    · exact QuotientGroup.out_eq' q
  have hsum : ∀ h : Hs, π h (∑ q, f (rep q)) = θ h • ∑ q, f (rep q) := by
    intro h
    rw [map_sum, Finset.smul_sum]
    simp_rw [hact]
    have : ∀ q, f (h * rep q) = f (rep (h • q)) := fun q => by
      apply hf
      rw [hrep (h • q)]
      conv_rhs => rw [← hrep q]
      rw [MulAction.Quotient.smul_mk, smul_eq_mul]
    simp_rw [this]
    exact Equiv.sum_comp (MulAction.toPerm h) (fun q => θ h • f (rep q))
  refine ⟨Finset.univ.image (fun q => ((rep q : Hs) : G)), ?_, ?_, ?_⟩
  · refine Finset.mem_image.mpr ⟨((1 : Hs) : Hs ⧸ T), Finset.mem_univ _, ?_⟩
    simp [rep]
  · intro j hj
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.mp hj
    exact (rep q).2
  · have hinj : Set.InjOn (fun q => ((rep q : Hs) : G)) (Finset.univ : Finset (Hs ⧸ T)) := by
      intro q₁ _ q₂ _ h
      rw [← hrep q₁, ← hrep q₂, Subtype.ext h]
    rw [Finset.sum_image hinj]
    intro h hh
    exact hsum ⟨h, hh⟩

end GlobalTheory.PsType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → ∀ w : V, ∃ R : Finset G, (1 : G) ∈ R ∧ (∀ j ∈ R, j ∈ H) ∧ IsEig π H θ (∑ j ∈ R, (θ j)⁻¹ • π j w) := by
  atlas_forward_decl GlobalTheory.PsType.avg_eig
end

section
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType

namespace GlobalTheory.PsType

theorem Datum.theta_ne_zero_of_mem {G : Type} [Group G] [TopologicalSpace G] {H : Set G} {θ : G → ℂ}
    (hD : Datum H θ) {j : G} (hj : j ∈ H) : θ j ≠ 0 := by
  intro h0
  have h := hD.val_mul j hj j⁻¹ (hD.inv j hj)
  rw [mul_inv_cancel, hD.val_one, h0, zero_mul] at h
  exact one_ne_zero h

theorem eig_compl_aug : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ →
    (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  intro G V _ _ _ _ _ π hπ H θ hD
  refine ⟨fun u hu he => ?_, fun w => ?_⟩
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.character_average_twistedSpan_eq_zero G V π hπ H θ hD u hu
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    have hsum : ∑ j ∈ R, (θ j)⁻¹ • π j u = (R.card : ℂ) • u := by
      rw [Finset.sum_congr rfl (g := fun _ => u), Finset.sum_const, Nat.cast_smul_eq_nsmul]
      intro j hj
      rw [he j (hRH j hj), smul_smul, inv_mul_cancel₀ (hD.theta_ne_zero_of_mem (hRH j hj)), one_smul]
    rw [hsum] at hs
    exact (smul_eq_zero.mp hs).resolve_left hc
  · obtain ⟨R, hR1, hRH, hs⟩ := GlobalTheory.T.exists_character_average_eigenvector_compact_subgroup G V π hπ H θ hD w
    have hc : (R.card : ℂ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr ⟨1, hR1⟩).ne'
    refine ⟨(R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w, ?_, ?_⟩
    · intro h hh
      rw [(π h).map_smul, hs h hh]
      exact smul_comm _ _ _
    · have e : w - (R.card : ℂ)⁻¹ • ∑ j ∈ R, (θ j)⁻¹ • π j w
          = (R.card : ℂ)⁻¹ • ∑ j ∈ R, (w - (θ j)⁻¹ • π j w) := by
        rw [Finset.sum_sub_distrib, Finset.sum_const, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
          inv_mul_cancel₀ hc, one_smul]
      rw [e]
      refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j hj => ?_)
      have hθ := hD.theta_ne_zero_of_mem (hRH j hj)
      have e2 : w - (θ j)⁻¹ • π j w = -(θ j)⁻¹ • (π j w - θ j • w) := by
        rw [neg_smul, smul_sub, smul_smul, inv_mul_cancel₀ hθ, one_smul, neg_sub]
      rw [e2]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hRH j hj, w, rfl⟩)

end GlobalTheory.PsType
end

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterEigenspace_isCompl_principalSeriesTwistedSpan : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V), IsSmooth π → ∀ (H : Set G) (θ : G → ℂ), Datum H θ → (∀ u ∈ aug π H θ, IsEig π H θ u → u = 0) ∧ ∀ w : V, ∃ w' : V, IsEig π H θ w' ∧ w - w' ∈ aug π H θ := by
  atlas_forward_decl GlobalTheory.PsType.eig_compl_aug
end
