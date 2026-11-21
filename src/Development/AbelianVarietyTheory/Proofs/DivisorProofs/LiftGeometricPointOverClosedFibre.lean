import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointRangeEqFixedGroupImage
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackIsoBaseChangeOverReducedClosedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedSpecialFibreGlobalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppTopBijectiveAndSurjectiveNormalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppBijectiveOfFlatBaseChangeGlobalFunctions
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZariskiConnectednessIsPreconnectedFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentOfClopen

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem fieldPoint_lift_of_isPreimmersion {X' X : Scheme.{0}} (j : X' ⟶ X) [IsPreimmersion j] {K : Type} [Field K]
    (y : Sp K ⟶ X) (ξ : X') (h : y (IsLocalRing.closedPoint K) = j ξ) : ∃ z : Sp K ⟶ X', z ≫ j = y := by
  obtain ⟨⟨p, φ⟩, hy⟩ := (Scheme.SpecToEquivOfField K X).symm.surjective y
  have hp : p = j ξ := by
    rw [← h, ← hy]
    exact (X.fromSpecResidueField_apply p _).symm
  subst hp
  have : IsIso (j.residueFieldMap ξ) := by
    refine (ConcreteCategory.isIso_iff_bijective _).2 ⟨(j.residueFieldMap ξ).hom.injective, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := X'.residue_surjective ξ a
    obtain ⟨b, rfl⟩ := j.stalkMap_surjective ξ a
    exact ⟨X.residue _ b, congr($(Scheme.residue_residueFieldMap j ξ).hom b)⟩
  refine ⟨Spec.map (inv (j.residueFieldMap ξ) ≫ φ) ≫ X'.fromSpecResidueField ξ, ?_⟩
  rw [← hy, Scheme.SpecToEquivOfField_symm_apply, Category.assoc,
    ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp,
    IsIso.hom_inv_id_assoc]

theorem Emb.exists_lift_fieldExt (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S)
    [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S)
    (hν : ν ≫ PSpace.str R E.N = s ≫ π)
    (hg : ∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) :
    ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme),
      q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  obtain ⟨g, hg, w, hw⟩ := hg
  obtain ⟨y, hy⟩ := (Emb.range_closed R S π G' E).1 g hg
  have hsub : ∀ a b : Sp Ω, a = b := fun a b => Subsingleton.elim (α := PrimeSpectrum Ω) a b
  have hx : ∀ v, (s ≫ π) v = closedPoint R := by
    intro v
    rw [hsub v w, ← hν, Scheme.Hom.comp_apply, hw, ← Scheme.Hom.comp_apply, E.f_over]
    simpa only [Scheme.Hom.comp_apply] using hg
  obtain ⟨κ, hκ⟩ := spMap_factor_residueField_of_closedPoint R Ω (s ≫ π) hx
  have := E.imm
  obtain ⟨y₀, hy₀⟩ := fieldPoint_lift_of_isPreimmersion E.j ν y (by rw [hsub (closedPoint Ω) w, hw, hy])
  have hcl : IsClosedImmersion (spMap (residue R)) :=
    IsClosedImmersion.spec_of_surjective _ (residue_surjective (R := R))
  have hY : y₀ ≫ E.Y.hom = spMap κ := by
    rw [← cancel_mono (spMap (residue R)), Category.assoc, ← E.j_over, ← Category.assoc, hy₀, hν, hκ,
      ← Spec.map_comp]
    rfl
  obtain ⟨Ω', _, io, e, l, -, hl1, hl2⟩ := E.fib Ω s κ hκ
  let t : Sp Ω' ⟶ pullback E.Y.hom (spMap (io.comp κ)) :=
    pullback.lift (spMap io ≫ y₀) (𝟙 _) (by rw [Category.assoc, hY, Category.id_comp, ← Spec.map_comp]; rfl)
  have h1 : t ≫ pullback.fst _ _ = spMap io ≫ y₀ := pullback.lift_fst _ _ _
  have h2 : t ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
  have he : e.inv.left ≫ e.hom.left = 𝟙 _ := by rw [← Over.comp_left, e.inv_hom_id]; rfl
  have hw' : e.inv.left ≫ pullback.snd G'.hom (spMap io ≫ s) = pullback.snd E.Y.hom (spMap (io.comp κ)) :=
    Over.w e.inv
  refine ⟨Ω', inferInstance, io, t ≫ e.inv.left ≫ l, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, hl2, ← Category.assoc e.inv.left, he, ← hy₀, ← Category.assoc (spMap io), ← h1]
    simp
  · rw [Category.assoc, Category.assoc, ← Category.assoc l, hl1]
    erw [pullback.condition, ← Category.assoc e.inv.left, hw', ← Category.assoc, h2, Category.id_comp]

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_after_field_extension : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S : Scheme.{0}) (π : S ⟶ Sp R) (G' : Over S) [GrpObj G'] (E : Emb π G') (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ PSpace R E.N) (s : Sp Ω ⟶ S), ν ≫ PSpace.str R E.N = s ≫ π → (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ∃ (Ω' : Type) (_ : Field Ω') (io : Ω →+* Ω') (q : Sp Ω' ⟶ E.H.toScheme), q ≫ E.f = spMap io ≫ ν ∧ q ≫ E.H.ι ≫ G'.hom = spMap io ≫ s := by
  atlas_forward_decl GlobalTheory.Mum.Emb.exists_lift_fieldExt
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_pt_of_pt_ext : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν →
    ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  intro H Q φ hφ Ω _ _ ν Ω' _ io q hq
  have : JacobsonSpace ↥(pullback φ ν) := LocallyOfFiniteType.jacobsonSpace (pullback.snd φ ν)
  have hne : (Set.univ : Set ↥(pullback φ ν)).Nonempty :=
    ⟨pullback.lift q (spMap io) hq (IsLocalRing.closedPoint Ω'), trivial⟩
  obtain ⟨c, -, hc⟩ := nonempty_inter_closedPoints hne isOpen_univ.isLocallyClosed
  have hc' : IsClosed ({c} : Set ↥(pullback φ ν)) := hc
  refine ⟨pointOfClosedPoint (pullback.snd φ ν) c hc' ≫ pullback.fst φ ν, ?_⟩
  rw [Category.assoc, pullback.condition, ← Category.assoc, pointOfClosedPoint_comp, Category.id_comp]

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_point_of_point_over_field_extension : ∀ (H Q : Scheme.{0}) (φ : H ⟶ Q), LocallyOfFiniteType φ → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (Ω' : Type) [Field Ω'] (io : Ω →+* Ω') (q : Sp Ω' ⟶ H), q ≫ φ = spMap io ≫ ν → ∃ p : Sp Ω ⟶ H, p ≫ φ = ν := by
  atlas_forward_decl GlobalTheory.Mum.exists_pt_of_pt_ext
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem section_eq_of_apply_eq {k : Type} [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) (q q' : Sp k ⟶ X)
    (hq : q ≫ p = 𝟙 _) (hq' : q' ≫ p = 𝟙 _) (h : q (closedPoint k) = q' (closedPoint k)) : q = q' := by
  obtain ⟨⟨y, a⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q
  obtain ⟨⟨y', a'⟩, rfl⟩ := (Scheme.SpecToEquivOfField k X).symm.surjective q'
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hq hq' h ⊢
  obtain rfl : y = y' := by
    have k₁ : ∀ (y : X) (p : Spec (X.residueField y)), X.fromSpecResidueField y p = y := fun y p =>
      Set.mem_singleton_iff.1 (X.range_fromSpecResidueField y ▸ Set.mem_range_self p)
    exact (k₁ y _).symm.trans (h.trans (k₁ y' _))
  obtain ⟨c, hc⟩ := Spec.map_surjective (X.fromSpecResidueField y ≫ p)
  have key : ∀ b : X.residueField y ⟶ CommRingCat.of k, (Spec.map b ≫ X.fromSpecResidueField y) ≫ p = 𝟙 _ →
      ∀ o, b.hom (c.hom o) = o := fun b hb o => by
    rw [Category.assoc, ← hc, ← Spec.map_comp] at hb
    have := Spec.map_injective (hb.trans (Spec.map_id _).symm)
    simpa using RingHom.congr_fun (congrArg CommRingCat.Hom.hom this) o
  obtain rfl : a = a' := by
    ext u
    have hu : c.hom (a.hom u) = u := a.hom.injective (key a hq _)
    rw [← hu, key a hq, key a' hq']
  rfl

theorem eq_of_comp_eq_of_connectedSpace_pullback : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  intro P Q b hb Ω _ _ ν ξ₁ ξ₂ h₁ h₂ hc
  haveI := hb
  have hsub : ∀ x y : (pullback b ν : Scheme.{0}), x = y := by
    intro x y
    have hopen : ∀ z : (pullback b ν : Scheme.{0}), IsOpen ({z} : Set (pullback b ν : Scheme.{0})) := by
      intro z
      have hd := (pullback.snd b ν).isDiscrete_preimage_singleton (pullback.snd b ν z)
      obtain ⟨U, hU, hUz⟩ := isDiscrete_iff_forall_exists_isOpen.mp hd z rfl
      have hU' : U ∩ (pullback.snd b ν) ⁻¹' {pullback.snd b ν z} = U :=
        Set.inter_eq_left.mpr fun w _ => Subsingleton.elim _ _
      rw [hU'] at hUz
      exact hUz ▸ hU
    have hcl : IsClopen ({x} : Set (pullback b ν : Scheme.{0})) := by
      refine ⟨?_, hopen x⟩
      rw [← isOpen_compl_iff, ← Set.biUnion_of_singleton ({x}ᶜ : Set (pullback b ν : Scheme.{0}))]
      exact isOpen_biUnion fun z _ => hopen z
    rcases isClopen_iff.mp hcl with h | h
    · exact absurd h (Set.singleton_ne_empty x)
    · have : y ∈ ({x} : Set (pullback b ν : Scheme.{0})) := h ▸ Set.mem_univ y
      exact (Set.mem_singleton_iff.mp this).symm
  have e₁ : ξ₁ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₁, Category.id_comp]
  have e₂ : ξ₂ ≫ b = 𝟙 (Sp Ω) ≫ ν := by rw [h₂, Category.id_comp]
  have hσ := section_eq_of_apply_eq (pullback.snd b ν) (pullback.lift ξ₁ (𝟙 _) e₁) (pullback.lift ξ₂ (𝟙 _) e₂)
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) (hsub _ _)
  have := congrArg (fun σ => σ ≫ pullback.fst b ν) hσ
  simp only [pullback.lift_fst] at this
  exact this

end GlobalTheory.Mum
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' : ∀ (P Q : Scheme.{0}) (b : P ⟶ Q), LocallyQuasiFinite b → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ Q) (ξ₁ ξ₂ : Sp Ω ⟶ P), ξ₁ ≫ b = ν → ξ₂ ≫ b = ν → ConnectedSpace (pullback b ν : Scheme.{0}) → ξ₁ = ξ₂ := by
  atlas_forward_decl GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem connectedSpace_pullback_of_comp_surjective (X P Q Z : Scheme.{0}) (a : X ⟶ P)
    (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q) (hg : a ≫ b = g) (ha : Surjective a)
    (hc : ConnectedSpace (pullback g ν : Scheme.{0})) :
    ConnectedSpace (pullback b ν : Scheme.{0}) := by
  subst hg
  let f : pullback (a ≫ b) ν ⟶ pullback b ν :=
    (pullbackRightPullbackFstIso b ν a).inv ≫ pullback.snd a (pullback.fst b ν)
  have hf : Surjective f := inferInstance
  exact Function.Surjective.connectedSpace hf.surj f.base.hom.continuous

end GlobalTheory
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective : ∀ (X P Q Z : Scheme.{0}) (a : X ⟶ P) (b : P ⟶ Q) (g : X ⟶ Q) (ν : Z ⟶ Q), a ≫ b = g → Surjective a → ConnectedSpace (pullback g ν : Scheme.{0}) → ConnectedSpace (pullback b ν : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.connectedSpace_pullback_of_comp_surjective
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem geomFibre_restrict_open_connected : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  intro H Q Z U f ν hU hc
  have hs : IsIso (pullback.snd U.ι (pullback.fst f ν)) := by
    refine isIso_of_isOpenImmersion_of_opensRange_eq_top _ ?_
    rw [Scheme.Hom.opensRange_pullbackSnd]
    refine top_unique fun z _ => ?_
    show pullback.fst f ν z ∈ U.ι.opensRange
    rw [Scheme.Opens.opensRange_ι]
    refine hU _ ⟨pullback.snd f ν z, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.condition]
  let e := Scheme.homeoOfIso ((pullbackRightPullbackFstIso f ν U.ι).symm ≪≫
    asIso (pullback.snd U.ι (pullback.fst f ν)))
  exact e.connectedSpace_iff.2 hc

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_pullback_restrict_open_containing_fibre : ∀ (H Q Z : Scheme.{0}) (U : H.Opens) (f : H ⟶ Q) (ν : Z ⟶ Q), (∀ h : H, f h ∈ Set.range ν → h ∈ U) → ConnectedSpace (pullback f ν : Scheme.{0}) → ConnectedSpace (pullback (U.ι ≫ f) ν : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.Mum.geomFibre_restrict_open_connected
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibConn

theorem lfac {X P : Scheme.{0}} (j : X ⟶ P) [IsImmersion j] (Ω : Type) [Field Ω] (ν : Sp Ω ⟶ P)
    (h : Set.range ν ⊆ Set.range j) : ∃ y₀ : Sp Ω ⟶ X, y₀ ≫ j = ν := by
  have h1 : Set.range ν ⊆ Set.range j.coborderRange.ι := by
    refine h.trans ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨j.liftCoborder x, by rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι]⟩
  let ν' := IsOpenImmersion.lift j.coborderRange.ι ν h1
  have hν' : ν' ≫ j.coborderRange.ι = ν := IsOpenImmersion.lift_fac _ _ _
  have h2 : Set.range ν' ⊆ Set.range j.liftCoborder := by
    rintro _ ⟨q, rfl⟩
    obtain ⟨x, hx⟩ := h ⟨q, rfl⟩
    refine ⟨x, j.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, Scheme.Hom.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hν']
  haveI : Surjective (pullback.snd j.liftCoborder ν') := ⟨by
    rw [← Set.range_eq_univ, Scheme.Pullback.range_snd]
    exact Set.eq_univ_of_forall fun y => h2 ⟨y, rfl⟩⟩
  haveI := isIso_of_isClosedImmersion_of_surjective (pullback.snd j.liftCoborder ν')
  have key : pullback.fst j.liftCoborder ν' ≫ j = pullback.snd j.liftCoborder ν' ≫ ν := by
    have := congrArg (· ≫ j.coborderRange.ι) (pullback.condition (f := j.liftCoborder) (g := ν'))
    simp only [Category.assoc, Scheme.Hom.liftCoborder_ι, hν'] at this
    exact this
  refine ⟨inv (pullback.snd j.liftCoborder ν') ≫ pullback.fst j.liftCoborder ν', ?_⟩
  rw [Category.assoc, key, IsIso.inv_hom_id_assoc]

theorem lsurj {X Y W Z : Scheme.{0}} (l : W ⟶ X) (f : X ⟶ Y) (ν : Z ⟶ Y)
    (h : ∀ z : (pullback f ν : Scheme.{0}), pullback.fst f ν z ∈ Set.range l)
    (hc : ConnectedSpace (pullback (l ≫ f) ν : Scheme.{0})) : ConnectedSpace (pullback f ν : Scheme.{0}) := by
  haveI : ConnectedSpace (pullback l (pullback.fst f ν) : Scheme.{0}) :=
    (pullbackRightPullbackFstIso f ν l).hom.homeomorph.connectedSpace_iff.2 hc
  refine Function.Surjective.connectedSpace (f := pullback.snd l (pullback.fst f ν)) ?_
    (pullback.snd l (pullback.fst f ν)).continuous
  intro z
  obtain ⟨w, hw⟩ := h z
  obtain ⟨d, -, hd⟩ := Scheme.Pullback.exists_preimage_pullback w z hw
  exact ⟨d, hd⟩

theorem liso {W Y T P Z B : Scheme.{0}} (a : Y ⟶ B) (k : T ⟶ B) (e : W ⟶ pullback a k) [IsIso e]
    (j : Y ⟶ P) [Mono j] (y₀ : Z ⟶ Y) (hc : ConnectedSpace (pullback (y₀ ≫ a) k : Scheme.{0})) :
    ConnectedSpace (pullback (e ≫ pullback.fst a k ≫ j) (y₀ ≫ j) : Scheme.{0}) := by
  set F := e ≫ pullback.fst a k ≫ j with hF
  set G := y₀ ≫ j with hG
  have c0 : pullback.fst F G ≫ e ≫ pullback.fst a k = pullback.snd F G ≫ y₀ := by
    rw [← cancel_mono j]
    have := pullback.condition (f := F) (g := G)
    simp only [hF, hG, Category.assoc] at this ⊢
    exact this
  have c1 : (pullback.fst (y₀ ≫ a) k ≫ y₀) ≫ a = pullback.snd (y₀ ≫ a) k ≫ k := by
    rw [Category.assoc]; exact pullback.condition
  let m₀ : pullback (y₀ ≫ a) k ⟶ pullback a k := pullback.lift (pullback.fst _ _ ≫ y₀) (pullback.snd _ _) c1
  have c2 : (m₀ ≫ inv e) ≫ F = pullback.fst (y₀ ≫ a) k ≫ G := by
    simp only [hF, hG, m₀, Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  let m : pullback (y₀ ≫ a) k ⟶ pullback F G := pullback.lift (m₀ ≫ inv e) (pullback.fst _ _) c2
  have c3 : pullback.snd F G ≫ y₀ ≫ a = (pullback.fst F G ≫ e ≫ pullback.snd a k) ≫ k := by
    rw [← Category.assoc, ← c0]
    simp only [Category.assoc, pullback.condition]
  let n : pullback F G ⟶ pullback (y₀ ≫ a) k := pullback.lift (pullback.snd _ _) (pullback.fst _ _ ≫ e ≫ pullback.snd a k) c3
  let φ : pullback (y₀ ≫ a) k ≅ pullback F G :=
    { hom := m, inv := n
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [m, n, Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
        · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
            Category.id_comp]
      inv_hom_id := by
        apply pullback.hom_ext
        · rw [← cancel_mono e]
          apply pullback.hom_ext
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst, IsIso.inv_hom_id_assoc,
              Category.id_comp]
            exact c0.symm
          · simp only [m, n, m₀, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd, IsIso.inv_hom_id_assoc,
              Category.id_comp]
        · simp only [m, n, Category.assoc, pullback.lift_snd, pullback.lift_fst, Category.id_comp] }
  haveI : IsIso φ.hom := Iso.isIso_hom φ
  exact φ.hom.homeomorph.connectedSpace_iff.1 hc

theorem lred {X Y Z W : Scheme.{0}} (i : X ⟶ Y) [IsClosedImmersion i] (hs : Function.Surjective i)
    (s : Y ⟶ W) (h : Z ⟶ W) (hc : ConnectedSpace (pullback h s : Scheme.{0})) :
    ConnectedSpace (pullback h (i ≫ s) : Scheme.{0}) := by
  haveI : Surjective i := ⟨hs⟩
  let q := pullback.fst (pullback.snd h s) i
  have hq : Function.Surjective q := (inferInstance : Surjective q).surj
  haveI : Nonempty (pullback (pullback.snd h s) i : Scheme.{0}) :=
    ⟨(hq (Nonempty.some inferInstance)).choose⟩
  haveI : ConnectedSpace (pullback (pullback.snd h s) i : Scheme.{0}) := by
    refine connectedSpace_iff_univ.2 ⟨Set.univ_nonempty, ?_⟩
    refine (q.isClosedEmbedding.isInducing.isPreconnected_image).1 ?_
    rw [Set.image_univ, hq.range_eq]
    exact isPreconnected_univ
  exact (pullbackLeftPullbackSndIso h s i).hom.homeomorph.connectedSpace_iff.1 this

theorem fib_conn : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  intro R _ _ _ S π hπ G' _ hG E hconn Ω _ _ ν hex
  obtain ⟨g, hg, p, hp⟩ := hex
  obtain ⟨y, hy⟩ := (GlobalTheory.Mum.Emb.range_closed R S π G' E).1 g hg
  haveI := E.imm
  have hrange : Set.range ν ⊆ Set.range E.j := by
    rintro _ ⟨q, rfl⟩
    rw [Subsingleton.elim q p, hp, hy]
    exact ⟨y, rfl⟩
  obtain ⟨y₀, hy₀⟩ := lfac E.j Ω ν hrange
  let κ₀ : ResidueField R →+* Ω := (Spec.preimage (y₀ ≫ E.Y.hom)).hom
  have hκ₀ : y₀ ≫ E.Y.hom = spMap κ₀ := by
    simp [κ₀, spMap]
  haveI := hπ
  let ρ := spMap (residue R)
  let S₀ := pullback π ρ
  haveI : IsLocallyNoetherian S₀ := LocallyOfFiniteType.isLocallyNoetherian (pullback.snd π ρ)
  let T := S₀.nilradical.subscheme
  let i : T ⟶ S₀ := S₀.nilradical.subschemeι
  haveI : IsReduced T := GlobalTheory.RedFibreField.isReduced_nilradical_subscheme _
  haveI : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian i
  have hi : Function.Surjective i := by
    rw [← Set.range_eq_univ, Scheme.IdealSheafData.range_subschemeι, Scheme.support_nilradical]
    rfl
  let t := i ≫ pullback.fst π ρ
  let kk := i ≫ pullback.snd π ρ
  obtain ⟨e, l, -, hl1, hl2⟩ := GlobalTheory.T.pullback_iso_baseChange_over_reduced_closedFibre R S π G' hG E T t kk inferInstance inferInstance
    (by show i ≫ pullback.fst π ρ ≫ π = (i ≫ pullback.snd π ρ) ≫ ρ; rw [pullback.condition, Category.assoc])
  apply lsurj l E.f ν
  · intro z
    have h1 : E.f (pullback.fst E.f ν z) = ν (pullback.snd E.f ν z) := by
      rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply]
    have h3 : ν (pullback.snd E.f ν z) = E.f g := by rw [Subsingleton.elim (pullback.snd E.f ν z) p, hp]
    have h4 : ∀ b : E.H.toScheme, PSpace.str R E.N (E.f b) = π (G'.hom (E.H.ι b)) := fun b => by
      rw [← Scheme.Hom.comp_apply, E.f_over]
      rfl
    have h2 : π (G'.hom (E.H.ι (pullback.fst E.f ν z))) = closedPoint R := by
      rw [← h4, h1, h3, h4, hg]
    have h5 : G'.hom (E.H.ι (pullback.fst E.f ν z)) ∈ Set.range (pullback.fst π ρ) := by
      rw [Scheme.Pullback.range_fst]
      exact ⟨closedPoint (ResidueField R), (IsLocalRing.comap_closedPoint (residue R)).trans h2.symm⟩
    obtain ⟨w, hw⟩ := h5
    obtain ⟨u, rfl⟩ := hi w
    obtain ⟨d, hd1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := G'.hom) (g := t)
      (E.H.ι (pullback.fst E.f ν z)) u hw.symm
    refine ⟨d, E.H.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hl1, hd1]
  · rw [hl2, ← hy₀]
    apply liso E.Y.hom kk e.hom E.j y₀
    rw [hκ₀]
    apply lred i hi
    have hc := hconn Ω κ₀
    have hcomp : spMap (κ₀.comp (residue R)) = spMap κ₀ ≫ ρ := by
      simp only [ρ, spMap, ← Spec.map_comp]
      rfl
    rw [hcomp] at hc
    exact ((pullbackLeftPullbackSndIso π ρ (spMap κ₀)).symm ≪≫ pullbackSymmetry _ _).hom.homeomorph.connectedSpace_iff.1 hc

end GlobalTheory.Mum.FibConn
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricFibre_projEmbedding_fixedGroup_connected : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R), LocallyOfFiniteType π → ∀ (G' : Over S) [GrpObj G'], Smooth G'.hom → ∀ (E : Emb π G'), (∀ (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback π (spMap (κ.comp (residue R))) : Scheme.{0})) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ν : Sp Ω ⟶ PSpace R E.N), (∃ g : E.H.toScheme, π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range ν) → ConnectedSpace (pullback E.f ν : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.Mum.FibConn.fib_conn
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem connectedSpace_pullback_of_finitelyGenerated_residue :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ S π hprop hsurj hbij K _ κ L hL n c hLc
  haveI := hprop
  haveI := hsurj
  have hc : ∀ j, c j ∈ L := fun j => hLc ▸ Subfield.subset_closure (Or.inr ⟨j, rfl⟩)
  set A := MvPolynomial (Fin n) R
  set ιC : R →+* A := MvPolynomial.C with hC
  set β : R →+* L := (κ.codRestrict L hL).comp (residue R) with hβ
  set φ : A →+* L := MvPolynomial.eval₂Hom β (fun j => ⟨c j, hc j⟩) with hφ
  have hφC : φ.comp ιC = β := by
    refine RingHom.ext fun r => ?_
    show MvPolynomial.eval₂ β (fun j => (⟨c j, hc j⟩ : L)) (MvPolynomial.C r) = β r
    exact MvPolynomial.eval₂_C _ _ _
  have hx : spMap β = spMap φ ≫ spMap ιC := by
    rw [← hφC]
    show Spec.map (CommRingCat.ofHom (φ.comp ιC)) = Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom ιC)
    rw [← Spec.map_comp]; rfl

  have hdiv : ∀ x : L, ∃ a b : A, φ b ≠ 0 ∧ φ b * x = φ a := by
    have hsub : Subring.closure (Set.range κ ∪ Set.range c) ≤ (φ.range).map L.subtype := by
      rw [Subring.closure_le]
      rintro y (⟨z, rfl⟩ | ⟨j, rfl⟩)
      · obtain ⟨r, rfl⟩ := residue_surjective z
        exact ⟨β r, ⟨MvPolynomial.C r, MvPolynomial.eval₂_C _ _ _⟩, rfl⟩
      · exact ⟨⟨c j, hc j⟩, ⟨MvPolynomial.X j, MvPolynomial.eval₂_X _ _ _⟩, rfl⟩
    intro x
    have hx' : (x : K) ∈ Subfield.closure (Set.range κ ∪ Set.range c) := hLc ▸ x.2
    obtain ⟨y, hy, z, hz, hyz⟩ := Subfield.mem_closure_iff.1 hx'
    obtain ⟨y', ⟨a, rfl⟩, rfl⟩ := hsub hy
    obtain ⟨z', ⟨b, rfl⟩, rfl⟩ := hsub hz
    by_cases hb : φ b = 0
    · refine ⟨0, 1, by simp, ?_⟩
      have : (x : K) = 0 := by rw [← hyz]; simp [hb]
      have : x = 0 := Subtype.ext this
      simp [this]
    · refine ⟨a, b, hb, ?_⟩
      apply Subtype.ext
      have hb' : ((φ b : L) : K) ≠ 0 := fun h => hb (Subtype.ext h)
      simp only [Subfield.coe_mul, L.subtype_apply] at hyz ⊢
      rw [← hyz]; field_simp
  have hstalk : φ.SurjectiveOnStalks := by
    refine RingHom.surjectiveOnStalks_of_exists_div fun x => ?_
    obtain ⟨a, b, hb, e⟩ := hdiv x
    exact ⟨a, b, (isUnit_iff_ne_zero).2 hb, e⟩
  haveI hpre : IsPreimmersion (spMap φ) := by
    rw [IsPreimmersion.SpecMap_iff]
    refine ⟨?_, hstalk⟩
    haveI : Subsingleton (PrimeSpectrum L) := inferInstance
    exact Topology.IsEmbedding.of_subsingleton _

  set π' : pullback π (spMap ιC) ⟶ Sp A := pullback.snd π (spMap ιC) with hπ'
  have hflat : Flat (spMap ιC) := by
    refine Flat.SpecMap_iff.2 ?_
    show (algebraMap R A).Flat
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  have hbij' : ∀ V : (Sp A).Opens, Function.Bijective (π'.app V).hom :=
    GlobalTheory.Mum.app_bijective_of_flat_baseChange R S (Sp A) _ π (spMap ιC) _ _ inferInstance inferInstance
      hbij hflat (IsPullback.of_hasPullback π (spMap ιC)).flip
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum L) := inferInstance
  have hconn := GlobalTheory.T.zariski_connectedness_isPreconnected_fibre _ _ π' inferInstance inferInstance hbij' (spMap φ q)
  have hrange : Set.range (spMap φ) = {spMap φ q} := by
    ext y
    constructor
    · rintro ⟨q', rfl⟩; rw [Subsingleton.elim q' q]; rfl
    · rintro rfl; exact ⟨q, rfl⟩
  set f := pullback.fst π' (spMap φ) with hf
  have hfr : Set.range f = {s | π' s = spMap φ q} := by
    rw [hf, Scheme.Pullback.range_fst, hrange]; rfl
  have hP : PreconnectedSpace ↥(pullback π' (spMap φ)) := by
    refine ⟨?_⟩
    rw [← f.isEmbedding.isInducing.isPreconnected_image, Set.image_univ, hfr]
    exact hconn
  have e : pullback π (spMap β) ≅ pullback π' (spMap φ) :=
    pullback.congrHom rfl hx ≪≫ (pullbackLeftPullbackSndIso π (spMap ιC) (spMap φ)).symm
  obtain ⟨z, -⟩ := (pullback.snd π (spMap β)).surjective q
  haveI : ConnectedSpace ↥(pullback π' (spMap φ)) := ConnectedSpace.mk ⟨e.hom z⟩
  exact (Scheme.homeoOfIso e).symm.surjective.connectedSpace (Scheme.homeoOfIso e).symm.continuous

end GlobalTheory.Mum
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (S : Scheme.{0}) (π : S ⟶ Sp R),
      IsProper π → Surjective π → Function.Bijective π.appTop.hom →
      ∀ (K : Type) [Field K] (κ : ResidueField R →+* K) (L : Subfield K) (hL : ∀ x, κ x ∈ L) (n : ℕ) (c : Fin n → K),
        L = Subfield.closure (Set.range κ ∪ Set.range c) →
        ConnectedSpace (pullback π (spMap ((κ.codRestrict L hL).comp (residue R))) : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.Mum.connectedSpace_pullback_of_finitelyGenerated_residue
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem flat_spec_field {K : Type} [Field K] {Z : Scheme.{0}} (f : Z ⟶ Sp K) : Flat f := by
  haveI : IsIntegral (Sp K) := by unfold Sp; infer_instance
  haveI : Subsingleton (Sp K) := by unfold Sp; infer_instance
  infer_instance

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (i : A →+* B) (j : B →+* C) :
    spMap (j.comp i) = spMap j ≫ spMap i := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem appTop_spMap_injective {A B : Type} [CommRing A] [CommRing B] (j : A →+* B)
    (hj : Function.Injective j) : Function.Injective (spMap j).appTop.hom := by
  intro a b h
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom j)
  have h3 : ∀ x, (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap j).appTop.hom x) =
      j ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom x) := fun x => congrArg (fun f => f.hom x) e
  have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom h
  rw [h3, h3] at h2
  have h4 := hj h2
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom h4
  simpa using this

theorem appTop_spMap_inv {A B : Type} [CommRing A] [CommRing B] (j : A →+* B) (y : A) :
    (spMap j).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom y) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (j y) := by
  have e := Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j)
  exact (congrArg (fun f => f.hom y) e).symm

variable {F : Type} [CommRing F] {X : Scheme.{0}} (f : X ⟶ Sp F)

def bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    pullback f (spMap i₀) ⟶ pullback f (spMap i) :=
  pullback.map f (spMap i₀) f (spMap i) (𝟙 X) (spMap j) (𝟙 _) (by simp)
    (by rw [Category.comp_id, ← hji, spMap_comp])

theorem bc_fst {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.fst f (spMap i) = pullback.fst f (spMap i₀) := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_fst _ _ _

theorem bc_snd {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    bc f i₀ i j hji ≫ pullback.snd f (spMap i) = pullback.snd f (spMap i₀) ≫ spMap j := by
  simp only [bc, pullback.map, Category.comp_id]
  exact pullback.lift_snd _ _ _

theorem isPullback_bc {K A : Type} [CommRing K] [CommRing A] (i₀ : F →+* K) (i : F →+* A) (j : A →+* K) (hji : j.comp i = i₀) :
    IsPullback (bc f i₀ i j hji) (pullback.snd f (spMap i₀)) (pullback.snd f (spMap i)) (spMap j) := by
  have s : IsPullback (bc f i₀ i j hji ≫ pullback.fst f (spMap i)) (pullback.snd f (spMap i₀)) f
      (spMap j ≫ spMap i) := by
    rw [bc_fst, ← spMap_comp, hji]
    exact IsPullback.of_hasPullback f (spMap i₀)
  exact IsPullback.of_right s (bc_snd f i₀ i j hji) (IsPullback.of_hasPullback f (spMap i))

theorem bc_trans {K A B : Type} [CommRing K] [CommRing A] [CommRing B] (i₀ : F →+* K) (i₁ : F →+* A) (j₁ : A →+* K) (h₁ : j₁.comp i₁ = i₀)
    (i₂ : F →+* B) (j₂ : B →+* K) (h₂ : j₂.comp i₂ = i₀) (k : A →+* B) (hk : k.comp i₁ = i₂)
    (hk' : j₂.comp k = j₁) :
    bc f i₀ i₁ j₁ h₁ = bc f i₀ i₂ j₂ h₂ ≫ bc f i₂ i₁ k hk := by
  apply pullback.hom_ext
  · simp [bc_fst]
  · rw [Category.assoc, bc_snd, bc_snd, ← Category.assoc, bc_snd, Category.assoc, ← spMap_comp, hk']

theorem mem_of_isPushout {R A B P : CommRingCat.{0}} {φ : R ⟶ A} {ψ : R ⟶ B} {inl : A ⟶ P} {inr : B ⟶ P}
    (H : IsPushout φ ψ inl inr) (S : Subring P) (hA : ∀ a, inl.hom a ∈ S) (hB : ∀ b, inr.hom b ∈ S)
    (x : P) : x ∈ S := by
  let inl' : A ⟶ CommRingCat.of S := CommRingCat.ofHom (inl.hom.codRestrict S hA)
  let inr' : B ⟶ CommRingCat.of S := CommRingCat.ofHom (inr.hom.codRestrict S hB)
  have w : φ ≫ inl' = ψ ≫ inr' := by
    ext r
    exact congrArg (fun g => g.hom r) H.w
  have hd : H.desc inl' inr' w ≫ CommRingCat.ofHom S.subtype = 𝟙 P := by
    apply H.hom_ext
    · rw [H.inl_desc_assoc, Category.comp_id]; rfl
    · rw [H.inr_desc_assoc, Category.comp_id]; rfl
  have := congrArg (fun g => g.hom x) hd
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at this
  rw [← this]
  exact ((H.desc inl' inr' w).hom x).2

theorem isClosed_basicOpen_idem {Y : Scheme.{0}} {e : Γ(Y, ⊤)} (he : IsIdempotentElem e) :
    IsClosed (Y.basicOpen e : Set Y) := by
  have : (Y.basicOpen e : Set Y) = (Y.basicOpen (1 - e) : Set Y)ᶜ := by
    ext x
    constructor
    · intro h h'
      have hx : x ∈ Y.basicOpen (e * (1 - e)) := by rw [Scheme.basicOpen_mul]; exact ⟨h, h'⟩
      rw [he.mul_one_sub_self, Scheme.basicOpen_zero] at hx
      exact hx
    · intro h
      rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Y.presheaf.germ ⊤ x trivial e) with h' | h'
      · exact (Y.mem_basicOpen e x trivial).2 h'
      · exact absurd ((Y.mem_basicOpen (U := ⊤) (1 - e) x trivial).2 (by rwa [map_sub, map_one])) h
  rw [this]
  exact (Y.basicOpen (1 - e)).isOpen.isClosed_compl

end GlobalTheory.GeomConnDesc

end

noncomputable section

namespace GlobalTheory.GeomConnDesc

theorem appTop_comp_apply {X Y Z : Scheme.{0}} (g : X ⟶ Y) (h : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (g ≫ h).appTop.hom x = g.appTop.hom (h.appTop.hom x) := by
  rw [Scheme.Hom.comp_appTop]; rfl

variable {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Sp F) {K : Type} [Field K] (i₀ : F →+* K)

def Lc {n : ℕ} (c : Fin n → K) : Subfield K := Subfield.closure (Set.range i₀ ∪ Set.range c)

theorem mem_Lc {n : ℕ} (c : Fin n → K) (x : F) : i₀ x ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inl ⟨x, rfl⟩)

theorem mem_Lc' {n : ℕ} (c : Fin n → K) (k : Fin n) : c k ∈ Lc i₀ c :=
  Subfield.subset_closure (Or.inr ⟨k, rfl⟩)

theorem hji_L (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) : L.subtype.comp (i₀.codRestrict L hL) = i₀ :=
  RingHom.ext fun _ => rfl

def hcL (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict L hL)) :=
  bc f i₀ (i₀.codRestrict L hL) L.subtype (hji_L i₀ L hL)

theorem hcL_factor {L₁ L₂ : Subfield K} (hL₁ : ∀ x, i₀ x ∈ L₁) (hL₂ : ∀ x, i₀ x ∈ L₂) (hle : L₁ ≤ L₂)
    (y : Γ(pullback f (spMap (i₀.codRestrict L₁ hL₁)), ⊤)) :
    ∃ y', (hcL f i₀ L₁ hL₁).appTop.hom y = (hcL f i₀ L₂ hL₂).appTop.hom y' := by
  have e : hcL f i₀ L₁ hL₁ = hcL f i₀ L₂ hL₂ ≫ bc f (i₀.codRestrict L₂ hL₂)
      (i₀.codRestrict L₁ hL₁) (Subfield.inclusion hle) (RingHom.ext fun _ => rfl) :=
    bc_trans f i₀ (i₀.codRestrict L₁ hL₁) L₁.subtype (hji_L i₀ L₁ hL₁)
      (i₀.codRestrict L₂ hL₂) L₂.subtype (hji_L i₀ L₂ hL₂) (Subfield.inclusion hle)
      (RingHom.ext fun _ => rfl) (RingHom.ext fun _ => rfl)
  exact ⟨_, by rw [e, appTop_comp_apply]⟩

def hc {n : ℕ} (c : Fin n → K) :
    pullback f (spMap i₀) ⟶ pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))) :=
  hcL f i₀ (Lc i₀ c) (mem_Lc i₀ c)

theorem hc_factor {n m : ℕ} (c : Fin n → K) (d : Fin m → K) (hle : Lc i₀ c ≤ Lc i₀ d)
    (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)) :
    ∃ y', (hc f i₀ c).appTop.hom y = (hc f i₀ d).appTop.hom y' :=
  hcL_factor f i₀ (mem_Lc i₀ c) (mem_Lc i₀ d) hle y

theorem Lc_le_append_left {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ c ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.castAdd m k, Fin.append_left _ _ _⟩))

theorem Lc_le_append_right {n m : ℕ} (c : Fin n → K) (d : Fin m → K) : Lc i₀ d ≤ Lc i₀ (Fin.append c d) :=
  Subfield.closure_mono (Set.union_subset_union_right _
    (Set.range_subset_iff.2 fun k => ⟨Fin.natAdd n k, Fin.append_right _ _ _⟩))

theorem gen [QuasiCompact f] [QuasiSeparated f] (x : Γ(pullback f (spMap i₀), ⊤)) :
    ∃ (n : ℕ) (c : Fin n → K) (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)),
      (hc f i₀ c).appTop.hom y = x := by
  haveI : Flat (spMap i₀) := flat_spec_field _
  let S : Subring Γ(pullback f (spMap i₀), ⊤) :=
    { carrier := {x | ∃ (n : ℕ) (c : Fin n → K)
        (y : Γ(pullback f (spMap (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c))), ⊤)), (hc f i₀ c).appTop.hom y = x}
      zero_mem' := ⟨0, Fin.elim0, 0, map_zero _⟩
      one_mem' := ⟨0, Fin.elim0, 1, map_one _⟩
      neg_mem' := by
        rintro _ ⟨n, c, y, rfl⟩
        exact ⟨n, c, -y, map_neg _ _⟩
      add_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' + z', by rw [map_add, hy', hz']⟩
      mul_mem' := by
        rintro _ _ ⟨n, c, y, rfl⟩ ⟨m, d, z, rfl⟩
        obtain ⟨y', hy'⟩ := hc_factor f i₀ c (Fin.append c d) (Lc_le_append_left i₀ c d) y
        obtain ⟨z', hz'⟩ := hc_factor f i₀ d (Fin.append c d) (Lc_le_append_right i₀ c d) z
        exact ⟨_, Fin.append c d, y' * z', by rw [map_mul, hy', hz']⟩ }
  have H := ProperFunctions.isPushout_appTop (IsPullback.of_hasPullback f (spMap i₀))
  refine mem_of_isPushout H S (fun a => ?_) (fun b => ?_) x
  · refine ⟨0, Fin.elim0, (pullback.fst f _).appTop.hom a, ?_⟩
    rw [← appTop_comp_apply]
    exact congrArg (fun g => g.appTop.hom a) (bc_fst f i₀ (i₀.codRestrict (Lc i₀ Fin.elim0) (mem_Lc i₀ Fin.elim0)) (Lc i₀ Fin.elim0).subtype (hji_L i₀ _ (mem_Lc i₀ Fin.elim0)))
  · let c : Fin 1 → K := ![(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b]
    refine ⟨1, c, (pullback.snd f _).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (Lc i₀ c))).inv.hom ⟨c 0, mem_Lc' i₀ c 0⟩), ?_⟩
    rw [← appTop_comp_apply]
    rw [show hc f i₀ c ≫ pullback.snd f _ = pullback.snd f (spMap i₀) ≫ spMap (Lc i₀ c).subtype from
      bc_snd f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)), appTop_comp_apply, appTop_spMap_inv]
    change (pullback.snd f (spMap i₀)).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom b)) = _
    simp

theorem preconnectedSpace_of_finGen : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F),
    QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  intro F _ X f _ _ K _ i₀ hyp
  haveI : Flat f := flat_spec_field f
  refine preconnectedSpace_iff_clopen.2 fun U hU => ?_
  obtain ⟨e, he, hUe⟩ := GlobalTheory.exists_idempotent_basicOpen_eq_of_isClopen _ U hU
  obtain ⟨n, c, y, rfl⟩ := gen f i₀ e
  have hinj : Function.Injective (hc f i₀ c).appTop.hom :=
    ProperFunctions.injective_appTop_of_isPullback (isPullback_bc f i₀ (i₀.codRestrict (Lc i₀ c) (mem_Lc i₀ c)) (Lc i₀ c).subtype (hji_L i₀ _ (mem_Lc i₀ c)))
      (appTop_spMap_injective _ (Lc i₀ c).subtype.injective)
  have hy : IsIdempotentElem y := hinj (by rw [map_mul]; exact he)
  have hcl : IsClopen (SetLike.coe (Scheme.basicOpen _ y)) :=
    ⟨isClosed_basicOpen_idem hy, (Scheme.basicOpen _ y).isOpen⟩
  haveI := hyp (Lc i₀ c) (mem_Lc i₀ c) n c rfl
  have hU' : U = (hc f i₀ c) ⁻¹' (SetLike.coe (Scheme.basicOpen _ y)) := by
    rw [← hUe, ← Scheme.preimage_basicOpen_top]; rfl
  rcases isClopen_iff.1 hcl with h0 | h1
  · left; rw [hU', h0]; rfl
  · right; rw [hU', h1]; rfl

end GlobalTheory.GeomConnDesc

end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges : ∀ (F : Type) [Field F] (X : Scheme.{0}) (f : X ⟶ Sp F), QuasiCompact f → QuasiSeparated f →
      ∀ (K : Type) [Field K] (i₀ : F →+* K),
        (∀ (L : Subfield K) (hL : ∀ x, i₀ x ∈ L) (n : ℕ) (c : Fin n → K),
          L = Subfield.closure (Set.range i₀ ∪ Set.range c) →
          PreconnectedSpace (pullback f (spMap (i₀.codRestrict L hL)) : Scheme.{0})) →
        PreconnectedSpace (pullback f (spMap i₀) : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.GeomConnDesc.preconnectedSpace_of_finGen
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

theorem GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  intro R _ _ _ hA M K _ κ
  obtain ⟨hN, -, hIC, -⟩ := hA
  haveI := hN
  haveI := hIC
  obtain ⟨hbij, hsurj⟩ := Modif.appTop_bijective_surjective R M
  haveI := M.proper
  haveI := hsurj
  have hcomp : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      spMap ψ ≫ spMap (residue R) = spMap (ψ.comp (residue R)) := fun ψ => by
    rw [← Spec.map_comp]; rfl
  have pc : ∀ {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (h : X ≃ₜ Y) [PreconnectedSpace X], PreconnectedSpace Y :=
    fun h _ => ⟨by rw [← h.surjective.range_eq, ← Set.image_univ]; exact isPreconnected_univ.image _ h.continuous.continuousOn⟩
  let f := pullback.snd M.π (spMap (residue R))
  have e : ∀ {A : Type} [CommRing A] (ψ : ResidueField R →+* A),
      pullback f (spMap ψ) ≅ pullback M.π (spMap (ψ.comp (residue R))) := fun ψ =>
    pullbackLeftPullbackSndIso M.π (spMap (residue R)) (spMap ψ) ≪≫ pullback.congrHom rfl (hcomp ψ)
  have hP : PreconnectedSpace (pullback f (spMap κ) : Scheme.{0}) := by
    refine GlobalTheory.T.preconnectedSpace_of_finGen_subfield_baseChanges (ResidueField R) _ f inferInstance inferInstance K κ fun L hL n c hc => ?_
    have hc' := GlobalTheory.T.connectedSpace_closedFibre_finitelyGenerated_ext R M.S M.π inferInstance hsurj hbij K κ L hL n c hc
    exact @pc _ _ _ _ (Scheme.homeoOfIso (e _)).symm hc'.toPreconnectedSpace
  haveI : PreconnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) :=
    pc (Scheme.homeoOfIso (e κ))
  obtain ⟨q⟩ : Nonempty (Sp K) := inferInstance
  obtain ⟨z, -⟩ := (pullback.snd M.π (spMap (κ.comp (residue R)))).surjective q
  exact ConnectedSpace.mk ⟨z⟩
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (K : Type) [Field K] (κ : ResidueField R →+* K), ConnectedSpace (pullback M.π (spMap (κ.comp (residue R))) : Scheme.{0}) := by
  atlas_forward_decl GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field
end

section
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in

theorem GlobalTheory.Mum.Emb.lift_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hAdm M G' _ _ hG E P' b X a hb ha hab hX x hx hxc Ω _ _ ξ s hξ hs
  have hxr : ∀ w, ξ w = x := fun w => by
    have : ξ w ∈ Set.range ξ := ⟨w, rfl⟩
    rw [hξ] at this; exact this
  have hfo : ∀ h : E.H.toScheme, PSpace.str R E.N (E.f h) = M.π (G'.hom (E.H.ι h)) := fun h => by
    rw [← Scheme.Hom.comp_apply, E.f_over]; rfl
  have hcl : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → M.π (G'.hom (E.H.ι h)) = closedPoint R := by
    rintro h ⟨w, hw⟩
    rw [← hfo, ← hw, ← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.comp_apply, hxr]
    exact hxc
  obtain ⟨z, hz⟩ := ha.surj x
  have hzx : E.f (X.ι z) = b x := by
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
  have hrng : E.f (X.ι z) ∈ Set.range (ξ ≫ b) := by
    let w : Sp Ω := Nonempty.some inferInstance
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hxr, hzx]⟩
  have hg : ∃ g : E.H.toScheme, M.π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range (ξ ≫ b) :=
    ⟨X.ι z, hcl _ hrng, hrng⟩
  have hs' : (ξ ≫ b) ≫ PSpace.str R E.N = s ≫ M.π := by rw [Category.assoc]; exact hs
  obtain ⟨Ω', _, io, q, hq1, hq2⟩ := GlobalTheory.T.exists_lift_after_field_extension R M.S M.π G' E Ω (ξ ≫ b) s hs' hg
  let φ : E.H.toScheme ⟶ pullback M.π (PSpace.str R E.N) :=
    pullback.lift (E.H.ι ≫ G'.hom) E.f (by rw [E.f_over, Category.assoc])
  haveI : Smooth G'.hom := hG.smooth
  have hφ : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    exact HasRingHomProperty.of_comp (fun _ _ => RingHom.FiniteType.of_comp_finiteType) this
  obtain ⟨p₀, hp₀⟩ := GlobalTheory.T.exists_rational_point_of_point_over_field_extension _ _ φ hφ Ω (pullback.lift s (ξ ≫ b) hs'.symm) Ω' io q (by
    apply pullback.hom_ext
    · simp only [φ, Category.assoc, pullback.lift_fst]; exact hq2
    · simp only [φ, Category.assoc, pullback.lift_snd]; exact hq1)
  have hp1 : p₀ ≫ E.f = ξ ≫ b := by
    have := congrArg (· ≫ pullback.snd M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_snd, pullback.lift_snd] at this
  have hp2 : p₀ ≫ E.H.ι ≫ G'.hom = s := by
    have := congrArg (· ≫ pullback.fst M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_fst, pullback.lift_fst, ← Category.assoc] at this
  have hU : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → h ∈ X := fun h hh => hX h (hcl h hh)
  have hpX : Set.range p₀ ⊆ Set.range X.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hU _ ⟨w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp1]
  let p : Sp Ω ⟶ X.toScheme := IsOpenImmersion.lift X.ι p₀ hpX
  have hpι : p ≫ X.ι = p₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsNoetherianRing R := hAdm.1
  have c4 := GlobalTheory.T.geometricFibre_projEmbedding_fixedGroup_connected R M.S M.π (by have := M.proper; infer_instance) G' hG.smooth E
    (GlobalTheory.T.connectedSpace_closedFibre_modification_fieldExtension R hAdm M) Ω (ξ ≫ b) hg
  have c3 := GlobalTheory.T.connectedSpace_pullback_restrict_open_containing_fibre _ _ _ X E.f (ξ ≫ b) hU c4
  have c2 := GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective _ _ _ _ a b (X.ι ≫ E.f) (ξ ≫ b) hab ha c3
  refine ⟨p, GlobalTheory.T.eq_of_comp_eq_of_connectedSpace_pullback' _ _ b hb Ω (ξ ≫ b) (p ≫ a) ξ ?_ rfl c2, ?_⟩
  · rw [Category.assoc, hab, ← Category.assoc, hpι, hp1]
  · rw [← Category.assoc, hpι, hp2]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_geometricPoint_over_closed_fibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  atlas_forward_decl GlobalTheory.Mum.Emb.lift_closedPoint
end
