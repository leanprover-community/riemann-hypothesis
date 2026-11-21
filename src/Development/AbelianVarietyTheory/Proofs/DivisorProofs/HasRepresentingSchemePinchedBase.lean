import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentingSchemeOfFiniteSurjectiveLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentsAdditiveLineBundleFamiliesUniqueIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveLineBundleFamilyOfGeometricFibres
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsLiftPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConductorSquareFlatBaseChangeSchemes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchingSquareUnitsPatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundleLocalGeneratorNearFiniteSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitRatioLocalGeneratorsCommonPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLineBundlePinchedOfMatchingGenerators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartOffClosedPartFromBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinchedChartsAffineOfSpectra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPushoutLocalizedPresentationBaseChange

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Pinch

variable {S : Scheme.{0}}

theorem isPullback_fst_whiskerRight {X Y : Over S} (f : X ⟶ Y) (W : Over S) :
    IsPullback (fst X W) (f ▷ W) f (fst Y W) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift s.fst (s.snd ≫ snd _ _)) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp [s.condition]
    · simp
  · ext1
    · simp [← h1]
    · simp [← h2]

theorem isPullback_snd_whiskerLeft (W : Over S) {X Y : Over S} (f : X ⟶ Y) :
    IsPullback (snd W X) (W ◁ f) f (snd W Y) := by
  refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => lift (s.snd ≫ fst _ _) s.fst) (fun s => by simp)
    (fun s => ?_) fun s l h1 h2 => ?_⟩⟩
  · ext1
    · simp
    · simp [s.condition]
  · ext1
    · simp [← h2]
    · simp [← h1]

theorem rep_cmp (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left)
    (e : C ⟶ Z) (Q : LB (A ⊗ C).left) (h₁ : Rep A b' P') (h₂ : Rep A e Q) :
    ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧
      Same A P' Q (fst B' Z) q := by
  have r₁ := Rep.baseChange S A B' S' (S' ⊗ Z) (B' ⊗ Z) b' P' (fst S' Z) (fst B' Z) (b' ▷ Z) h₁
    (isPullback_fst_whiskerRight b' Z)
  have r₂ := Rep.baseChange S A C Z (S' ⊗ Z) (S' ⊗ C) e Q (snd S' Z) (snd S' C) (S' ◁ e) h₂
    (isPullback_snd_whiskerLeft S' e)
  obtain ⟨ε, hε, hs⟩ := rep_unique S A (B' ⊗ Z) (S' ⊗ C) (S' ⊗ Z) (b' ▷ Z) _ (S' ◁ e) _ r₁ r₂
  have hf : ε.hom.left ≫ (fst S' C).left = (fst B' Z ≫ b').left := by
    rw [← Over.comp_left, ← whiskerLeft_fst S' e, reassoc_of% hε, whiskerRight_fst]
  refine ⟨ε.hom ≫ snd S' C, ?_, ?_, ?_⟩
  · rw [Category.assoc, ← whiskerLeft_snd, reassoc_of% hε, whiskerRight_snd]
  · have hpb : IsPullback (snd S' C).left (fst S' C).left C.hom S'.hom :=
      (IsPullback.of_hasPullback S'.hom C.hom).flip
    have : IsIso ε.hom.left := ⟨⟨ε.inv.left, by rw [← Over.comp_left, ε.hom_inv_id, Over.id_left],
      by rw [← Over.comp_left, ε.inv_hom_id, Over.id_left]⟩⟩
    have hiso : IsPullback ε.hom.left (fst B' Z ≫ b').left (fst S' C).left (𝟙 S'.left) :=
      IsPullback.of_horiz_isIso ⟨by rw [hf, Category.comp_id]⟩
    have := hiso.paste_horiz hpb
    rwa [Category.id_comp, ← Over.comp_left] at this
  · rw [same_iff h₁.fam.isLB h₂.fam.isLB]
    rw [same_iff r₁.fam.isLB r₂.fam.isLB, evc_ev h₁.fam.isLB, evc_ev h₂.fam.isLB] at hs
    simpa [lift_fst, lift_snd_assoc] using hs

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representsAdditiveLineBundleFamilies_compare : ∀ (S : Scheme.{0}) (A B' S' C Z : Over S) [GrpObj A] (b' : B' ⟶ S') (P' : LB (A ⊗ B').left) (e : C ⟶ Z) (Q : LB (A ⊗ C).left), GlobalTheory.DualCon.Rep A b' P' → GlobalTheory.DualCon.Rep A e Q → ∃ q : B' ⊗ Z ⟶ C, q ≫ e = snd B' Z ∧ IsPullback q.left (fst B' Z ≫ b').left C.hom S'.hom ∧ Same A P' Q (fst B' Z) q := by
  atlas_forward_decl GlobalTheory.Pinch.rep_cmp
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_fam_of_pull : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left],
    IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left)
    (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB →
    ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  intro S A U U' _ _ hA p hfin hsurj N' h c hc
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have key : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hL a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    have e : lift a (u ≫ p) = lift a u ≫ (A ◁ p) := by ext <;> simp
    rw [evc, e, Over.comp_left, pull_comp, hc]
    rfl
  obtain ⟨M, hM, hMc⟩ := cls_surj (cls L hL - CechPic.pull (snd A U).left (evc hL (1 : U ⟶ A) (𝟙 U)))
  have form : ∀ (Y : Over S) (a : Y ⟶ A) (t : Y ⟶ U), evc hM a t = evc hL a t - evc hL (1 : Y ⟶ A) t := by
    intro Y a t
    rw [evc, hMc, map_sub, ← pull_comp, ← Over.comp_left, lift_snd, pull_evc, MonObj.comp_one, Category.comp_id]
    rfl
  have keyM : ∀ (Y : Over S) (a : Y ⟶ A) (u : Y ⟶ U'), evc hM a (u ≫ p) = evc h.isLB a u := by
    intro Y a u
    rw [form, key, key, h.add.evc_one h.isLB, sub_zero]
  refine ⟨M, ⟨hM, GlobalTheory.T.isAdditive_lineBundleFamily_of_geometricFibres S A U hA M hM ((triv_ev_iff hM _ _).2 (by rw [form, sub_self])) ?_⟩, ?_⟩
  · intro K _ _ s t
    haveI := hfin
    haveI := hsurj
    obtain ⟨b, hb⟩ := exists_lift_pt p.left t.left
    let t' : Over.mk s ⟶ U' := Over.homMk b (by
      rw [← Over.w p, ← Category.assoc, hb, Over.w t])
    have ht : t = t' ≫ p := Over.OverMorphism.ext hb.symm
    rw [ht]
    refine (isAdditive_iff (pull_isLB hM _)).2 fun Y a a' y ↦ ?_
    have e : ∀ a₀ : Y ⟶ A, evc (pull_isLB hM _) a₀ y = evc h.isLB a₀ (y ≫ t') := fun a₀ ↦ by
      rw [evc_ev hM, lift_fst, lift_snd_assoc, ← Category.assoc, keyM]
    rw [e, e, e]
    exact (isAdditive_iff h.isLB).1 h.add _ _ _ _
  · rw [same_iff hM h.isLB, Category.comp_id]
    exact keyM _ _ _

end GlobalTheory.Pinch
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective : ∀ (S : Scheme.{0}) (A U U' : Over S) [GrpObj A] [IsLocallyNoetherian U.left], IsAbelianScheme A → ∀ (p : U' ⟶ U), IsFinite p.left → Surjective p.left → ∀ (N' : LB (A ⊗ U').left) (h : Fam A N') (c : Pic (A ⊗ U).left), GlobalTheory.CechPic.pull (A ◁ p).left c = cls N' h.isLB → ∃ M : LB (A ⊗ U).left, Fam A M ∧ Same A M N' p (𝟙 U') := by
  atlas_forward_decl GlobalTheory.Pinch.exists_fam_of_pull
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem locGen_near_fibre_of_finite : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  intro H X X' p hp L hL x
  obtain ⟨W₀, hW₀, hxW₀, -⟩ :=
    (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineOpen.preimage hW₀ p
  have hF : (p.base ⁻¹' {x}).Finite := Scheme.Hom.finite_preimage_singleton p x
  have hFW : p.base ⁻¹' {x} ⊆ (p ⁻¹ᵁ W₀ : Set X') := by
    intro y hy
    show p.base y ∈ W₀
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hy
    rw [hy]; exact hxW₀
  obtain ⟨V, a, hFV, ha⟩ := H X' L hL (p ⁻¹ᵁ W₀) hA _ hF hFW
  have hcl : IsClosed (p.base '' (V : Set X')ᶜ) := p.isClosedMap _ V.isOpen.isClosed_compl
  let W : X.Opens := ⟨(p.base '' (V : Set X')ᶜ)ᶜ, hcl.isOpen_compl⟩
  have hWV : p ⁻¹ᵁ W ≤ V := by
    intro y hy
    by_contra h
    exact hy ⟨y, h, rfl⟩
  have hxW : x ∈ W := by
    rintro ⟨y, hy, hyx⟩
    exact hy (hFV (show p.base y = x from hyx))
  refine ⟨W, fun k ↦ res (inf_le_inf_right _ hWV) (a k), hxW, ?_⟩
  intro y k k' hy hk hk'
  rw [gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk⟩, gm_res (𝟙 X') y (inf_le_inf_right _ hWV) ⟨hy, hk'⟩]
  exact ha y k k' (hWV hy) hk hk'

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_generator_finite_cover_near_point : (∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (W : X.Opens), IsAffineOpen W → ∀ F : Set X, F.Finite → F ⊆ W → ∃ (V : X.Opens) (a : ∀ k, Γ(X, V ⊓ L.U k)ˣ), F ⊆ V ∧ GlobalTheory.Pinch.LocGen L V a) → ∀ (X X' : Scheme.{0}) (p : X' ⟶ X), IsFinite p → ∀ (L : LB X'), L.IsLB → ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L.U k)ˣ), x ∈ W ∧ GlobalTheory.Pinch.LocGen L (p ⁻¹ᵁ W) a := by
  atlas_forward_decl GlobalTheory.Pinch.locGen_near_fibre_of_finite
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem unit_lift_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  intro X X' Z Z' p i i' p' h hp hi W x hx u
  have hi' : IsClosedImmersion i' := MorphismProperty.of_isPullback h.flip hi
  have hw : ∀ z : Z', p (i' z) = i (p' z) := fun z => by
    rw [← Scheme.Hom.comp_apply, h.w, Scheme.Hom.comp_apply]
  by_cases hxr : x ∈ Set.range i
  swap
  · refine ⟨W ⊓ ⟨(Set.range i)ᶜ, hi.base_closed.isClosed_range.isOpen_compl⟩, 1, inf_le_left, ⟨hx, hxr⟩,
      fun z hz => ?_⟩
    exact absurd ⟨p' z, (hw z).symm⟩ hz.2
  obtain ⟨z0, hz0⟩ := hxr
  obtain ⟨W₀, hW₀, hxW₀, hW₀W⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle0 : W₀ ≤ W := hW₀W
  have hA : IsAffineOpen (p ⁻¹ᵁ W₀) := IsAffineHom.isAffine_preimage _ hW₀
  let u0 : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W₀)) :=
    (Z'.presheaf.map (homOfLE (i'.preimage_mono (p.preimage_mono hle0))).op).hom u.val
  have hu0 : IsUnit u0 := (Units.isUnit u).map _
  obtain ⟨t, ht⟩ := Scheme.Hom.app_surjective i' (p ⁻¹ᵁ W₀) hA u0
  have hC : IsClosed ((X'.basicOpen t : Set X')ᶜ) := (X'.basicOpen t).isOpen.isClosed_compl
  let W' : X.Opens := W₀ ⊓ ⟨(p '' (X'.basicOpen t : Set X')ᶜ)ᶜ, (p.isClosedMap _ hC).isOpen_compl⟩
  have hsub : p ⁻¹ᵁ W' ≤ X'.basicOpen t := fun y hy => by
    by_contra hc
    exact hy.2 ⟨y, hc, rfl⟩
  have hx' : x ∈ W' := by
    refine ⟨hxW₀, ?_⟩
    rintro ⟨y, hyC, hy⟩
    obtain ⟨z', hz'1, -⟩ := Scheme.exists_preimage_of_isPullback h y z0 (hy.trans hz0.symm)
    apply hyC
    have hz'W : z' ∈ i' ⁻¹ᵁ (p ⁻¹ᵁ W₀) := by
      show p (i' z') ∈ W₀
      rw [hz'1, hy]; exact hxW₀
    have : z' ∈ i' ⁻¹ᵁ X'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, Scheme.basicOpen_of_isUnit _ hu0]
      exact hz'W
    rw [← hz'1]; exact this
  have hle' : p ⁻¹ᵁ W' ≤ p ⁻¹ᵁ W₀ := hsub.trans (X'.basicOpen_le t)
  have hunit : IsUnit ((X'.presheaf.map (homOfLE hle').op).hom t) := by
    have := (X'.toRingedSpace.isUnit_res_basicOpen t).map (X'.presheaf.map (homOfLE hsub).op).hom
    convert this using 1
    change _ = (X'.presheaf.map (homOfLE (X'.basicOpen_le t)).op ≫ X'.presheaf.map (homOfLE hsub).op).hom t
    rw [← Functor.map_comp]
    rfl
  refine ⟨W', hunit.unit, inf_le_left.trans hle0, hx', fun z hz => ?_⟩
  have hle2 : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) :=
    i'.preimage_mono (p.preimage_mono (inf_le_left.trans hle0))
  rw [← gm_id_pull i' z (p ⁻¹ᵁ W') hz, ← gm_res (𝟙 Z') z hle2 hz]
  congr 1
  apply Units.ext
  show (i'.app (p ⁻¹ᵁ W')).hom ((X'.presheaf.map (homOfLE hle').op).hom t) =
    (Z'.presheaf.map (homOfLE hle2).op).hom u.val
  have e := congrArg (fun φ => φ.hom t) (i'.naturality (homOfLE hle').op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
  rw [e, ht]
  show (Z'.presheaf.map _).hom ((Z'.presheaf.map _).hom u.val) = _
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → ∀ (W : X.Opens) (x : X), x ∈ W → ∀ u : Γ(Z', i' ⁻¹ᵁ (p ⁻¹ᵁ W))ˣ, ∃ (W' : X.Opens) (u' : Γ(X', p ⁻¹ᵁ W')ˣ), W' ≤ W ∧ x ∈ W' ∧ ∀ z : Z', p (i' z) ∈ W' → gm i' z (p ⁻¹ᵁ W') u' = gm (𝟙 Z') z (i' ⁻¹ᵁ (p ⁻¹ᵁ W)) u := by
  atlas_forward_decl GlobalTheory.Pinch.unit_lift_near_fibre
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem exists_affine_basicOpen_nbhd : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i →
    IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O →
    ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  intro B' C Y i q hi hq hB y O hO hyO
  have hF : (q ⁻¹' {q y}).Finite := q.finite_preimage_singleton (q y)
  classical
  obtain ⟨V₀, hV₀, hFV₀⟩ := hB ((hF.image i).toFinset)
  have hY₀ : IsAffineOpen (i ⁻¹ᵁ V₀) := hV₀.preimage i
  obtain ⟨h, hFh, hhO⟩ := GlobalTheory.exists_basicOpen_le_of_finite hY₀ (q ⁻¹ᵁ O) hF
    (fun x hx ↦ hFV₀ _ (by simpa using ⟨x, hx, rfl⟩)) (fun x hx ↦ by
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx; simp [hx, hyO])
  have hcl : IsClosed (q '' (Y.basicOpen h : Set Y)ᶜ) :=
    q.isClosedMap _ (Y.basicOpen h).isOpen.isClosed_compl
  have hyW : q y ∉ q '' (Y.basicOpen h : Set Y)ᶜ := by
    rintro ⟨x, hx, hxy⟩
    exact hx (hFh (by simpa using hxy))
  let W : C.Opens := ⟨(q '' (Y.basicOpen h : Set Y)ᶜ)ᶜ, hcl.isOpen_compl⟩
  obtain ⟨r, hrW, hyr⟩ := hO.exists_basicOpen_le (V := W) ⟨q y, hyW⟩ hyO
  have hle : q ⁻¹ᵁ C.basicOpen r ≤ Y.basicOpen h := by
    intro x hx
    by_contra hxh
    exact hrW hx ⟨x, hxh, rfl⟩
  have hbo : q ⁻¹ᵁ C.basicOpen r = Y.basicOpen (q.app O r) := Scheme.preimage_basicOpen q r
  obtain ⟨f', hf'⟩ := hY₀.basicOpen_basicOpen_is_basicOpen h
    (Y.presheaf.map (homOfLE hhO).op (q.app O r))
  rw [Scheme.basicOpen_res, ← hbo, inf_eq_right.mpr hle] at hf'
  obtain ⟨t, ht⟩ := i.app_surjective V₀ hV₀ f'
  refine ⟨B'.basicOpen t, r, hV₀.basicOpen t, ?_, ?_⟩
  · have : y ∈ i ⁻¹ᵁ B'.basicOpen t := by
      rw [Scheme.preimage_basicOpen, ht, hf']; exact hyr
    exact this
  · rw [Scheme.preimage_basicOpen, ht, hf']

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage : ∀ (B' C Y : Scheme.{0}) (i : Y ⟶ B') (q : Y ⟶ C), IsClosedImmersion i → IsFinite q → FinAff B' → ∀ (y : Y) (O : C.Opens), IsAffineOpen O → q y ∈ O → ∃ (V' : B'.Opens) (r : Γ(C, O)), IsAffineOpen V' ∧ i y ∈ V' ∧ i ⁻¹ᵁ V' = q ⁻¹ᵁ (C.basicOpen r) := by
  atlas_forward_decl GlobalTheory.Pinch.exists_affine_basicOpen_nbhd
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.Pinch

theorem appTop_ι_comp_eq {C Z : Scheme.{0}} (e : C ⟶ Z) (U : C.Opens) :
    (U.ι ≫ e).appTop = e.appLE ⊤ U le_top ≫ U.topIso.inv := by
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso, Scheme.Hom.comp_appTop, Scheme.Opens.ι_app]
  simp [← Functor.map_comp]

theorem exists_affine_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z),
    SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧
      ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  intro g C Z _ e he x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) e he
    ⟨⊤, isAffineOpen_top Z⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨t, ht⟩, hxt⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen t
  have h1 := h' t ht Γ(C, C.basicOpen t)
  refine ⟨C.basicOpen t, hW.basicOpen t, hxt, fun r => ?_⟩
  have hl2 := (hW.basicOpen t).isLocalization_basicOpen r
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).right
    Γ(C, C.basicOpen r) r _ h1
  have h3 : (e.appLE ⊤ (C.basicOpen r) le_top).hom.IsStandardSmoothOfRelativeDimension g := by
    convert h2 using 1
    ext a
    change _ = (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) ((C.presheaf.map (homOfLE (C.basicOpen_le t)).op) _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map]
  rw [appTop_ι_comp_eq, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (C.basicOpen r).topIso.symm.commRingCatIsoToRingEquiv h3

end GlobalTheory.Pinch
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z), SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧ ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  atlas_forward_decl GlobalTheory.Pinch.exists_affine_basicOpen_standardSmooth
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.Pinch

theorem restrict_pinched : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  intro g S S' Z B' C Y s' z b' e i q h₁ h₂ V' V hV
  refine ⟨(Y.isoOfEq hV).hom ≫ (q ∣_ V), ?_, ?_, ?_⟩
  · have hq : ((Y.isoOfEq hV).hom ≫ (q ∣_ V)) ≫ V.ι ≫ e = (i ⁻¹ᵁ V').ι ≫ q ≫ e := by
      simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_hom_ι_assoc]
    rw [hq, Category.assoc]
    exact (isPullback_morphismRestrict i V').paste_vert h₁
  · have P := (isPullback_morphismRestrict q V).paste_vert h₂
    refine IsPullback.of_iso P (Y.isoOfEq hV).symm (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp
    · simp [morphismRestrict_ι_assoc, Scheme.isoOfEq_inv_ι_assoc]
    · simp
    · simp
  · intro x hx
    obtain ⟨U, U', W₀, u, p, j, n, k, hu, hp, hj, hx, hn, hl⟩ := hx
    refine ⟨U, U', W₀, u, p, j ≫ V'.ι, n, k ≫ V.ι, hu, by simpa using hp, inferInstance, ?_, by simpa using hn, ?_⟩
    · obtain ⟨w, rfl⟩ := hx
      exact ⟨w, rfl⟩
    · intro T a a' haa
      obtain ⟨y, hy₁, hy₂⟩ := hl T a a' haa
      refine ⟨y ≫ (i ⁻¹ᵁ V').ι, ?_, ?_⟩
      · rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, hy₁, Category.assoc]
      · have hq : (Y.isoOfEq hV).hom ≫ (q ∣_ V) ≫ V.ι = (i ⁻¹ᵁ V').ι ≫ q := by
          simp [morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
        rw [Category.assoc, ← hq, reassoc_of% hy₂]

end GlobalTheory.Pinch
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pinched_charts_restrict_matching_opens : ∀ (g : ℕ) (S S' Z B' C Y : Scheme.{0}) (s' : S' ⟶ S) (z : Z ⟶ S) (b' : B' ⟶ S') (e : C ⟶ Z) (i : Y ⟶ B') (q : Y ⟶ C), IsPullback i (q ≫ e) (b' ≫ s') z → IsPullback q (i ≫ b') (e ≫ z) s' → ∀ (V' : B'.Opens) (V : C.Opens), i ⁻¹ᵁ V' = q ⁻¹ᵁ V → ∃ (q₀ : (i ⁻¹ᵁ V').toScheme ⟶ V.toScheme), IsPullback (i ∣_ V') (q₀ ≫ V.ι ≫ e) ((V'.ι ≫ b') ≫ s') z ∧ IsPullback q₀ ((i ∣_ V') ≫ V'.ι ≫ b') ((V.ι ≫ e) ≫ z) s' ∧ ∀ x : V'.toScheme, GlobalTheory.Pinch.Pinched g s' z (V'.ι ≫ b') (V.ι ≫ e) (i ∣_ V') q₀ x → GlobalTheory.Pinch.Pinched g s' z b' e i q (V'.ι x) := by
  atlas_forward_decl GlobalTheory.Pinch.restrict_pinched
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pushout_quotient_map_eq_quotient_map_ideal : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  intro R C E _ _ _ c f π χ h
  have hw' : ∀ r, π (f r) = χ (Ideal.Quotient.mk c r) := fun r => by
    have := congrArg (fun g => g.hom r) h.w
    simpa using this
  have hle : c.map f ≤ RingHom.ker π := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    simp [RingHom.mem_ker, hw', Ideal.Quotient.eq_zero_iff_mem.mpr hr]
  let q : C →+* C ⧸ c.map f := Ideal.Quotient.mk _
  let qm : R ⧸ c →+* C ⧸ c.map f := Ideal.quotientMap (c.map f) f Ideal.le_comap_map
  let φ : C ⧸ c.map f →+* E := Ideal.Quotient.lift _ π (fun x hx => hle hx)
  have hcomm : CommRingCat.ofHom f ≫ CommRingCat.ofHom q =
      CommRingCat.ofHom (Ideal.Quotient.mk c) ≫ CommRingCat.ofHom qm := by
    ext r; rfl
  let ψ := h.desc (CommRingCat.ofHom q) (CommRingCat.ofHom qm) hcomm
  have h1 : CommRingCat.ofHom π ≫ ψ = CommRingCat.ofHom q := h.inl_desc _ _ _
  have h2 : CommRingCat.ofHom χ ≫ ψ = CommRingCat.ofHom qm := h.inr_desc _ _ _
  have hid : ψ ≫ CommRingCat.ofHom φ = 𝟙 _ := by
    apply h.hom_ext
    · rw [← Category.assoc, h1, Category.comp_id]
      ext x; rfl
    · rw [← Category.assoc, h2, Category.comp_id]
      ext r
      change φ (qm (Ideal.Quotient.mk c r)) = χ (Ideal.Quotient.mk c r)
      rw [← hw']
      rfl
  have hφsurj : Function.Surjective φ := fun e =>
    ⟨ψ e, by
      have := congrArg (fun g => g.hom e) hid
      simpa using this⟩
  refine ⟨?_, ?_⟩
  · intro e
    obtain ⟨y, hy⟩ := hφsurj e
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact ⟨x, hy⟩
  · refine le_antisymm ?_ hle
    intro x hx
    have hx1 : ψ.hom (π x) = q x := by
      rw [← CommRingCat.hom_ofHom q, ← h1]; rfl
    rw [RingHom.mem_ker] at hx
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    change q x = 0
    rw [← hx1, hx, map_zero]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushout_quotient_surjective_ker_eq_map : ∀ (R C E : Type) [CommRing R] [CommRing C] [CommRing E] (c : Ideal R) (f : R →+* C) (π : C →+* E) (χ : R ⧸ c →+* E), IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom χ) → Function.Surjective π ∧ RingHom.ker π = c.map f := by
  atlas_forward_decl GlobalTheory.pushout_quotient_map_eq_quotient_map_ideal
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchEnl

open MvPolynomial

theorem ker_aeval_zero_eq_span (D κ : Type) [CommRing D] :
    RingHom.ker (aeval (R := D) (fun _ : κ ↦ (0 : D))) = Ideal.span (Set.range X) := by
  apply le_antisymm
  · intro p hp
    rw [← Set.image_univ, MvPolynomial.mem_ideal_span_X_image]
    intro m hm
    by_contra h
    push_neg at h
    have hm0 : m = 0 := by ext i; simpa using h i (Set.mem_univ i)
    subst hm0
    rw [RingHom.mem_ker] at hp
    have : aeval (R := D) (fun _ : κ ↦ (0 : D)) p = coeff 0 p := by
      first
        | (show MvPolynomial.eval (0 : κ → D) p = _
           exact congrFun (congrArg DFunLike.coe (MvPolynomial.eval_zero (R := D) (σ := κ))) p)
        | (rw [MvPolynomial.aeval_def]; simp [MvPolynomial.eval₂_eq, MvPolynomial.coeff_zero_eq_constantCoeff])
    exact (mem_support_iff.mp hm) (this ▸ hp)
  · rw [Ideal.span_le]
    rintro _ ⟨k, rfl⟩
    simp

noncomputable def zeroPre (D κ : Type) [CommRing D] :
    Algebra.PreSubmersivePresentation D D κ κ where
  val _ := 0
  σ' x := C x
  aeval_val_σ' x := by simp
  relation k := X k
  span_range_relation_eq_ker := by
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    exact (ker_aeval_zero_eq_span D κ).symm
  map := id
  map_inj := Function.injective_id

theorem zeroPre_jacobian (D κ : Type) [CommRing D] [Finite κ] : (zeroPre D κ).jacobian = 1 := by
  classical
  have : Fintype κ := Fintype.ofFinite κ
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  have h1 : (zeroPre D κ).jacobiMatrix = 1 := by
    ext i j
    rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
    simp [zeroPre, Matrix.one_apply, pderiv_X, Pi.single_apply, eq_comm]
  rw [h1]
  simp

end GlobalTheory.PinchEnl

theorem GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  intro R D ν σ κ _ _ _ _ _ _ P
  let Q : Algebra.SubmersivePresentation D D κ κ :=
    { __ := GlobalTheory.PinchEnl.zeroPre D κ
      jacobian_isUnit := by rw [GlobalTheory.PinchEnl.zeroPre_jacobian]; exact isUnit_one }
  refine ⟨Q.comp P, ?_⟩
  ext i
  rcases i with k | j
  · rfl
  · rfl
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_submersivePresentation_add_zero_variables : ∀ (R D ν σ κ : Type) [CommRing R] [CommRing D] [Algebra R D] [Finite ν] [Finite σ] [Finite κ] (P : Algebra.SubmersivePresentation R D ν σ), ∃ P' : Algebra.SubmersivePresentation R D (κ ⊕ ν) (κ ⊕ σ), P'.val = Sum.elim (fun _ ↦ 0) P.val := by
  atlas_forward_decl GlobalTheory.PinchEnl.exists_submersivePresentation_sum_zero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pinch_gens_adapted : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  intro R R₀ R' C' D E ν _ _ _ _ _ _ _ _ _ a m π ψ ζ hm hπ hζ po
  choose ξ₀ hξ₀ using fun s => hπ (ψ (ζ s))
  have hcomm : ψ.comp ((algebraMap R₀ D).comp m) = (π.comp (algebraMap R' C')).comp a := by
    have := po.w
    exact congrArg CommRingCat.Hom.hom this
  have hsurj : Function.Surjective (π.comp (MvPolynomial.aeval ξ₀ : MvPolynomial ν R' →ₐ[R'] C').toRingHom) := by
    rw [← RingHom.range_eq_top, ← top_le_iff,
      ← CommRingCat.closure_range_union_range_eq_top_of_isPushout po, Subring.closure_le]
    rintro _ (⟨d, rfl⟩ | ⟨r, rfl⟩)
    · obtain ⟨f, rfl⟩ := hζ d
      obtain ⟨g, rfl⟩ := MvPolynomial.map_surjective m hm f
      refine ⟨MvPolynomial.map a g, ?_⟩
      simp only [CommRingCat.hom_ofHom, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      induction g using MvPolynomial.induction_on with
      | C c =>
        have := congrArg (fun h => h c) hcomm
        simpa using this.symm
      | add p q hp hq => simp [hp, hq]
      | mul_X p s hp => simp [hp, hξ₀]
    · exact ⟨MvPolynomial.C r, by simp⟩
  obtain ⟨S, hS⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra R' C').FG)
  choose p hp using fun t : S => hsurj (π t)
  refine ⟨S, inferInstance, Sum.elim (fun t => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀, ?_, ?_⟩
  · rintro (t | s)
    · have := hp t
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      simp [map_sub, this]
    · simp [hξ₀]
  · intro x
    have hx : x ∈ Algebra.adjoin R' (S : Set C') := by rw [hS]; trivial
    have hle : Algebra.adjoin R' (S : Set C') ≤
        (MvPolynomial.aeval (Sum.elim (fun t : S => (t : C') - MvPolynomial.aeval ξ₀ (p t)) ξ₀) :
          MvPolynomial (S ⊕ ν) R' →ₐ[R'] C').range := by
      rw [Algebra.adjoin_le_iff]
      intro t ht
      refine ⟨MvPolynomial.X (Sum.inl ⟨t, ht⟩) + MvPolynomial.rename Sum.inr (p ⟨t, ht⟩), ?_⟩
      simp [MvPolynomial.aeval_rename, Function.comp_def]
    obtain ⟨y, hy⟩ := hle hx
    exact ⟨y, hy⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generators_adapted_to_quotient_generators : ∀ (R R₀ R' C' D E ν : Type) [CommRing R] [CommRing R₀] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R' C'] [Algebra.FiniteType R' C'] [Algebra R₀ D] (a : R →+* R') (m : R →+* R₀) (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D), Function.Surjective m → Function.Surjective π → Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν R₀ →ₐ[R₀] D) → IsPushout (CommRingCat.ofHom ((algebraMap R₀ D).comp m)) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp (algebraMap R' C'))) → ∃ (κ : Type) (_ : Finite κ) (ξ : κ ⊕ ν → C'), (∀ s, π (ξ s) = ψ (Sum.elim (fun _ ↦ 0) ζ s)) ∧ Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial (κ ⊕ ν) R' →ₐ[R'] C') := by
  atlas_forward_decl GlobalTheory.pinch_gens_adapted
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem relations_lift_vanishing : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  intro hH R R' C' D E ν _ _ _ _ _ _ _ c _ hc π ψ ζ ξ hker hcomm hξ hsurj f hf
  obtain ⟨F₀, rfl⟩ := MvPolynomial.map_surjective (Ideal.Quotient.mk c) Ideal.Quotient.mk_surjective f
  have hπ : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀)) = 0 := by
    have h1 : π (MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀))
        = ψ (MvPolynomial.aeval ζ (MvPolynomial.map (Ideal.Quotient.mk c) F₀)) := by
      rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_map, MvPolynomial.eval₂_map,
        MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_comp_left, ← RingHom.comp_assoc, hcomm]
      congr 1
      funext s
      exact hξ s
    rw [h1, hf, map_zero]
  have hmem : MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F₀) ∈
      ((c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R')).map
        (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') := by
    rw [Ideal.map_map]
    change _ ∈ Ideal.map ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C') _
    rw [Ideal.map_map]
    have : ((MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') : MvPolynomial ν R' →+* C').comp
        ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp (algebraMap R R'))
        = (algebraMap R' C').comp (algebraMap R R') := by
      ext x; simp
    rw [this, ← hker]
    exact hπ
  obtain ⟨G, hG, hGe⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hmem
  obtain ⟨H, hH0, hHG⟩ := hH R R' ν c hc G hG
  refine ⟨F₀ - H, ?_, ?_⟩
  · rw [map_sub, hH0, sub_zero]
  · rw [map_sub, hHG, map_sub, hGe, sub_self]

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_relations_lift_vanishing_conductor : (∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G) → ∀ (R R' C' D E ν : Type) [CommRing R] [CommRing R'] [CommRing C'] [CommRing D] [CommRing E] [Algebra R R'] [Algebra R' C'] (c : Ideal R) [Algebra (R ⧸ c) D], (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (π : C' →+* E) (ψ : D →+* E) (ζ : ν → D) (ξ : ν → C'), RingHom.ker π = c.map ((algebraMap R' C').comp (algebraMap R R')) → ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) = (π.comp (algebraMap R' C')).comp (algebraMap R R') → (∀ s, π (ξ s) = ψ (ζ s)) → Function.Surjective (MvPolynomial.aeval ξ : MvPolynomial ν R' →ₐ[R'] C') → ∀ f : MvPolynomial ν (R ⧸ c), MvPolynomial.aeval ζ f = 0 → ∃ F : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) F = f ∧ MvPolynomial.aeval ξ (MvPolynomial.map (algebraMap R R') F) = 0 := by
  atlas_forward_decl GlobalTheory.Pinch.relations_lift_vanishing
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PinchKernel

theorem mem_span_of_eval_eq_zero (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E]
    (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D)
    (F : σ → MvPolynomial ν R)
    (hsurj : Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D))
    (hker : RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)))
    (hpo : IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)))
      (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ))
    (G : MvPolynomial ν R') (hG : MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0) :
    G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  classical
  set J : Ideal (MvPolynomial ν R') := Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔
      (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') with hJ
  let mkJ : MvPolynomial ν R' →+* MvPolynomial ν R' ⧸ J := Ideal.Quotient.mk J
  have hc : ∀ r ∈ c, (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) r = 0 := by
    intro r hr
    simp only [RingHom.comp_apply, mkJ]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hr))
  let base : R ⧸ c →+* MvPolynomial ν R' ⧸ J :=
    Ideal.Quotient.lift c (mkJ.comp ((MvPolynomial.C : R' →+* MvPolynomial ν R').comp a)) hc
  let φ : MvPolynomial ν (R ⧸ c) →+* MvPolynomial ν R' ⧸ J :=
    MvPolynomial.eval₂Hom base (fun s ↦ mkJ (MvPolynomial.X s))
  have hφC : ∀ r : R, φ (MvPolynomial.C (Ideal.Quotient.mk c r)) = mkJ (MvPolynomial.C (a r)) := by
    intro r
    simp [φ, base]
  have hφmap : ∀ P : MvPolynomial ν R,
      φ (MvPolynomial.map (Ideal.Quotient.mk c) P) = mkJ (MvPolynomial.map a P) := by
    intro P
    have h : φ.comp (MvPolynomial.map (Ideal.Quotient.mk c)) = mkJ.comp (MvPolynomial.map a) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply, MvPolynomial.map_C]
        exact hφC r
      · intro s
        simp [φ]
    exact RingHom.congr_fun h P
  let q : MvPolynomial ν (R ⧸ c) →+* D := (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D)
  have hkerφ : RingHom.ker q ≤ RingHom.ker φ := by
    have hq : RingHom.ker q = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) := by
      rw [← hker]; rfl
    rw [hq, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    rw [SetLike.mem_coe, RingHom.mem_ker, hφmap, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨s, rfl⟩)
  let dA : D →+* MvPolynomial ν R' ⧸ J :=
    q.liftOfRightInverse (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨φ, hkerφ⟩
  have hdA : ∀ p, dA (q p) = φ p := fun p =>
    RingHom.liftOfRightInverse_comp_apply q _ _ ⟨φ, hkerφ⟩ p
  have hqX : ∀ s, q (MvPolynomial.X s) = ζ s := fun s => by simp [q]
  have hqC : ∀ x : R ⧸ c, q (MvPolynomial.C x) = algebraMap (R ⧸ c) D x := fun x => by
    simp [q]
  have w : CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) ≫ CommRingCat.ofHom dA =
      CommRingCat.ofHom a ≫ CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R')) := by
    ext r
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply]
    rw [← hqC, hdA, hφC]
  let desc := hpo.desc (CommRingCat.ofHom dA) (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w
  have hinl : ∀ x : D, desc.hom (ψ x) = dA x := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inl_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hinr : ∀ x : R', desc.hom (χ x) = mkJ (MvPolynomial.C x) := fun x => by
    have := congrArg (fun f => f.hom x) (hpo.inr_desc (CommRingCat.ofHom dA)
      (CommRingCat.ofHom (mkJ.comp (MvPolynomial.C : R' →+* MvPolynomial ν R'))) w)
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at this
    exact this
  have hΦ : desc.hom.comp (MvPolynomial.eval₂Hom χ (fun s ↦ ψ (ζ s))) = mkJ := by
    apply MvPolynomial.ringHom_ext
    · intro x
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_C]
      exact hinr x
    · intro s
      simp only [RingHom.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [hinl, ← hqX, hdA]
      simp [φ]
  have h0 : mkJ G = 0 := by
    rw [← hΦ, RingHom.comp_apply, MvPolynomial.coe_eval₂Hom, hG, map_zero]
  exact (Ideal.Quotient.eq_zero_iff_mem).1 h0

end GlobalTheory.PinchKernel
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero : ∀ (R R' D E ν σ : Type) [CommRing R] [CommRing R'] [CommRing D] [CommRing E] (a : R →+* R') (c : Ideal R) [Algebra (R ⧸ c) D] (χ : R' →+* E) (ψ : D →+* E) (ζ : ν → D) (F : σ → MvPolynomial ν R), Function.Surjective (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) → RingHom.ker (MvPolynomial.aeval ζ : MvPolynomial ν (R ⧸ c) →ₐ[R ⧸ c] D) = Ideal.span (Set.range fun s ↦ MvPolynomial.map (Ideal.Quotient.mk c) (F s)) → IsPushout (CommRingCat.ofHom ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom a) (CommRingCat.ofHom ψ) (CommRingCat.ofHom χ) → ∀ G : MvPolynomial ν R', MvPolynomial.eval₂ χ (fun s ↦ ψ (ζ s)) G = 0 → G ∈ Ideal.span (Set.range fun s ↦ MvPolynomial.map a (F s)) ⊔ (c.map a).map (MvPolynomial.C : R' →+* MvPolynomial ν R') := by
  atlas_forward_decl GlobalTheory.PinchKernel.mem_span_of_eval_eq_zero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem mem_map_mul_ker_of_flat {R' A C' : Type} [CommRing R'] [CommRing A] [CommRing C']
    [Algebra R' A] [Algebra R' C'] [Module.Flat R' C'] (f : A →ₐ[R'] C')
    (hf : Function.Surjective f) (J : Ideal R') {x : A}
    (hx : x ∈ J.map (algebraMap R' A)) (hfx : f x = 0) :
    x ∈ J.map (algebraMap R' A) * RingHom.ker f := by
  rw [Ideal.map, Ideal.span, Submodule.mem_span_set'] at hx
  obtain ⟨n, c, g, rfl⟩ := hx
  have hg : ∀ i, ∃ j ∈ J, algebraMap R' A j = (g i : A) := fun i => (g i).2
  choose j hjJ hjg using hg
  have hsum : ∑ i, j i • f (c i) = 0 := by
    rw [← hfx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, map_mul, AlgHom.commutes, Algebra.smul_def, _root_.mul_comm]
  obtain ⟨k, a, y, hy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero (R := R') (M := C') (f := j)
    (x := fun i => f (c i)) hsum
  choose z hz using fun l => hf (y l)
  have hd : ∀ i, c i - ∑ l, a i l • z l ∈ RingHom.ker f := by
    intro i
    rw [RingHom.mem_ker]
    change f (c i - ∑ l, a i l • z l) = 0
    rw [map_sub, map_sum]
    simp only [map_smul, hz]
    rw [← hy i, sub_self]
  have h0 : ∑ i, algebraMap R' A (j i) * ∑ l, a i l • z l = 0 := by
    have hl : ∀ l, ∑ i, algebraMap R' A (j i) * (a i l • z l) = 0 := by
      intro l
      have : ∑ i, algebraMap R' A (j i) * (a i l • z l) = (∑ i, j i * a i l) • z l := by
        rw [Finset.sum_smul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, _root_.mul_assoc]
      rw [this, ha l, zero_smul]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun l _ => hl l
  have key : ∑ i, c i • (g i : A) =
      ∑ i, algebraMap R' A (j i) * (c i - ∑ l, a i l • z l) := by
    simp only [mul_sub, Finset.sum_sub_distrib, h0, sub_zero]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul, ← hjg i, _root_.mul_comm]
  rw [key]
  exact Ideal.sum_mem _ fun i _ => Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ (hjJ i)) (hd i)

theorem exists_sub_one_mem_mul_ker_le :
    ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C']
      [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f →
      ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f →
        RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) →
          ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  intro R' A C' _ _ _ _ _ _ _ f hf I J hI hK
  have hle : RingHom.ker f ≤ I ⊔ (J.map (algebraMap R' A)) • RingHom.ker f := by
    intro G hG
    obtain ⟨i, hi, x, hx, rfl⟩ := Submodule.mem_sup.1 (hK hG)
    have hfx : f x = 0 := by
      have h1 : f (i + x) = 0 := hG
      have h2 : f i = 0 := hI hi
      rw [map_add, h2, zero_add] at h1
      exact h1
    exact Submodule.add_mem_sup hi (mem_map_mul_ker_of_flat f hf J hx hfx)
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup
    (IsNoetherian.noetherian (RingHom.ker f)) le_rfl hle
  refine ⟨r, hr1, fun G hG => ?_⟩
  exact hr (Submodule.smul_mem_pointwise_smul G r _ hG)

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat : ∀ (R' A C' : Type) [CommRing R'] [CommRing A] [CommRing C'] [Algebra R' A] [Algebra R' C'] [IsNoetherianRing A] [Module.Flat R' C'] (f : A →ₐ[R'] C'), Function.Surjective f → ∀ (I : Ideal A) (J : Ideal R'), I ≤ RingHom.ker f → RingHom.ker f ≤ I ⊔ J.map (algebraMap R' A) → ∃ s : A, s - 1 ∈ J.map (algebraMap R' A) ∧ ∀ G ∈ RingHom.ker f, s * G ∈ I := by
  atlas_forward_decl GlobalTheory.Pinch.exists_sub_one_mem_mul_ker_le
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_mvPolynomial_lift_of_mem_conductor :
    ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  intro R R' ν _ _ _ c hc G hG
  have key : ∀ z ∈ c.map (algebraMap R R'), ∃ y ∈ c, algebraMap R R' y = z := by
    intro z hz
    refine Submodule.span_induction (p := fun z _ => ∃ y ∈ c, algebraMap R R' y = z)
      ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hy, rfl⟩
    · exact ⟨0, c.zero_mem, map_zero _⟩
    · rintro _ _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, c.add_mem ha hb, map_add _ _ _⟩
    · rintro r _ _ ⟨a, ha, rfl⟩
      obtain ⟨y, hy, h⟩ := hc a ha r
      exact ⟨y, hy, by rw [h, smul_eq_mul, mul_comm]⟩
  rw [MvPolynomial.mem_map_C_iff] at hG
  choose y hy hyG using fun m => key _ (hG m)
  refine ⟨∑ m ∈ G.support, MvPolynomial.monomial m (y m), ?_, ?_⟩
  · rw [map_sum]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [MvPolynomial.map_monomial, Ideal.Quotient.eq_zero_iff_mem.mpr (hy m), map_zero]
  · rw [map_sum]
    conv_rhs => rw [G.as_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.map_monomial, hyG]

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs : ∀ (R R' ν : Type) [CommRing R] [CommRing R'] [Algebra R R'] (c : Ideal R), (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ G ∈ (c.map (algebraMap R R')).map (MvPolynomial.C : R' →+* MvPolynomial ν R'), ∃ H : MvPolynomial ν R, MvPolynomial.map (Ideal.Quotient.mk c) H = 0 ∧ MvPolynomial.map (algebraMap R R') H = G := by
  atlas_forward_decl GlobalTheory.exists_mvPolynomial_lift_of_mem_conductor
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

theorem isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
    (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν)
    (hm : Function.Injective m) (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R)
    (hdvd : (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h) :
    Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  classical
  set A := MvPolynomial ν R ⧸ Ideal.span (Set.range F)
  set T := Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  let P := Algebra.PreSubmersivePresentation.naive (v := F) m hm
  let Q := Algebra.SubmersivePresentation.localizationAway T
    (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)
  have hPjac : P.jacobian = Ideal.Quotient.mk (Ideal.span (Set.range F))
      (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det := by
    rw [P.jacobian_eq_jacobiMatrix_det, Algebra.Generators.algebraMap_apply]
    have hM : P.jacobiMatrix = Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t) := by
      ext i j
      simp [P]
    rw [hM]
    have : MvPolynomial.aeval P.val = Ideal.Quotient.mkₐ R (Ideal.span (Set.range F)) :=
      MvPolynomial.algHom_ext fun v => by simp [P]
    rw [this]
    rfl
  let P' : Algebra.SubmersivePresentation R T (Unit ⊕ ν) (Unit ⊕ σ) :=
    { __ := Q.toPreSubmersivePresentation.comp P
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian,
          Algebra.smul_def]
        refine IsUnit.mul ?_ Q.jacobian_isUnit
        rw [hPjac]
        exact isUnit_of_dvd_unit (map_dvd _ (map_dvd _ hdvd))
          (IsLocalization.Away.algebraMap_isUnit _) }
  refine P'.isStandardSmoothOfRelativeDimension ?_
  change (Q.toPreSubmersivePresentation.comp P).dimension = _
  rw [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension]
  simp [Algebra.Presentation.dimension, P]

end GlobalTheory.Pinch
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd : ∀ (R ν σ : Type) [CommRing R] [Finite ν] [Fintype σ] [DecidableEq σ] (m : σ → ν), Function.Injective m → ∀ (F : σ → MvPolynomial ν R) (h : MvPolynomial ν R), (Matrix.of fun s t : σ ↦ MvPolynomial.pderiv (m s) (F t)).det ∣ h → Algebra.IsStandardSmoothOfRelativeDimension (Nat.card ν - Nat.card σ) R (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range F)) h)) := by
  atlas_forward_decl GlobalTheory.Pinch.isStandardSmoothOfRelativeDimension_localizationAway_of_det_dvd
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Pinch

open MvPolynomial in

theorem exists_standardSmooth : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∃ (F : Type) (_ : CommRing F) (ε : R →+* F) (t : C') (α : F →+* Localization.Away t) (β : F →+* D) (τ : Localization.Away t →+* E), ε.IsStandardSmoothOfRelativeDimension g ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom α) (CommRingCat.ofHom ((algebraMap C' (Localization.Away t)).comp φ)) ∧ IsPushout (CommRingCat.ofHom ε) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom β) (CommRingCat.ofHom δ) ∧ τ.comp (algebraMap C' (Localization.Away t)) = π ∧ τ.comp α = ψ.comp β := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2
  classical
  letI : Algebra R' C' := φ.toAlgebra
  letI : Algebra (R ⧸ c) D := δ.toAlgebra
  haveI : Algebra.Smooth R' C' := hφ
  haveI : IsNoetherianRing R' := IsNoetherianRing.of_finite R R'
  obtain ⟨ν₀, σ₀, _, _, P₀, hP₀⟩ := (show Algebra.IsStandardSmoothOfRelativeDimension g (R ⧸ c) D from hδ).out
  obtain ⟨hπ, hker⟩ := GlobalTheory.T.pushout_quotient_surjective_ker_eq_map R C' E c _ π _ h1
  obtain ⟨κ, _, ξ, hξ, hsurj⟩ := GlobalTheory.T.exists_generators_adapted_to_quotient_generators R (R ⧸ c) R' C' D E ν₀ (algebraMap R R') (Ideal.Quotient.mk c) π ψ P₀.val
    Ideal.Quotient.mk_surjective hπ P₀.aeval_val_surjective h2
  obtain ⟨P, hP⟩ := GlobalTheory.T.exists_submersivePresentation_add_zero_variables (R ⧸ c) D ν₀ σ₀ κ P₀
  rw [← hP] at hξ
  have hw : ψ.comp ((algebraMap (R ⧸ c) D).comp (Ideal.Quotient.mk c)) =
      (π.comp (algebraMap R' C')).comp (algebraMap R R') := congrArg CommRingCat.Hom.hom h2.w
  choose F hF hF0 using fun s ↦ GlobalTheory.T.exists_relations_lift_vanishing_conductor GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' C' D E _ c hc π ψ P.val ξ hker hw hξ hsurj (P.relation s)
    (P.aeval_val_relation s)
  have hrel : (fun s ↦ map (Ideal.Quotient.mk c) (F s)) = P.relation := funext hF
  have hkP : RingHom.ker (aeval P.val : MvPolynomial _ (R ⧸ c) →ₐ[R ⧸ c] D) =
      Ideal.span (Set.range fun s ↦ map (Ideal.Quotient.mk c) (F s)) := by
    rw [hrel, P.span_range_relation_eq_ker, P.ker_eq_ker_aeval_val]
  have key : ∀ G : MvPolynomial (κ ⊕ ν₀) R', π (aeval ξ G) = eval₂ (π.comp φ) (fun s ↦ ψ (P.val s)) G := fun G ↦ by
    rw [aeval_def, eval₂_comp_left]
    exact congrArg (fun v ↦ eval₂ _ v G) (funext hξ)
  have key2 : ∀ G : MvPolynomial (κ ⊕ ν₀) R, π (aeval ξ (map (algebraMap R R') G)) =
      ψ (aeval P.val (map (Ideal.Quotient.mk c) G)) := fun G ↦ by
    rw [key, aeval_def, eval₂_comp_left, eval₂_map, eval₂_map]
    exact congrArg (fun f ↦ eval₂ f _ G) hw.symm
  obtain ⟨s', hs1, hs2⟩ := GlobalTheory.T.exists_sub_one_mem_mul_ker_nakayama_flat R' (MvPolynomial (κ ⊕ ν₀) R') C' (aeval ξ) hsurj
    (Ideal.span (Set.range fun s ↦ map (algebraMap R R') (F s))) (c.map (algebraMap R R'))
    (Ideal.span_le.2 (by rintro _ ⟨s, rfl⟩; exact hF0 s))
    (fun G hG ↦ GlobalTheory.T.mem_span_relations_conductor_of_eval_eq_zero R R' D E _ _ (algebraMap R R') c (π.comp φ) ψ P.val F P.aeval_val_surjective hkP h2 G
      (by rw [← key, show aeval ξ G = 0 from hG, map_zero]))
  obtain ⟨H, hH0, hH⟩ := GlobalTheory.T.exists_mvPolynomial_lift_conductor_coeffs R R' _ c hc _ hs1
  letI : Fintype (κ ⊕ σ₀) := Fintype.ofFinite _
  let Δ : MvPolynomial (κ ⊕ ν₀) R := (Matrix.of fun s t ↦ pderiv (P.map s) (F t)).det
  have hΔ : aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1))) = P.jacobian := by
    rw [map_mul, map_add, hH0, map_one, zero_add, _root_.mul_one, P.jacobian_eq_jacobiMatrix_det, P.algebraMap_apply,
      RingHom.map_det]
    congr 2
    ext1 s t
    rw [P.jacobiMatrix_apply, ← hF, pderiv_map]
    rfl
  have hu : IsUnit (aeval P.val (map (Ideal.Quotient.mk c) (Δ * (H + 1)))) := hΔ ▸ P.jacobian_isUnit
  obtain ⟨α, hα, hα'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R R' C' (Localization.Away (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) _ _
    (algebraMap R R') F (Δ * (H + 1)) ξ hsurj hF0 (fun G hG ↦ by
      rw [map_mul, map_add, hH, map_one, sub_add_cancel, _root_.mul_assoc]
      exact Ideal.mul_mem_left _ _ (hs2 G hG)) inferInstance
  obtain ⟨β, hβ, hβ'⟩ := GlobalTheory.T.isPushout_localized_presentation_baseChange R (R ⧸ c) D D _ _ (Ideal.Quotient.mk c) F (Δ * (H + 1)) P.val
    P.aeval_val_surjective (fun s ↦ by rw [hF]; exact P.aeval_val_relation s)
    (fun G hG ↦ Ideal.mul_mem_left _ _ (hkP ▸ hG)) (IsLocalization.away_of_isUnit_of_bijective _ hu Function.bijective_id)
  have ht : IsUnit (π (aeval ξ (map (algebraMap R R') (Δ * (H + 1))))) := by
    rw [key2]
    exact hu.map ψ
  refine ⟨_, inferInstance, algebraMap R _, _, α, β, IsLocalization.Away.lift _ ht, ?_, hα, hβ,
    IsLocalization.Away.lift_comp _ ht, ?_⟩
  · have := GlobalTheory.T.isStandardSmooth_localizationAway_jacobian_dvd R _ _ P.map P.map_inj F (Δ * (H + 1)) (dvd_mul_right _ _)
    have hd : Nat.card (κ ⊕ ν₀) - Nat.card (κ ⊕ σ₀) = g := by
      rw [← hP₀, Algebra.Presentation.dimension, Nat.card_sum, Nat.card_sum]
      omega
    rw [hd] at this
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap g).2 this
  · refine IsLocalization.ringHom_ext (Submonoid.powers (Ideal.Quotient.mk (Ideal.span (Set.range F)) (Δ * (H + 1)))) ?_
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun G ↦ ?_)
    simp only [RingHom.comp_apply]
    rw [hα', hβ', IsLocalization.Away.lift_eq, key2]
    rfl

theorem pinched_spec : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (C' D E : Type) [CommRing C'] [CommRing D] [CommRing E] (φ : R' →+* C') (δ : R ⧸ c →+* D) (π : C' →+* E) (ψ : D →+* E), φ.Smooth → δ.IsStandardSmoothOfRelativeDimension g → IsPushout (CommRingCat.ofHom (φ.comp (algebraMap R R'))) (CommRingCat.ofHom (Ideal.Quotient.mk c)) (CommRingCat.ofHom π) (CommRingCat.ofHom (ψ.comp δ)) → IsPushout (CommRingCat.ofHom (δ.comp (Ideal.Quotient.mk c))) (CommRingCat.ofHom (algebraMap R R')) (CommRingCat.ofHom ψ) (CommRingCat.ofHom (π.comp φ)) → ∀ y : Sp E, GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) (spMap φ) (spMap δ) (spMap π) (spMap ψ) (spMap π y) := by
  intro R _ _ R' _ _ _ hinj c hc g C' D E _ _ _ φ δ π ψ hφ hδ h1 h2 y
  obtain ⟨F, _, ε, t, α, β, τ, hε, k1, k2, e1, e2⟩ := exists_standardSmooth R R' hinj c hc g C' D E φ δ π ψ hφ hδ h1 h2
  have p1 := isPullback_SpecMap_of_isPushout _ _ _ _ h1
  have q1 := isPullback_SpecMap_of_isPushout _ _ _ _ k1
  have q2 := isPullback_SpecMap_of_isPushout _ _ _ _ k2
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hβ : IsClosedImmersion (spMap β) := MorphismProperty.of_isPullback q2.flip hcl
  have cmp : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (f' : B →+* C),
      spMap (f'.comp f) = spMap f' ≫ spMap f := fun f f' ↦ by
    rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  have hj : IsOpenImmersion (spMap (algebraMap C' (Localization.Away t))) := inferInstance
  have f1 : spMap τ ≫ spMap (algebraMap C' (Localization.Away t)) = spMap π := by rw [← cmp, e1]
  have f2 : spMap τ ≫ spMap α = spMap ψ ≫ spMap β := by rw [← cmp, ← cmp, e2]
  refine ⟨Sp F, Sp (Localization.Away t), Sp D, spMap ε, spMap α, spMap (algebraMap C' _), spMap β, 𝟙 _, ?_, ?_, hj,
    ⟨spMap τ y, ?_⟩, ?_, fun T a a' h ↦ ?_⟩
  · exact (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension g)).2
      (RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hε)
  · rw [← cmp]
    exact q1
  · rw [← Scheme.Hom.comp_apply, f1]
  · rw [Category.id_comp]
    exact q2
  · have w : (a ≫ spMap (algebraMap C' (Localization.Away t))) ≫ spMap (φ.comp (algebraMap R R')) =
        (a' ≫ spMap δ) ≫ spMap (Ideal.Quotient.mk c) := by
      have w1 : spMap α ≫ spMap ε = spMap ((algebraMap C' (Localization.Away t)).comp φ) ≫
        spMap (algebraMap R R') := q1.w
      have w2 : spMap β ≫ spMap ε = spMap δ ≫ spMap (Ideal.Quotient.mk c) := q2.w
      rw [Category.assoc, Category.assoc, ← w2, ← Category.assoc a', ← h, Category.assoc, w1, cmp (algebraMap R R') φ,
        cmp φ (algebraMap C' (Localization.Away t)), Category.assoc]
    have l1 : p1.lift _ _ w ≫ spMap π = _ := p1.lift_fst _ _ w
    refine ⟨p1.lift _ _ w, l1, ?_⟩
    have l2 : p1.lift _ _ w ≫ spMap τ = a := by
      rw [← cancel_mono (spMap (algebraMap C' (Localization.Away t))), Category.assoc, f1, l1]
    rw [Category.comp_id, ← cancel_mono (spMap β), Category.assoc, ← f2, ← Category.assoc, l2, h]

theorem pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → ∀ (g : ℕ) (B' C Y : Scheme.{0}) (b' : B' ⟶ Sp R') (e : C ⟶ Sp (R ⧸ c)) (i : Y ⟶ B') (q : Y ⟶ C), SmoothOfRelativeDimension g b' → SmoothOfRelativeDimension g e → FinAff B' → IsPullback i (q ≫ e) (b' ≫ spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) → IsPullback q (i ≫ b') (e ≫ spMap (Ideal.Quotient.mk c)) (spMap (algebraMap R R')) → ∀ x : B', GlobalTheory.Pinch.Pinched g (spMap (algebraMap R R')) (spMap (Ideal.Quotient.mk c)) b' e i q x := by
  intro R _ _ R' _ _ _ hinj c hc g B' C Y b' e i q hb he hF h1 h2 x
  by_cases hx : (b' ≫ spMap (algebraMap R R')) x ∈ Set.range (spMap (Ideal.Quotient.mk c))
  swap
  · exact GlobalTheory.T.pinched_chart_off_closed_part_from_base R R' hinj c hc g B' C Y b' e i q hb x hx
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨y, rfl⟩ : x ∈ Set.range i := by
    obtain ⟨t, ht⟩ := hx
    obtain ⟨y, hy, -⟩ := Scheme.exists_preimage_of_isPullback h1 x t ht.symm
    exact ⟨y, hy⟩
  obtain ⟨O, hO, hyO, hstd⟩ := GlobalTheory.T.exists_affine_nbhd_basicOpen_standardSmooth g C _ e he (q y)
  obtain ⟨V', r, hV', hy, hV⟩ := GlobalTheory.T.exists_affine_open_saturated_basicOpen_preimage B' C Y i q (MorphismProperty.of_isPullback h1.flip hcl)
    (MorphismProperty.of_isPullback h2.flip hfin) hF y O hO hyO
  obtain ⟨q₀, k1, k2, k3⟩ := GlobalTheory.T.pinched_charts_restrict_matching_opens g _ _ _ B' C Y _ _ b' e i q h1 h2 V' (C.basicOpen r) hV
  have hsm : Smooth b' := SmoothOfRelativeDimension.smooth g b'
  have := k3 _ (GlobalTheory.T.pinched_charts_affine_of_spectra pinched_spec R R' hinj c hc g _ _ _ (V'.ι ≫ b') ((C.basicOpen r).ι ≫ e) (i ∣_ V') q₀ hV'
    (hO.basicOpen r) inferInstance (hstd r) k1 k2 ⟨y, hy⟩)
  have e0 : V'.ι ((i ∣_ V') ⟨y, hy⟩) = i y :=
    (Scheme.Hom.comp_apply (i ∣_ V') V'.ι ⟨y, hy⟩).symm.trans (by rw [morphismRestrict_ι]; rfl)
  rwa [e0] at this

theorem exists_pic_patch : ∀ (X X' Z Z' : Scheme.{0}) (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z), IsPullback i' p' p i → IsFinite p → IsClosedImmersion i → GlobalTheory.Pinch.Cond p i → ∀ (c' : Pic X') (d : Pic Z), GlobalTheory.CechPic.pull i' c' = GlobalTheory.CechPic.pull p' d → ∃ c : Pic X, GlobalTheory.CechPic.pull p c = c' := by
  intro X X' Z Z' p i i' p' hsq hp hi hc c' d h
  obtain ⟨L', hL', rfl⟩ := cls_surj c'
  obtain ⟨N, hN, rfl⟩ := cls_surj d
  obtain ⟨w, hw⟩ := (cls_eq_iff (pull_isLB hL' i') (pull_isLB hN p')).1 h
  have hw' : ∀ z : Z', p (i' z) = i (p' z) := fun z ↦ by
    rw [← Scheme.Hom.comp_apply, hsq.w, Scheme.Hom.comp_apply]
  have loc : ∀ x : X, ∃ (W : X.Opens) (a : ∀ k, Γ(X', p ⁻¹ᵁ W ⊓ L'.U k)ˣ) (b : ∀ l, Γ(Z, i ⁻¹ᵁ W ⊓ N.U l)ˣ),
      x ∈ W ∧ GlobalTheory.Pinch.LocGen L' (p ⁻¹ᵁ W) a ∧ GlobalTheory.Pinch.LocGen N (i ⁻¹ᵁ W) b ∧ GlobalTheory.Pinch.Matches i' p' w a b := by
    intro x
    obtain ⟨W₁, a, h₁, ha⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X X' p hp L' hL' x
    obtain ⟨W₂, b, h₂, hb⟩ := GlobalTheory.T.exists_local_generator_finite_cover_near_point GlobalTheory.T.exists_lineBundle_localGenerator_near_finiteSet X Z i inferInstance N hN x
    obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_ratio_local_generators_common_pullback X' Z Z' i' p' L' N hL' hN w hw _ _ a b ha hb (i' ⁻¹ᵁ (p ⁻¹ᵁ (W₁ ⊓ W₂)))
      (fun z hz ↦ hz.1) (fun z hz ↦ show i (p' z) ∈ W₂ from hw' z ▸ hz.2)
    obtain ⟨W, u', hW, hx, hu'⟩ := GlobalTheory.T.exists_unit_lift_closed_subscheme_near_fibre X X' Z Z' p i i' p' hsq hp hi (W₁ ⊓ W₂) x ⟨h₁, h₂⟩ u
    have l₁ : ∀ k, p ⁻¹ᵁ W ⊓ L'.U k ≤ p ⁻¹ᵁ W₁ ⊓ L'.U k := fun k y hy ↦ ⟨(hW hy.1).1, hy.2⟩
    have l₂ : ∀ l, i ⁻¹ᵁ W ⊓ N.U l ≤ i ⁻¹ᵁ W₂ ⊓ N.U l := fun k y hy ↦ ⟨(hW hy.1).2, hy.2⟩
    refine ⟨W, fun k ↦ res inf_le_left u' * res (l₁ k) (a k), fun l ↦ res (l₂ l) (b l), hx, ?_, ?_, ?_⟩
    · intro y k k' hy hk hk'
      have m : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨hy, hk⟩
      have m' : (𝟙 X' : X' ⟶ X') y ∈ p ⁻¹ᵁ W ⊓ L'.U k' := ⟨hy, hk'⟩
      rw [map_mul, map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', gm_res _ _ _ m',
        ha y k k' (hW hy).1 hk hk', mul_left_comm]
    · intro y k k' hy hk hk'
      have m : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k := ⟨hy, hk⟩
      have m' : (𝟙 Z : Z ⟶ Z) y ∈ i ⁻¹ᵁ W ⊓ N.U k' := ⟨hy, hk'⟩
      rw [gm_res _ _ _ m, gm_res _ _ _ m', hb y k k' (hW hy).2 hk hk']
    · intro z k l h1 h2 hk hl
      have m : i' z ∈ p ⁻¹ᵁ W ⊓ L'.U k := ⟨h1, hk⟩
      have m' : p' z ∈ i ⁻¹ᵁ W ⊓ N.U l := ⟨h2, hl⟩
      rw [map_mul, gm_res _ _ _ m, gm_res _ _ _ m, gm_res _ _ _ m', hu' z h1]
      exact hu z k l (hW h1) hk hl
  choose W a b hx ha hb hm using loc
  obtain ⟨L, hL, hiso⟩ := GlobalTheory.T.exists_lineBundle_pinched_of_matching_generators X X' Z Z' p i i' p' hsq.w (GlobalTheory.T.pinchingSquare_unitsPatch X X' Z Z' p i i' p' hsq inferInstance hi hc)
    L' N hL' hN w W a b hx ha hb hm
  exact ⟨cls L hL, (cls_eq_iff (pull_isLB hL p) hL').2 hiso⟩

theorem isPullback_whisker {S : Scheme.{0}} (A : Over S) {T T' : Over S} (f : T' ⟶ T) :
    IsPullback (A ◁ f).left (snd A T').left (snd A T).left f.left := by
  have : IsPullback (A ◁ f) (snd A T') (snd A T) f := by
    refine ⟨⟨by simp⟩, ⟨PullbackCone.IsLimit.mk _ (fun s ↦ lift (s.fst ≫ fst A T) s.snd) (fun s ↦ ?_)
      (fun s ↦ by simp) (fun s m h₁ h₂ ↦ ?_)⟩⟩
    · ext
      · simp
      · simp [s.condition]
    · ext
      · simp [← h₁]
      · simp [← h₂]
  exact this.map (Over.forget S)

theorem hasRep_pinched : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg R' _ _ _ hinj c hc ⟨B', b', P', hP', hG', hF⟩ ⟨C, e, Q, hQ, hG⟩
  have hfin : IsFinite (spMap (algebraMap R R')) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 inferInstance)
  have hsur : Surjective (spMap (algebraMap R R')) := by
    refine ⟨fun x ↦ ?_⟩
    have : FaithfulSMul R R' := (faithfulSMul_iff_algebraMap_injective R R').2 hinj
    exact Algebra.IsIntegral.comap_surjective R R' x
  have hcl : IsClosedImmersion (spMap (Ideal.Quotient.mk c)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  refine GlobalTheory.T.representingScheme_of_finite_surjective_lift R A g hA hg B' _ b' P' hfin hsur hP' hG' fun x ↦ ?_
  obtain ⟨q, hq, hpb, hS⟩ := GlobalTheory.T.representsAdditiveLineBundleFamilies_compare _ A B' _ C _ b' P' e Q hP' hQ
  have wb : b'.left ≫ spMap (algebraMap R R') = B'.hom := Over.w b'
  have we : e.left ≫ spMap (Ideal.Quotient.mk c) = C.hom := Over.w e
  have hq' : q.left ≫ e.left = pullback.snd B'.hom (spMap (Ideal.Quotient.mk c)) := congrArg (·.left) hq
  obtain ⟨U, U', V, u, p, j, n, k, hu, h1, hj, hx, h2, h3⟩ := pinched R R' hinj c hc g B'.left C.left
    (B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c))).left b'.left e.left (fst B' _).left q.left hG'.smooth hG.smooth hF
    (by rw [wb, hq']; exact IsPullback.of_hasPullback _ _) (by rw [we]; exact hpb) x
  let Uo : Over (Sp R) := Over.mk u
  let U'o : Over (Sp R) := Over.mk (p ≫ u)
  let Vo : Over (Sp R) := Over.mk (n ≫ u)
  let po : U'o ⟶ Uo := Over.homMk p rfl
  let no : Vo ⟶ Uo := Over.homMk n rfl
  let jo : U'o ⟶ B' := Over.homMk j (by change j ≫ B'.hom = p ≫ u; rw [← wb, h1.w, Category.assoc])
  let ko : Vo ⟶ C := Over.homMk k (by change k ≫ C.hom = n ≫ u; rw [← we, h2.w, Category.assoc])
  let Wo : Over (Sp R) := Over.mk (pullback.fst p n ≫ p ≫ u)
  let ao : Wo ⟶ U'o := Over.homMk (pullback.fst p n) rfl
  let bo : Wo ⟶ Vo := Over.homMk (pullback.snd p n) (by
    change pullback.snd p n ≫ n ≫ u = pullback.fst p n ≫ p ≫ u
    rw [pullback.condition_assoc])
  obtain ⟨y, hy1, hy2⟩ := h3 _ (pullback.fst p n) (pullback.snd p n) pullback.condition
  let yo : Wo ⟶ B' ⊗ Over.mk (spMap (Ideal.Quotient.mk c)) := Over.homMk y (by
    rw [← Over.w (fst B' (Over.mk (spMap (Ideal.Quotient.mk c)))), ← Category.assoc, hy1]
    exact Over.w (ao ≫ jo))
  have hy1' : yo ≫ fst _ _ = ao ≫ jo := Over.OverMorphism.ext hy1
  have hy2' : yo ≫ q = bo ≫ ko := Over.OverMorphism.ext hy2
  have hsm : Smooth u := SmoothOfRelativeDimension.smooth g u
  have hsA : Smooth A.hom := SmoothOfRelativeDimension.smooth g _
  have hp : IsFinite p := MorphismProperty.of_isPullback h1.flip hfin
  have hps : Surjective p := MorphismProperty.of_isPullback h1.flip hsur
  have hn : IsClosedImmersion n := MorphismProperty.of_isPullback h2.flip hcl
  have hnoe : IsLocallyNoetherian Uo.left := LocallyOfFiniteType.isLocallyNoetherian u
  have hfl : Flat ((snd A Uo).left ≫ u) := by
    have : Flat (snd A Uo).left := inferInstanceAs (Flat (pullback.snd A.hom u))
    infer_instance
  have hcond := GlobalTheory.T.conductorSquare_flat_baseChange_schemes R R' hinj c hc _ _ _ _ _ _ _ _ hfl ((isPullback_whisker A po).paste_vert h1)
    ((isPullback_whisker A no).paste_vert h2)
  have hsq : IsPullback (A ◁ ao).left (A ◁ bo).left (A ◁ po).left (A ◁ no).left := by
    have big : IsPullback (A ◁ ao).left ((snd A Wo).left ≫ bo.left) ((snd A U'o).left ≫ po.left) no.left := (isPullback_whisker A ao).paste_vert
      ((IsPullback.of_hasPullback p n) : IsPullback ao.left bo.left po.left no.left)
    have e1 : (snd A Wo).left ≫ bo.left = (A ◁ bo).left ≫ (snd A Vo).left := (isPullback_whisker A bo).w.symm
    have e2 : (snd A U'o).left ≫ po.left = (A ◁ po).left ≫ (snd A Uo).left := (isPullback_whisker A po).w.symm
    rw [e1, e2] at big
    refine IsPullback.of_bot big ?_ (isPullback_whisker A no)
    rw [← Over.comp_left, ← Over.comp_left, ← MonoidalCategory.whiskerLeft_comp, ← MonoidalCategory.whiskerLeft_comp]
    exact congrArg (fun t ↦ (A ◁ t).left) (Over.OverMorphism.ext pullback.condition)
  have hN : Fam A (ev P' (fst A U'o) (snd A U'o ≫ jo)) := by
    have hl : (ev P' (fst A U'o) (snd A U'o ≫ jo)).IsLB := pull_isLB hP'.fam.isLB _
    refine ⟨hl, (isAdditive_iff hl).2 fun Y a a' t ↦ ?_⟩
    simp only [evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc]
    exact (isAdditive_iff hP'.fam.isLB).1 hP'.fam.add _ _ _ _
  obtain ⟨c₀, hc₀⟩ := exists_pic_patch _ _ _ _ _ _ _ _ hsq
    (MorphismProperty.of_isPullback (isPullback_whisker A po).flip hp)
    (MorphismProperty.of_isPullback (isPullback_whisker A no).flip hn) hcond
    (evc hP'.fam.isLB (fst A U'o) (snd A U'o ≫ jo)) (evc hQ.fam.isLB (fst A Vo) (snd A Vo ≫ ko)) (by
      have := congrArg (GlobalTheory.CechPic.pull (A ◁ yo).left) ((same_iff hP'.fam.isLB hQ.fam.isLB _ _).1 hS)
      simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, hy1', hy2'] at this ⊢
      exact this)
  obtain ⟨M, hM, hMS⟩ := GlobalTheory.T.exists_additiveFamily_of_pullback_finiteSurjective _ A Uo U'o hA po hp hps _ hN c₀ hc₀
  let S' : Over (Sp R) := Over.mk (spMap (algebraMap R R'))
  let r : Uo ⊗ S' ⟶ U'o := Over.homMk h1.isoPullback.inv (by
    change h1.isoPullback.inv ≫ p ≫ u = pullback.fst u (spMap (algebraMap R R')) ≫ u
    rw [h1.isoPullback_inv_fst_assoc])
  have r1 : r ≫ po = fst Uo S' := Over.OverMorphism.ext h1.isoPullback_inv_fst
  refine ⟨Uo, M, r ≫ jo, hM, hu, Over.OverMorphism.ext h1.isoPullback_inv_snd, ?_, ?_, ?_⟩
  · change IsOpenImmersion (h1.isoPullback.inv ≫ j)
    infer_instance
  · obtain ⟨x', rfl⟩ := hx
    refine ⟨h1.isoPullback.hom x', ?_⟩
    change (h1.isoPullback.hom ≫ h1.isoPullback.inv ≫ j) x' = _
    rw [Iso.hom_inv_id_assoc]
  · refine (same_iff hM.isLB hP'.fam.isLB _ _).2 ?_
    have := congrArg (GlobalTheory.CechPic.pull (A ◁ r).left) ((same_iff hM.isLB hN.isLB _ _).1 hMS)
    simp only [pull_evc, whiskerLeft_fst, whiskerLeft_snd_assoc, r1, evc_ev hP'.fam.isLB, lift_fst, lift_snd_assoc,
      Category.comp_id, whiskerLeft_snd] at this
    simpa only [Category.assoc] using this

end GlobalTheory.Pinch
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasRepresentingScheme_pinchedBase : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [Module.Finite R R'], Function.Injective (algebraMap R R') → ∀ c : Ideal R, (∀ x ∈ c, ∀ r : R', ∃ y ∈ c, algebraMap R R' y = algebraMap R R' x * r) → HasRepAF A g (Over.mk (spMap (algebraMap R R'))) → HasRep A g (Over.mk (spMap (Ideal.Quotient.mk c))) → HasRep A g (𝟙_ _) := by
  atlas_forward_decl GlobalTheory.Pinch.hasRep_pinched
end
