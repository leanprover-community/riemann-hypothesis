import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupIdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGrpObjIsGrpPullbackOfIsPullbackStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.PreUMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageCochainRestrictionBijectiveClosedImmersi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CocyclePullbackIffPreimageAffineHomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSectionsStatement
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairFstPreimageRestrictionBijectiveClosedImmersi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyClassPullbackReductionPairs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SurjectiveDeformationAffineSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GrpPullbackProdSelfIsPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullH1SurjectiveBijectiveFibre

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbCoh

theorem exists_bock : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF x
  have hc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hS.1
  have hc₀ : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hS.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback h.flip hc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback h₀.flip hc₀
  have sec := fun U ↦ GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hS hF U
  have red := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w
  have red₀ := GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w
  have bij₀ := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R₀ X X₀ φ₀ s₀).2.1
  obtain ⟨c, hc⟩ := GlobalTheory.CatCoh.H1.mk_surjective _ ((preRes φ s').pull1 x)
  choose f hf using fun (U V : AffOp X) (a : U ⟶ V) ↦ (sec V).1 (c.1 U V a)
  have hd : ∀ (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W), preα φ s s' W (d1 (OAff s) f U V W a b) = 0 := by
    intro U V W a b
    have nat := (preCoef h.w).naturality b (f U V a)
    have cc := c.2 a b
    rw [d1_apply, map_add, map_sub, hf, hf]
    erw [nat, hf]
    rw [cc]; ring
  choose w hw using fun (U V W : AffOp X) (a : U ⟶ V) (b : V ⟶ W) ↦ ((sec W).2.1 _).1 (hd U V W a b)
  have hdw : d1 (OAff s) f = t • w := by
    funext U V W a b; exact hw U V W a b
  have hw2 : ∀ ⦃U V W Y : AffOp X⦄ (a : U ⟶ V) (b : V ⟶ W) (e : W ⟶ Y),
      t • (mp (OAff s) e (w U V W a b) + w U W Y (a ≫ b) e - (w U V Y a (b ≫ e) + w V W Y b e)) = 0 := by
    intro U V W Y a b e
    have := (differential_one_mem_scaled_lattice (OAff s) f) a b e
    rw [hdw] at this
    simp only [Pi.smul_apply, map_smul] at this
    rw [smul_sub, smul_add, smul_add, this, sub_self]
  have hc0 : (fun U V W (a : U ⟶ V) (b : V ⟶ W) ↦ preα φ₀ s s₀ W (w U V W a b) : C2 (OPre φ₀ s₀)) ∈
      Z2 (OPre φ₀ s₀) := by
    intro U V W Y a b e
    have h1 := ((sec Y).2.2.2 _).2 (hw2 a b e)
    have nat := (preCoef h₀.w).naturality e (w U V W a b)
    simp only [map_add, map_sub] at h1
    erw [nat] at h1
    dsimp only
    exact sub_eq_zero.1 h1
  obtain ⟨z, hz⟩ := bij₀.2 (GlobalTheory.CatCoh.H2.mk _ ⟨_, hc0⟩)
  exact ⟨z, f, w, hdw, (red.1 f x).2 ⟨c, fun U V a ↦ (hf U V a).symm, hc⟩,
    (red₀.2.1 w z).2 ⟨⟨_, hc0⟩, fun U V W a b ↦ rfl, hz.symm⟩⟩

end GlobalTheory.AbCoh
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flat_lifting_obstruction_class : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', ∃ z : HO2 s₀, Bock h.w h₀.w t x z := by
  atlas_forward_decl GlobalTheory.AbCoh.exists_bock
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace GlobalTheory.AbCoh

theorem exists_lift_of_bock_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl x hB
  have hσc : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hse.1
  have hσ₀c : IsClosedImmersion (spMap σ₀) := IsClosedImmersion.spec_of_surjective _ hse.2.2.1
  haveI : IsClosedImmersion φ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip hσc
  haveI : IsClosedImmersion φ₀ := MorphismProperty.of_isPullback (P := @IsClosedImmersion) h₀.flip hσ₀c
  obtain ⟨f, w, hfw, hf, hw⟩ := hB
  have R1 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).1
  have R2 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R₀ X X₀ s s₀ σ₀ φ₀ h₀.w).2.1
  have R3 := (GlobalTheory.T.cocyclePullback_iff_preimage_affineHom R R' X X' s s' σ φ h.w).2.2.1
  have S := GlobalTheory.T.surjective_deformation_affine_sections R R' R₀ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ hse hfl
  have B := (GlobalTheory.T.preimageCochainRestriction_bijective_closedImmersion R' X X' φ s').1.1
  obtain ⟨c, hc, hcx⟩ := (R1 f x).1 hf
  obtain ⟨c₀, hc₀, hc₀z⟩ := (R2 w 0).1 hw
  rw [map_zero, H2.mk_eq_zero] at hc₀z
  obtain ⟨b, hb⟩ := hc₀z
  choose u hu using fun (U V : AffOp X) (a : U ⟶ V) ↦ (S V).2.2.1 (b U V a)
  have nat₀ : ∀ {V W : AffOp X} (a : V ⟶ W) (y : (OAff s).obj V),
      preα φ₀ s s₀ W (mp (OAff s) a y) = mp (OPre φ₀ s₀) a (preα φ₀ s s₀ V y) :=
    fun a y ↦ (preCoef h₀.w).naturality a y
  have hker : ∀ (U V W : AffOp X) (a : U ⟶ V) (a' : V ⟶ W), t • (w U V W a a' - d1 (OAff s) u U V W a a') = 0 := by
    intro U V W a a'
    rw [← (S W).2.2.2, map_sub, d1_apply, map_add, map_sub, nat₀, hu, hu, hu, ← hc₀, ← d1_apply, hb, sub_self]
  have hg : f - t • u ∈ Z1 (OAff s) := by
    rw [commAlgFunctorCocyclesOne_eq_ker, LinearMap.mem_ker, map_sub, hfw, map_smul, ← smul_sub]
    funext U V W a a'
    exact hker U V W a a'
  refine ⟨H1.mk _ ⟨f - t • u, hg⟩, B ?_⟩
  rw [R3, CoefMap.pullCohomologyOne_class, ← hcx]
  congr 1
  refine Subtype.ext ?_
  funext U V a
  rw [CoefMap.pullCocycleOne_apply, hc]
  show preα φ s s' V (f U V a - t • u U V a) = _
  rw [map_sub, ((S V).2.1 _).2 ⟨_, rfl⟩, sub_zero]

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)), SmallExt t σ σ₀ → Flat s → ∀ x : HO1 s', Bock h.w h₀.w t x 0 → ∃ y : HO1 s, pullHO1 h.w y = x := by
  atlas_forward_decl GlobalTheory.AbCoh.exists_lift_of_bock_zero
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem Bock_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ x x' z z'
  rintro ⟨f, w, hd, ⟨c, hc, hcx⟩, ⟨e, he, hez⟩⟩ ⟨f', w', hd', ⟨c', hc', hcx'⟩, ⟨e', he', hez'⟩⟩
  refine ⟨f + f', w + w', by rw [map_add, hd, hd', smul_add], ⟨c + c', fun p q a ↦ ?_, ?_⟩,
    ⟨e + e', fun p q r a b ↦ ?_, ?_⟩⟩
  · simp only [Submodule.coe_add, Pi.add_apply, hc, hc', map_add]
  · rw [map_add, hcx, hcx', map_add]
  · simp only [Submodule.coe_add, Pi.add_apply, he, he', map_add]
  · rw [map_add, hez, hez', map_add]

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftingObstructionBockstein_add : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (h₀ : φ₀ ≫ s = s₀ ≫ spMap σ₀) (x x' : HO1 s') (z z' : HO2 s₀), Bock h h₀ t x z → Bock h h₀ t x' z' → Bock h h₀ t (x + x') (z + z') := by
  atlas_forward_decl GlobalTheory.AbCoh.Bock_add
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.AbCoh

theorem isClosedImmersion_of_isPullback_spMap_surj {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'}
    (hσ : Function.Surjective σ) {X X' : Scheme.{0}} {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    (h : IsPullback φ s' s (spMap σ)) : IsClosedImmersion φ := by
  have : IsClosedImmersion (spMap σ) := IsClosedImmersion.spec_of_surjective _ hσ
  exact MorphismProperty.of_isPullback (P := @IsClosedImmersion) h.flip this

theorem restrict_pull1_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO1 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull1 ((preRes χ q').pull1 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull1 y := by
  obtain ⟨y, rfl⟩ := H1.mk_surjective _ y
  rfl

theorem restrict_pull2_preRes_pairFst {R' : Type} [CommRing R'] {X Y Y' : Scheme.{0}} (ψ : Y ⟶ X)
    (χ : Y' ⟶ Y) [IsAffineHom χ] (q' : Y' ⟶ Sp R') (y : HO2 q') :
    (CoefMap.restrict (OPre χ q') (pairFst ψ)).pull2 ((preRes χ q').pull2 y) =
      (CoefMap.restrict (OAff q') (pairFst ψ ⋙ preAff χ)).pull2 y := by
  obtain ⟨y, rfl⟩ := H2.mk_surjective _ y
  rfl

set_option maxHeartbeats 1000000 in

theorem bock_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  intro R R' R₀ _ _ _ t σ σ₀ X X' X₀ s s' s₀ φ φ₀ h h₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ ψ ψ' ψ₀ w w' w₀ hc hc₀
    hS hs hq x z z' hB hB'
  obtain ⟨f, v, hfv, hf, hv⟩ := hB
  obtain ⟨f₂, v₂, hfv₂, hf₂, hv₂⟩ := hB'
  haveI : IsClosedImmersion φ := isClosedImmersion_of_isPullback_spMap_surj hS.1 h
  haveI : IsClosedImmersion φ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 h₀
  haveI : IsClosedImmersion χ := isClosedImmersion_of_isPullback_spMap_surj hS.1 k
  haveI : IsClosedImmersion χ₀ := isClosedImmersion_of_isPullback_spMap_surj hS.2.2.1 k₀
  have hsec := GlobalTheory.AbCoh.preα_surjective_and_ker R R' R₀ t σ σ₀ Y Y' Y₀ q q' q₀ χ χ₀ k k₀ hS hq
  obtain ⟨c₁, hc₁, hC₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R' σ X X' Y Y' s s' q q' φ χ h.w ψ ψ' w w' hc inferInstance).1 f x hf
  obtain ⟨c₂, hc₂, hC₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R' Y Y' q q' σ χ k.w).1 f₂ (pullHO1 w' x)).1 hf₂
  obtain ⟨e₁, he₁, hE₁⟩ :=
    (GlobalTheory.AbCoh.red_preimage_pairs R R₀ σ₀ X X₀ Y Y₀ s s₀ q q₀ φ₀ χ₀ h₀.w ψ ψ₀ w w₀ hc₀ inferInstance).2 v z hv
  obtain ⟨e₂, he₂, hE₂⟩ := ((GlobalTheory.AbCoh.red_iff_pre R R₀ Y Y₀ q q₀ σ₀ χ₀ k₀.w).2.1 v₂ z').1 hv₂
  have nat : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ q q' V (mp (OAff q) a b) = mp (OPre χ q') a (preα χ q q' U b) :=
    fun a b ↦ (preCoef k.w).naturality a b
  have nat₀ : ∀ {U V : AffOp Y} (a : U ⟶ V) (b : (OAff q).obj U),
      preα χ₀ q q₀ V (mp (OAff q) a b) = mp (OPre χ₀ q₀) a (preα χ₀ q q₀ U b) :=
    fun a b ↦ (preCoef k₀.w).naturality a b

  obtain ⟨g', hg'⟩ := (H1.mk_eq_mk (f := c₁)
    (f' := (CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂)).1 (by
      rw [hC₁, ← CoefMap.pullCohomologyOne_class, hC₂, restrict_pull1_preRes_pairFst])
  choose g hg using fun p : (Pair ψ)ᵒᵖ ↦ (hsec ((pairFst ψ).obj p)).1 (g' p)
  obtain ⟨F1, hF1⟩ : ∃ F1 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F1 a b u = (pairPull w).α b (f _ _ ((pairPull w).G.map u)) := ⟨_, fun _ _ _ ↦ rfl⟩
  obtain ⟨F2, hF2⟩ : ∃ F2 : C1 (OPair ψ q), ∀ a b (u : a ⟶ b),
      F2 a b u = f₂ _ _ ((pairFst ψ).map u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hred : ∀ a b (u : a ⟶ b),
      preα χ q q' ((pairFst ψ).obj b) ((F1 - F2 - d0 (OPair ψ q) g) a b u) = 0 := by
    intro a b u
    have hc₂' : ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u =
        preα χ q q' ((pairFst ψ).obj b) (f₂ _ _ ((pairFst ψ).map u)) := hc₂ _ _ _
    have e : g' b - mp (pairFst ψ ⋙ OPre χ q') u (g' a) =
        c₁.1 a b u - ((CoefMap.restrict (OPre χ q') (pairFst ψ)).pullbackOneCocycle c₂).1 a b u :=
      congrFun (congrFun (congrFun hg' a) b) u
    have e' : preα χ q q' ((pairFst ψ).obj b) (mp (OPair ψ q) u (g a)) =
        mp (pairFst ψ ⋙ OPre χ q') u (g' a) := by
      have := nat ((pairFst ψ).map u) (g a)
      rw [hg a] at this
      exact this
    simp only [Pi.sub_apply, amitsur_d0_apply, map_sub]
    rw [hF1, hF2, ← hc₁, ← hc₂', hg b, e', e, sub_self]
  choose u₀ hu₀ using fun a b (u : a ⟶ b) ↦ ((hsec ((pairFst ψ).obj b)).2.1 _).1 (hred a b u)
  have hD : F1 - F2 - d0 (OPair ψ q) g = t • (u₀ : C1 (OPair ψ q)) := by
    funext a b u; exact hu₀ a b u
  obtain ⟨W1, hW1⟩ : ∃ W1 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W1 a b c u u' = (pairPull w).α c (v _ _ _ ((pairPull w).G.map u) ((pairPull w).G.map u')) :=
    ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  obtain ⟨W2, hW2⟩ : ∃ W2 : C2 (OPair ψ q), ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      W2 a b c u u' = v₂ _ _ _ ((pairFst ψ).map u) ((pairFst ψ).map u') := ⟨_, fun _ _ _ _ _ ↦ rfl⟩
  have hdF1 : d1 (OPair ψ q) F1 = t • W1 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv _) _) _)
      ((pairPull w).G.map u)) ((pairPull w).G.map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF1, hF1, hF1, hW1, ← (pairPull w).naturality, Functor.map_comp, ← map_sub, ← map_add, e,
      (pairPull w).smul]
    rfl
  have hdF2 : d1 (OPair ψ q) F2 = t • W2 := by
    funext a b c u u'
    have e := congrFun (congrFun (congrFun (congrFun (congrFun hfv₂ _) _) _)
      ((pairFst ψ).map u)) ((pairFst ψ).map u')
    simp only [d1_apply, Pi.smul_apply] at e ⊢
    rw [hF2, hF2, hF2, hW2, Functor.map_comp]
    exact e
  have hdd : d1 (OPair ψ q) (d0 (OPair ψ q) g) = 0 := by
    have := commAlgFunctorCoboundaryZero_mem_cocyclesOne (OPair ψ q) g
    rw [commAlgFunctorCocyclesOne_eq_ker] at this
    exact this
  have hmain : t • (W1 - W2 - d1 (OPair ψ q) u₀) = 0 := by
    rw [smul_sub, smul_sub, ← hdF1, ← hdF2, ← (d1 (OPair ψ q)).map_smul, ← hD, map_sub, map_sub, hdd,
      sub_zero, sub_self]
  have hzero : ∀ a b c (u : a ⟶ b) (u' : b ⟶ c),
      preα χ₀ q q₀ ((pairFst ψ).obj c) ((W1 - W2 - d1 (OPair ψ q) u₀) a b c u u') = 0 := by
    intro a b c u u'
    refine ((hsec ((pairFst ψ).obj c)).2.2.2 _).2 ?_
    exact congrFun (congrFun (congrFun (congrFun (congrFun hmain a) b) c) u) u'
  obtain ⟨ub, hub⟩ : ∃ ub : C1 (pairFst ψ ⋙ OPre χ₀ q₀), ∀ a b (u : a ⟶ b),
      ub a b u = preα χ₀ q q₀ ((pairFst ψ).obj b) (u₀ a b u) := ⟨_, fun _ _ _ ↦ rfl⟩
  have hH2 : H2.mk _ e₁ = H2.mk _ ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂) := by
    refine H2.mk_eq_mk.2 ⟨ub, ?_⟩
    funext a b c u u'
    have E := hzero a b c u u'
    simp only [Pi.sub_apply, d1_apply, map_sub, map_add] at E
    have E1 : preα χ₀ q q₀ ((pairFst ψ).obj c) (mp (OPair ψ q) u' (u₀ a b u)) =
        mp (pairFst ψ ⋙ OPre χ₀ q₀) u' (ub a b u) := by
      rw [hub]; exact nat₀ ((pairFst ψ).map u') (u₀ a b u)
    have E2 : e₁.1 a b c u u' = preα χ₀ q q₀ _ (W1 a b c u u') := by rw [he₁, hW1]
    have E3 : ((CoefMap.restrict (OPre χ₀ q₀) (pairFst ψ)).pullbackTwoCocycle e₂).1 a b c u u' =
        preα χ₀ q q₀ _ (W2 a b c u u') := by
      rw [hW2]; exact he₂ _ _ _ _ _
    simp only [d1_apply, Pi.sub_apply]
    rw [E2, E3, ← E1, hub, hub]
    linear_combination -E
  rw [hE₁, ← CoefMap.pullCohomologyTwo_class, hE₂, restrict_pull2_preRes_pairFst] at hH2
  exact ((GlobalTheory.AbCoh.pair_pre_bijective R₀ X Y Y₀ ψ χ₀ q₀).2.1.1 hH2).symm

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.obstructionClass_natural : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (X X' X₀ : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (s₀ : X₀ ⟶ Sp R₀) (φ : X' ⟶ X) (φ₀ : X₀ ⟶ X) (h : IsPullback φ s' s (spMap σ)) (h₀ : IsPullback φ₀ s₀ s (spMap σ₀)) (Y Y' Y₀ : Scheme.{0}) (q : Y ⟶ Sp R) (q' : Y' ⟶ Sp R') (q₀ : Y₀ ⟶ Sp R₀) (χ : Y' ⟶ Y) (χ₀ : Y₀ ⟶ Y) (k : IsPullback χ q' q (spMap σ)) (k₀ : IsPullback χ₀ q₀ q (spMap σ₀)) (ψ : Y ⟶ X) (ψ' : Y' ⟶ X') (ψ₀ : Y₀ ⟶ X₀) (w : ψ ≫ s = q ≫ spMap (RingHom.id R)) (w' : ψ' ≫ s' = q' ≫ spMap (RingHom.id R')) (w₀ : ψ₀ ≫ s₀ = q₀ ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = χ ≫ ψ → ψ₀ ≫ φ₀ = χ₀ ≫ ψ → SmallExt t σ σ₀ → Flat s → Flat q → ∀ (x : HO1 s') (z : HO2 s₀) (z' : HO2 q₀), Bock h.w h₀.w t x z → Bock k.w k₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
  atlas_forward_decl GlobalTheory.AbCoh.bock_natural
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_smallExt : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  intro R R' R₀ _ _ _ t σ σ₀ g A _ A' _ A₀ _ φ φ₀ h h₀ hS hA _ hP hN x
  haveI := hA.smooth
  have hF : Flat A.hom := inferInstance
  have hF2 : Flat (A ⊗ A).hom := by
    show Flat (pullback.fst A.hom A.hom ≫ A.hom)
    infer_instance
  obtain ⟨Φ, hΦ, hm, h1, h2, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R' σ A A' φ h
  obtain ⟨Φ₀, hΦ₀, hm₀, h1₀, h2₀, -, -⟩ := GlobalTheory.T.grpPullback_prod_self_isPullback R R₀ σ₀ A A₀ φ₀ h₀
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x

  have nat : ∀ (ψ : (A ⊗ A).left ⟶ A.left) (ψ' : (A' ⊗ A').left ⟶ A'.left) (ψ₀ : (A₀ ⊗ A₀).left ⟶ A₀.left)
      (w : ψ ≫ A.hom = (A ⊗ A).hom ≫ spMap (RingHom.id R)) (w' : ψ' ≫ A'.hom = (A' ⊗ A').hom ≫ spMap (RingHom.id R'))
      (w₀ : ψ₀ ≫ A₀.hom = (A₀ ⊗ A₀).hom ≫ spMap (RingHom.id R₀)), ψ' ≫ φ = Φ ≫ ψ → ψ₀ ≫ φ₀ = Φ₀ ≫ ψ →
      ∀ z', Bock hΦ.w hΦ₀.w t (pullHO1 w' x) z' → z' = pullHO2 w₀ z := by
    intro ψ ψ' ψ₀ w w' w₀ e e₀ z' hz'
    exact GlobalTheory.T.obstructionClass_natural R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1
      (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom Φ Φ₀ hΦ hΦ₀
      ψ ψ' ψ₀ w w' w₀ e e₀ hS hF hF2 x z z' hz hz'
  have ex : ∀ y : HO1 (A' ⊗ A').hom, ∃ z' : HO2 (A₀ ⊗ A₀).hom, Bock hΦ.w hΦ₀.w t y z' := fun y ↦
    GlobalTheory.T.exists_flat_lifting_obstruction_class R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom (A₀ ⊗ A₀).hom
      Φ Φ₀ hΦ hΦ₀ hS hF2 y
  obtain ⟨z1, hz1⟩ := ex (pO1 (fst A' A') x)
  obtain ⟨z2, hz2⟩ := ex (pO1 (snd A' A') x)
  have e1 : z1 = structureSheafH2Pullback (fst A₀ A₀) z := nat _ _ _ (ovw (fst A A)) (ovw (fst A' A')) (ovw (fst A₀ A₀)) h1 h1₀ z1 hz1
  have e2 : z2 = structureSheafH2Pullback (snd A₀ A₀) z := nat _ _ _ (ovw (snd A A)) (ovw (snd A' A')) (ovw (snd A₀ A₀)) h2 h2₀ z2 hz2
  have hsum := GlobalTheory.T.liftingObstructionBockstein_add R R' R₀ t σ σ₀ (A ⊗ A).left (A' ⊗ A').left (A₀ ⊗ A₀).left (A ⊗ A).hom (A' ⊗ A').hom
    (A₀ ⊗ A₀).hom Φ Φ₀ hΦ.w hΦ₀.w _ _ z1 z2 hz1 hz2
  rw [← hP x] at hsum
  have em : z1 + z2 = structureSheafH2Pullback μ[A₀] z := nat _ _ _ (ovw μ[A]) (ovw μ[A']) (ovw μ[A₀]) hm hm₀ _ hsum
  have z0 : z = 0 := hN z (by rw [← em, e1, e2])
  subst z0
  exact GlobalTheory.T.exists_lift_of_lifting_obstruction_eq_zero R R' R₀ t σ σ₀ A.left A'.left A₀.left A.hom A'.hom A₀.hom φ φ₀ h.1 h₀.1 hS hF x hz

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_extension_primitive_lift : ∀ (R R' R₀ : Type) [CommRing R] [CommRing R'] [CommRing R₀] (t : R) (σ : R →+* R') (σ₀ : R →+* R₀) (g : ℕ) (A : Over (Sp R)) [GrpObj A] (A' : Over (Sp R')) [GrpObj A'] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A'.left ⟶ A.left) (φ₀ : A₀.left ⟶ A.left) (h : IsGrpPullback A' A (spMap σ) φ) (h₀ : IsGrpPullback A₀ A (spMap σ₀) φ₀), SmallExt t σ σ₀ → IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → StructureSheafH1Primitive A' → NoPrimitiveStructureSheafH2 A₀ → Function.Surjective (pullHO1 h.1.w) := by
  atlas_forward_decl GlobalTheory.AbCoh.pullHO1_surjective_of_smallExt
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbCoh

theorem pullHO1_surjective_of_bijective_base : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) :=
  fun R R' _ _ σ X X' s s' φ h hσ ↦ pullHO1_surjective_of_bijective R R' σ hσ X s X' s' φ h

end GlobalTheory.AbCoh
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_h1_surjective_of_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] (σ : R →+* R') (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (h : IsPullback φ s' s (spMap σ)), Function.Bijective σ → Function.Surjective (pullHO1 h.w) := by
  atlas_forward_decl GlobalTheory.AbCoh.pullHO1_surjective_of_bijective_base
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.SmallStepSurj

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem surj_of_smallExt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  intro R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w
  have hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)
  by_cases htm : t ∈ IsLocalRing.maximalIdeal R
  ·
    let R₀ := R ⧸ IsLocalRing.maximalIdeal R
    let σ₀ : R →+* R₀ := Ideal.Quotient.mk _
    have hR₀ : IsField R₀ :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)
    have hse : SmallExt t σ' σ₀ := by
      refine ⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · exact hm a
      · intro hat
        by_contra hna
        have hu : IsUnit a := by
          by_contra hnu
          exact hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)
        exact ht (hu.mul_right_eq_zero.1 hat)

    have hP' := IsPullback.of_hasPullback A.hom (spMap σ')
    have hP₀ := IsPullback.of_hasPullback A.hom (spMap σ₀)
    obtain ⟨i', hg', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' σ' A _ _ _ hP'
    obtain ⟨i₀, hg₀, hab₀, hsm₀⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R₀ σ₀ A _ _ _ hP₀
    have hstep := GlobalTheory.T.small_extension_primitive_lift R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg
      (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1

    have hle : RingHom.ker σ' ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]; exact htm
    let τ : R' →+* k := RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩
    have hτ : ∀ r, τ (σ' r) = σ r := fun r =>
      RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r
    have hτs : Function.Surjective τ := fun y => by
      obtain ⟨x, rfl⟩ := hσ y; exact ⟨σ' x, hτ x⟩
    have hcomp : spMap σ = spMap τ ≫ spMap σ' := by
      rw [← spMap_comp_hom]; congr 1; ext r; exact (hτ r).symm
    let ψ' : X₀ ⟶ pullback A.hom (spMap σ') := hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])
    have hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ := hP'.lift_fst _ _ _
    have w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ) := by
      refine IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'
      rw [hψ', ← hcomp]; exact w
    have hsurj := (hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'
    intro y
    obtain ⟨x', rfl⟩ := hsurj y
    obtain ⟨a, rfl⟩ := hstep x'
    refine ⟨a, ?_⟩
    exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ'))
      σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm
  ·
    have hu : IsUnit t := by
      by_contra hnu
      exact htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)
    have hinj : Function.Injective σ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      have hma : a ∈ IsLocalRing.maximalIdeal R := by rw [← hkerσ]; exact ha
      exact (hu.mul_left_eq_zero).1 (hm a hma)
    exact GlobalTheory.T.pull_h1_surjective_of_bijective R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩

end GlobalTheory.AbCoh.SmallStepSurj
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.artinian_lift_axes_wedge : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  atlas_forward_decl GlobalTheory.AbCoh.SmallStepSurj.surj_of_smallExt
end
