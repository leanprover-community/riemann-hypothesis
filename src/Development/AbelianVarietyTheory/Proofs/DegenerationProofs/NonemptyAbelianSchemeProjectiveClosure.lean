import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsHomOpenPart
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ImmByOfSpans
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsInvertibleMatrixChangeOfSpanEq
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace
import BuildAid.ForwardExisting
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueIsRatio
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsLBGenTrivOfRatios
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericTrivialisationSectionAndPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsClosedImmersionOfCoordinateDivisibility

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projBundle_closure_alt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [IsNoetherianRing o] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (J : Type) [Fintype J] (EE : M.Lat J) (s : J → Ω'), IsProjOver M.s → (∃ j, s j ≠ 0) → Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = s j / s i}) = ⊤ → ∃ (M' : RatModel o Ω') (f : M'.Z ⟶ M.Z), M.IsHom M' φ f ∧ IsProjOver M'.s ∧ ∀ (W : M.Z.Opens) (B : Matrix J J Ω), IsAffineOpen W → (W : Set M.Z).Nonempty → (∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)) → (∀ z', f z' ∈ W → ∃ i, M'.Div ((B.map φ).mulVec s) i z') ∧ ∀ i, (B.map φ).mulVec s i ≠ 0 → ∃ U : M'.Z.Opens, IsAffineOpen U ∧ (U : Set M'.Z) = {z' | f z' ∈ W ∧ M'.Div ((B.map φ).mulVec s) i z'} ∧ M'.ringOn U = Algebra.adjoin o (φ '' (M.ringOn W : Set Ω) ∪ Set.range fun j => (B.map φ).mulVec s j / (B.map φ).mulVec s i) := by
  first | exact @GlobalTheory.ZH.RatModel.exists_projBundle_closure | exact GlobalTheory.ZH.RatModel.exists_projBundle_closure | (intros; apply GlobalTheory.ZH.RatModel.exists_projBundle_closure <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem comp_opens_toSpecΓ_eq_valMap {C : Type} [CommRing C] {X : Scheme.{0}} (U : X.Opens)
    (eta : Sp C ⟶ U.toScheme) (h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U) :
    eta ≫ U.toSpecΓ = Spec.map (valMap (eta ≫ U.ι) U h) := by
  have e : (⊤ : U.toScheme.Opens) ≤ U.ι ⁻¹ᵁ U := fun z _ => z.2
  rw [← appLE_valMap eta U.ι e (le_preimage_top eta) h, Scheme.Opens.toSpecΓ, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Spec.map_comp, valMap, Spec.map_comp]
  have h1 : (Sp C).toSpecΓ = Spec.map (Scheme.ΓSpecIso (CommRingCat.of C)).hom := by
    rw [← Scheme.isoSpec_Spec_hom]; rfl
  have h2 : U.topIso.inv = U.ι.appLE U ⊤ e := by
    rw [Scheme.Opens.ι_appLE]; rfl
  rw [h1, h2]
  rfl

theorem exists_hom_spec_of_le_ringOn :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  intro o Ω _ _ _ M U R hU hR
  let ψ : R →+* Γ(M.Z, U) :=
    (M.sectionsEquiv U hU).symm.toRingHom.comp (Subalgebra.inclusion hR).toRingHom
  refine ⟨U.toSpecΓ ≫ Spec.map (CommRingCat.ofHom ψ), fun eta he => ?_⟩
  have h : ⊤ ≤ (eta ≫ U.ι) ⁻¹ᵁ U := he ▸ M.top_le_preimage_pt hU
  rw [← Category.assoc, comp_opens_toSpecΓ_eq_valMap U eta h, ← Spec.map_comp]
  congr 1
  ext a
  have e : (M.sectionsEquiv U hU (ψ a) : Ω) = a :=
    congrArg Subtype.val ((M.sectionsEquiv U hU).apply_symm_apply _)
  rw [coe_sectionsEquiv, ← he, valF_eq_valR, valR_eq _ U h] at e
  exact e

end GlobalTheory.ZH.RatModel
end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hom_spec_of_le_ringOn' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (U₀ : M.Z.Opens) (R : Subalgebra o Ω), (U₀ : Set M.Z).Nonempty → R ≤ M.ringOn U₀ → ∃ u₀ : U₀.toScheme ⟶ Sp R, ∀ eta : Sp Ω ⟶ U₀.toScheme, eta ≫ U₀.ι = M.pt → eta ≫ u₀ = spMap R.val.toRingHom := by
  atlas_forward_decl GlobalTheory.ZH.RatModel.exists_hom_spec_of_le_ringOn
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH
open GlobalTheory.Points

theorem exists_functionField_point (X : Scheme.{0}) [IsIntegral X] :
    ∃ (K : Type) (_ : Field K) (pt : Sp K ⟶ X), (∀ w, pt w = genericPoint X) ∧
      ∀ x : K, ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x := by
  let pt : Sp X.functionField ⟶ X := X.fromSpecStalk (genericPoint X)
  refine ⟨X.functionField, inferInstance, pt, fun w => ?_, fun x => ?_⟩
  · rw [Subsingleton.elim w (IsLocalRing.closedPoint X.functionField)]
    exact Scheme.fromSpecStalk_closedPoint
  · obtain ⟨W, hW, g, rfl⟩ := X.presheaf.germ_exist (x := genericPoint X) x
    obtain ⟨V, hV, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hW
    have hle' : V ≤ W := hle
    let φ : Γ(X, V) ⟶ CommRingCat.of X.functionField := X.presheaf.germ V (genericPoint X) hz
    have e : pt = Spec.map φ ≫ hV.fromSpec := (hV.fromSpecStalk_eq_fromSpecStalk hz).symm
    refine ⟨V, (X.presheaf.map (homOfLE hle').op).hom g, ⟨_, hz⟩, ?_⟩
    rw [e, valF_eq_valR, valR_eq _ V (le_preimage_specMap_fromSpec hV φ), valMap_specMap_fromSpec]
    exact X.presheaf.germ_res_apply (homOfLE hle') _ hz g

theorem RatModel.exists_functionField_of_isDominant (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω]
    (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q] :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X),
      Set.range pt = {genericPoint X} ∧
      (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧
      pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  obtain ⟨K, _, pt, hpt, honto⟩ := exists_functionField_point X
  have hq : q (genericPoint X) = genericPoint M.Z := by
    have h := (genericPoint_spec X).image q.continuous
    rw [Set.image_univ, q.denseRange.closure_range] at h
    exact h.eq (genericPoint_spec M.Z)
  have hy : ∀ w, (pt ≫ q) w = genericPoint M.Z := fun w => by
    rw [Scheme.Hom.comp_apply, hpt, hq]
  have hs : ∀ w, (pt ≫ q) w ⤳ genericPoint M.Z := fun w => (hy w) ▸ specializes_rfl
  have hm : ∀ x : Ω, x ∈ M.O (genericPoint M.Z) := fun x => by rw [RatModel.O_genericPoint]; trivial
  let β : Ω →+* K := (RatModel.valHomOf (pt ≫ q) _ hs).comp
    ((RingHom.id Ω).codRestrict (M.O (genericPoint M.Z)).toSubring hm)
  letI : Algebra o K := (β.comp (algebraMap o Ω)).toAlgebra
  refine ⟨K, inferInstance, inferInstance, { β with commutes' := fun _ => rfl }, pt, ?_, honto, ?_⟩
  · exact Set.eq_singleton_iff_unique_mem.2 ⟨⟨_, hpt (IsLocalRing.closedPoint K)⟩, by
      rintro _ ⟨w, rfl⟩
      exact hpt w⟩
  · obtain ⟨U, hU, hz, -⟩ := exists_isAffineOpen_mem_and_subset (X := M.Z) (x := genericPoint M.Z) (U := ⊤) trivial
    have h1 := top_le_preimage_of_specializes hs hz
    have h2 : ⊤ ≤ M.pt ⁻¹ᵁ U := M.top_le_preimage_pt ⟨_, hz⟩
    refine ext_of_valR hU h1 (le_preimage_comp _ _ h2 (le_preimage_top _)) fun f => ?_
    exact ((valR_spMap_comp β M.pt U h2 f).trans (RatModel.val_valF ((top_le_preimage_iff _ _).1 h1) f)).symm

end GlobalTheory.ZH
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_functionField_of_isDominant' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (X : Scheme.{0}) [IsIntegral X] (q : X ⟶ M.Z) [IsDominant q], ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra o Ω') (φ : Ω →ₐ[o] Ω') (pt : Sp Ω' ⟶ X), Set.range pt = {genericPoint X} ∧ (∀ x : Ω', ∃ (U : X.Opens) (f : Γ(X, U)), (U : Set X).Nonempty ∧ valF pt U f = x) ∧ pt ≫ q = spMap φ.toRingHom ≫ M.pt := by
  first | exact @GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | exact GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant | (intros; apply GlobalTheory.ZH.RatModel.exists_functionField_of_isDominant <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

namespace GlobalTheory.ZH.DivCrd

open GlobalTheory.Points CrdCalc

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {N : RatModel o Ω} {X : Scheme.{0}} {a : N.Z ⟶ X}
  {H : LB X} {J : Type} {s : J → H.Sec} {t : J → Ω}

theorem ratio_eq (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z} (hz : a z ∈ nonzeroLocus (s k)) :
    t k ≠ 0 ∧ ∀ (j : J) (r : Γ(X, nonzeroLocus (s k))), IsRatio (s j) (s k) _ r →
      valF N.pt (a ⁻¹ᵁ nonzeroLocus (s k)) (a.app _ r) = t j / t k := by
  have h : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s k) :=
    N.top_le_preimage_pt (U := a ⁻¹ᵁ nonzeroLocus (s k)) ⟨z, hz⟩
  have hk : t k ≠ 0 := ((crd_isUnit_iff k ht).2 h).ne_zero
  refine ⟨hk, fun j r hr => ?_⟩
  rw [eq_div_iff hk, crd_ratio ht hr h, valR_comp]
  rfl

theorem div_of_mem (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {k : J} {z : N.Z}
    (hz : a z ∈ nonzeroLocus (s k)) : N.Div t k z := by
  obtain ⟨hk, h⟩ := ratio_eq ht hz
  refine ⟨hk, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  exact ⟨a ⁻¹ᵁ nonzeroLocus (s k), a.app _ r, hz, h j r hr⟩

theorem crd_eq_val_mul (hH : H.IsLB) (ht : Crd H s (N.pt ≫ a) t) {K : Type} [Field K] {x : Sp K ⟶ N.Z}
    {v : J → K} {k : J} (hv : Crd H s (x ≫ a) v)
    (hz : a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s k)) :
    v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  have hx : ⊤ ≤ x ⁻¹ᵁ (a ⁻¹ᵁ nonzeroLocus (s k)) := (le_preimage_iff x _).2 hz
  have h : ⊤ ≤ (x ≫ a) ⁻¹ᵁ nonzeroLocus (s k) := hx
  refine ⟨((crd_isUnit_iff k hv).2 h).ne_zero, fun j => ?_⟩
  obtain ⟨r, hr, -⟩ := GlobalTheory.SecRatio.existsUnique_isRatio hH (s j) (s k) _ le_rfl
  rw [RatModel.val_eq ((top_le_preimage_iff _ _).1 hx) ((ratio_eq ht hz).2 j r hr), crd_ratio hv hr h,
    valR_comp]
  rfl

theorem mem_of_div_pt (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {K : Type} [Field K] (x : Sp K ⟶ N.Z) {i : J} (hi : N.Div t i (x (IsLocalRing.closedPoint K))) :
    a (x (IsLocalRing.closedPoint K)) ∈ nonzeroLocus (s i) := by
  have hm : a (x (IsLocalRing.closedPoint K)) ∈ ⨆ j, nonzeroLocus (s j) := by rw [hs]; trivial
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
  obtain ⟨v, hv⟩ := crd_exists hH s (x ≫ a)
  obtain ⟨h0, h1⟩ := crd_eq_val_mul hH ht hv hk
  have hd := div_of_mem hH ht hk
  have hu := (RatModel.val_ne_zero_iff (RatModel.range_eq_singleton x _) _).2 ((hd.div_iff_isUnit i).1 hi)
  have hvi : IsUnit (v i) := isUnit_iff_ne_zero.2 (by rw [h1 i]; exact mul_ne_zero hu h0)
  exact (le_preimage_iff (x ≫ a) _).1 ((crd_isUnit_iff i hv).1 hvi)

theorem mem_of_div (hH : H.IsLB) (hs : ⨆ j, nonzeroLocus (s j) = ⊤) (ht : Crd H s (N.pt ≫ a) t)
    {i : J} {z : N.Z} (hi : N.Div t i z) : a z ∈ nonzeroLocus (s i) := by
  let x : Sp (N.Z.residueField z) ⟶ N.Z := N.Z.fromSpecResidueField z
  have e : x (IsLocalRing.closedPoint (N.Z.residueField z)) = z := Scheme.fromSpecResidueField_apply _ _
  have h := mem_of_div_pt hH hs ht x (i := i) (by rw [e]; exact hi)
  rwa [e] at h

theorem div_iff_mem_nonzeroLocus : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ hH hs ht =>
    ⟨fun _ _ => ⟨mem_of_div hH hs ht, div_of_mem hH ht⟩,
      fun _ _ x _ _ hv hk => crd_eq_val_mul hH ht hv (mem_of_div_pt hH hs ht x hk)⟩

end GlobalTheory.ZH.DivCrd
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.div_iff_mem_nonzeroLocus_and_crd_ratio : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (N : RatModel o Ω) (X : Scheme.{0}) (a : N.Z ⟶ X) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω), H.IsLB → ⨆ j, nonzeroLocus (s j) = ⊤ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) ∧ ∀ (K : Type) [Field K] (x : Sp K ⟶ N.Z) (v : J → K) (k : J), Crd H s (x ≫ a) v → N.Div t k (x (IsLocalRing.closedPoint K)) → v k ≠ 0 ∧ ∀ j, v j = N.val x (t j / t k) * v k := by
  atlas_forward_decl GlobalTheory.ZH.DivCrd.div_iff_mem_nonzeroLocus
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valR_mem_image_ringOn {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {N : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {Y : Scheme.{0}} {j : Y ⟶ M.Z} [IsOpenImmersion j]
    {b : N.Z ⟶ Y} (h : M.IsHom N φ (b ≫ j)) {V : Y.Opens} (hV : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V) (g : Γ(Y, V)) :
    valR (N.pt ≫ b) V g ∈ φ '' (M.ringOn (j ''ᵁ V : M.Z.Opens) : Set Ω) := by
  have hne : ((j ''ᵁ V : M.Z.Opens) : Set M.Z).Nonempty :=
    ⟨_, _, hV (x := IsLocalRing.closedPoint Ω') trivial, rfl⟩
  have hle : V ≤ j ⁻¹ᵁ (j ''ᵁ V) := (j.preimage_image_eq V).ge
  refine ⟨valF M.pt _ ((j.appIso V).inv.hom g), (mem_ringOn_iff_exists hne).2 ⟨_, rfl⟩, ?_⟩
  refine (valR_spMap_comp φ.toRingHom M.pt _ (M.top_le_preimage_pt hne) _).symm.trans ?_
  rw [← show N.pt ≫ b ≫ j = spMap φ.toRingHom ≫ M.pt from h, ← Category.assoc, ← valR_appLE _ j hle hV,
    ← CommRingCat.comp_apply, Scheme.Hom.appIso_inv_appLE]
  exact valR_res _ le_rfl hV g

theorem projChart_of_isPullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  intro o Ω _ _ _ M Ω' _ _ φ N U₀ R _ X p u₀ a b H J s t sq hom imm crd hdiv W hWU hW hne
  obtain ⟨V, rfl⟩ : ∃ V : U₀.toScheme.Opens, U₀.ι ''ᵁ V = W :=
    ⟨U₀.ι ⁻¹ᵁ W, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]; exact inf_eq_right.2 hWU⟩
  have hV : IsAffineOpen V := U₀.ι.isAffineOpen_iff_of_isOpenImmersion.1 hW
  have hmem : ∀ z : N.Z, (b ≫ U₀.ι) z ∈ U₀.ι ''ᵁ V ↔ b z ∈ V := fun z =>
    Iff.of_eq (congrArg (b z ∈ ·) (U₀.ι.preimage_image_eq V))
  refine ⟨fun z _ => ?_, fun i hi => ?_⟩
  · have hz : a z ∈ ⨆ i ∈ (Set.univ : Set J), nonzeroLocus (s i) := by rw [imm.1]; trivial
    simp only [Set.mem_univ, iSup_pos, TopologicalSpace.Opens.mem_iSup] at hz
    obtain ⟨i, hi⟩ := hz
    exact ⟨i, (hdiv i z).2 hi⟩
  obtain ⟨hD, r, hr, hgen⟩ := imm.2 i trivial
  have hU : IsAffineOpen (a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V) := by
    have : IsAffine _ := isAffineOpen_top (Sp R)
    have : IsAffine _ := hV
    have : IsAffine _ := hD
    exact .of_isIso (Scheme.Hom.isPullback_resLE sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top
      rfl).isoPullback.hom
  have hset : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z) =
      {z' | (b ≫ U₀.ι) z' ∈ U₀.ι ''ᵁ V ∧ N.Div t i z'} :=
    Set.ext fun z => and_comm.trans (and_congr (hmem z).symm (hdiv i z).symm)
  refine ⟨_, hU, hset, le_antisymm (fun x hx => ?_) (Algebra.adjoin_le ?_)⟩
  · have hgp : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀.ι ''ᵁ V := by
      have e := congrArg (fun f => f (IsLocalRing.closedPoint Ω')) (show N.pt ≫ b ≫ U₀.ι = _ from hom)
      rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
      refine (congrArg (· ∈ U₀.ι ''ᵁ V) e).mpr ?_
      exact M.top_le_preimage_pt hne (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    have hUne : ((a ⁻¹ᵁ nonzeroLocus (s i) ⊓ b ⁻¹ᵁ V : N.Z.Opens) : Set N.Z).Nonempty :=
      ⟨_, hset.ge ⟨hgp, div_genericPoint hi⟩⟩
    have hpt := N.top_le_preimage_pt hUne
    have ha : ⊤ ≤ (N.pt ≫ a) ⁻¹ᵁ nonzeroLocus (s i) := le_preimage_comp _ a inf_le_left hpt
    have hb : ⊤ ≤ (N.pt ≫ b) ⁻¹ᵁ V := le_preimage_comp _ b inf_le_right hpt
    set A := Algebra.adjoin o (φ '' (M.ringOn (U₀.ι ''ᵁ V : M.Z.Opens) : Set Ω) ∪ Set.range fun j => t j / t i)
    have hB : ∀ g, valR (N.pt ≫ b) V g ∈ A := fun g =>
      Algebra.subset_adjoin (Or.inl (hom.valR_mem_image_ringOn hb g))
    have hA : ∀ g, valR (N.pt ≫ a) (nonzeroLocus (s i)) g ∈ A := fun g => by
      have : Subring.closure (Set.range (constFn p (nonzeroLocus (s i))) ∪ Set.range r) ≤
          A.toSubring.comap (valMap _ _ ha).hom := by
        rw [Subring.closure_le]
        rintro _ (⟨c, rfl⟩ | ⟨j, rfl⟩)
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, valR_constFn _ _ _ ha, Category.assoc, sq.w, ← Category.assoc, ← valR_constFn _ _ _ hb]
          exact hB _
        · show (valMap _ _ ha).hom _ ∈ A
          rw [← valR_eq, eq_div_of_mul_eq hi (CrdCalc.crd_ratio crd (hr j) ha).symm]
          exact Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      rw [valR_eq _ _ ha]
      exact this (hgen.ge (Subring.mem_top g))
    have po := (isIso_pushoutSection_iff sq (US := ⊤) (UT := V) (UX := nonzeroLocus (s i)) le_top le_top rfl).1
      (isIso_pushoutSection_of_isAffineOpen sq _ _ _ (isAffineOpen_top _) hV hD)
    have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
    have hle : (⊤ : Subring _) ≤ A.toSubring.comap (valMap _ _ hpt).hom := by
      rw [← hcl, Subring.closure_le]
      rintro _ (⟨g, rfl⟩ | ⟨g, rfl⟩)
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hA g
      · show (valMap _ _ hpt).hom _ ∈ A
        rw [← valR_eq, valR_appLE _ _ _ hpt]
        exact hB g
    obtain ⟨f, rfl⟩ := (mem_ringOn_iff_exists hUne).1 hx
    rw [valF_eq_valR, valR_eq _ _ hpt]
    exact hle (Subring.mem_top f)
  · rintro _ (⟨x, hx, rfl⟩ | ⟨j, rfl⟩)
    · exact mem_ringOn.2 fun z hz => hom.map_mem_O (mem_ringOn.1 hx _ (hset.le hz).1)
    · exact mem_ringOn.2 fun z hz => (hset.le hz).2.2 j

end GlobalTheory.ZH.RatModel
end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersionBaseChange_projChart : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (U₀ : M.Z.Opens) (R : Type) [CommRing R] (X : Scheme.{0}) (p : X ⟶ Sp R) (u₀ : U₀.toScheme ⟶ Sp R) (a : N.Z ⟶ X) (b : N.Z ⟶ U₀.toScheme) (H : LB X) (J : Type) (s : J → H.Sec) (t : J → Ω'), IsPullback a b p u₀ → M.IsHom N φ (b ≫ U₀.ι) → ImmBy p H s Set.univ → Crd H s (N.pt ≫ a) t → (∀ (i : J) (z : N.Z), N.Div t i z ↔ a z ∈ nonzeroLocus (s i)) → ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t := by
  atlas_forward_decl GlobalTheory.ZH.RatModel.projChart_of_isPullback
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isLB_genTriv_of_ratios' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (ι : Type) (U : ι → M.Z.Opens) (d : ι → Ω), ⨆ k, U k = ⊤ → (∀ k, d k ≠ 0) → (∀ k k', ∀ z ∈ U k ⊓ U k', d k' / d k ∈ M.O z) → ∃ g : ∀ k k', Γ(M.Z, U k ⊓ U k')ˣ, (⟨ι, U, g⟩ : LB M.Z).IsLB ∧ M.GenTriv ⟨ι, U, g⟩ d := by
  first | exact @GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | exact GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios | (intros; apply GlobalTheory.ZH.RatModel.exists_isLB_genTriv_of_ratios <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericTrivialisation_section_and_pullback : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω), M.GenTriv H d → (∀ x : Ω, (∀ k, ∀ z ∈ H.U k, x / d k ∈ M.O z) → ∃ σ : H.Sec, M.HasVal d σ x) ∧ ∀ (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N : RatModel o Ω') (a : N.Z ⟶ M.Z), M.IsHom N φ a → N.GenTriv (H.pull a) fun k => φ (d (k PUnit.unit)) := by
  first | exact @GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | exact GlobalTheory.ZH.RatModel.genTriv_sec_and_pull | (intros; apply GlobalTheory.ZH.RatModel.genTriv_sec_and_pull <;> assumption)
end

section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (H : LB M.Z) (d : H.ι → Ω) (J : Type) (σ : J → H.Sec) (t : J → Ω) (k : Type) [CommRing k] (p : M.Z ⟶ Sp k) (ψ : k →+* Ω), H.IsLB → M.GenTriv H d → (∀ j, M.HasVal d (σ j) (t j)) → (∀ l, ∀ z ∈ H.U l, ∃ i, t i ≠ 0 ∧ d l / t i ∈ M.O z) → M.pt ≫ p = spMap ψ → (∀ i, t i ≠ 0 → ∃ U : M.Z.Opens, IsAffineOpen U ∧ (U : Set M.Z) = {z | M.Div t i z} ∧ ∀ x ∈ M.ringOn U, x ∈ Subring.closure (Set.range ψ ∪ Set.range fun j => t j / t i)) → ImmBy p H σ Set.univ := by
  first | exact @GlobalTheory.ZH.RatModel.immBy_of_div | exact GlobalTheory.ZH.RatModel.immBy_of_div | (intros; apply GlobalTheory.ZH.RatModel.immBy_of_div <;> assumption)
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem IsHom.apply_genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (h : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  have e : (N.pt ≫ q) (IsLocalRing.closedPoint Ω') =
      (spMap φ.toRingHom ≫ M.pt) (IsLocalRing.closedPoint Ω') := by
    rw [show N.pt ≫ q = _ from h]
  have e' : q (N.pt (IsLocalRing.closedPoint Ω')) = M.pt (spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) := e
  rw [e']
  exact M.top_le_preimage_pt hW (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial

theorem IsHom.comp_id {N Q : RatModel o Ω'} {q : N.Z ⟶ M.Z} {a : Q.Z ⟶ N.Z} (h : M.IsHom N φ q)
    (ha : N.IsHom Q (AlgHom.id o Ω') a) : M.IsHom Q φ (a ≫ q) := by
  simpa only [AlgHom.id_comp] using h.comp ha

theorem exists_isHom_of_projChart {N₁ N₂ : RatModel o Ω'} {q₁ : N₁.Z ⟶ M.Z} {q₂ : N₂.Z ⟶ M.Z}
    (h₁ : M.IsHom N₁ φ q₁) (h₂ : M.IsHom N₂ φ q₂) {J : Type} [Finite J] {t : J → Ω'}
    (h : ∀ z, ∃ (W : M.Z.Opens) (i : J), q₁ z ∈ W ∧ N₁.Div t i z ∧ M.ProjChart N₂ φ q₂ W t) :
    ∃ a, N₂.IsHom N₁ (AlgHom.id o Ω') a := by
  refine exists_isHom_of_local fun z => ?_
  obtain ⟨W, i, hz, hi, hc⟩ := h z
  obtain ⟨U, hU, hD, hR⟩ := hc.2 i hi.1
  refine ⟨q₁ ⁻¹ᵁ W ⊓ ⟨_, N₁.isOpen_setOf_div t i⟩, U, ⟨hz, hi⟩, hU,
    ⟨genericPoint N₂.Z, hD ▸ ⟨h₂.apply_genericPoint_mem ⟨_, hz⟩, div_genericPoint hi.1⟩⟩,
    fun x hx => mem_ringOn.2 fun w hw => ?_⟩
  rw [hR] at hx
  refine (Algebra.adjoin_le ?_ : _ ≤ N₁.O w) hx
  rintro _ (⟨y, hy, rfl⟩ | ⟨j, rfl⟩)
  · exact h₁.map_mem_O (ringOn_le_O (M := M) (U := W) (z := q₁ w) hw.1 hy)
  · exact hw.2.2 j

theorem exists_isPullback_of_projChart_of_isPullback {N P Q : RatModel o Ω'} {U₀ : M.Z.Opens} {b : N.Z ⟶ U₀.toScheme}
    {f : P.Z ⟶ M.Z} {ι : Q.Z ⟶ P.Z} [IsOpenImmersion ι] {g : Q.Z ⟶ U₀.toScheme} (hι : P.IsHom Q (AlgHom.id o Ω') ι)
    (hpb : IsPullback ι g f U₀.ι) {J : Type} [Finite J] {t : J → Ω'} (hb : M.IsHom N φ (b ≫ U₀.ι))
    (hf : M.IsHom P φ f)
    (h : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty →
      M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) :
    ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  have hU : ∀ {X : Scheme.{0}} (b : X ⟶ U₀.toScheme) (z : X), (b ≫ U₀.ι) z ∈ U₀ := fun b z => by
    rw [Scheme.Hom.comp_apply]
    exact (b z).2
  obtain ⟨a₀, ha₀⟩ : ∃ a, P.IsHom N (AlgHom.id o Ω') a := by
    refine exists_isHom_of_projChart hb hf (t := t) fun z => ?_
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset (hU b z)
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h1.1 z hz
    exact ⟨W, i, hz, hi, h2⟩
  have hfι : M.IsHom Q φ (ι ≫ f) := hf.comp_id hι
  obtain ⟨c, hc⟩ : ∃ c, N.IsHom Q (AlgHom.id o Ω') c := by
    refine exists_isHom_of_projChart hfι hb (t := t) fun z => ?_
    have hz0 : (ι ≫ f) z ∈ U₀ := hpb.w ▸ hU g z
    obtain ⟨W, hW, hz, hle⟩ := exists_isAffineOpen_mem_and_subset hz0
    obtain ⟨h1, h2⟩ := h W hle hW ⟨_, hz⟩
    obtain ⟨i, hi⟩ := h2.1 (ι z) (by rwa [Scheme.Hom.comp_apply] at hz)
    refine ⟨W, i, hz, ⟨hi.1, fun j => ?_⟩, h1⟩
    rw [hι.O_eq z]
    exact hi.2 j
  have hw : a₀ ≫ f = b ≫ U₀.ι := IsHom.unique (φ := φ) (hf.comp_id ha₀) hb
  obtain ⟨a₁, e₁, e₂⟩ : ∃ a₁ : N.Z ⟶ Q.Z, a₁ ≫ ι = a₀ ∧ a₁ ≫ g = b :=
    ⟨hpb.lift a₀ b hw, hpb.lift_fst _ _ _, hpb.lift_snd _ _ _⟩
  have ha₁ : Q.IsHom N (AlgHom.id o Ω') a₁ := by
    unfold IsHom at hι ha₀ ⊢
    have e : spMap (AlgHom.id o Ω').toRingHom = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp] at hι ha₀ ⊢
    rw [← cancel_mono ι, Category.assoc, e₁, hι, ha₀]
  have h₁ : a₁ ≫ c = 𝟙 N.Z := IsHom.unique (φ := AlgHom.id o Ω') (hc.comp_id ha₁) N.isHom_id
  have h₂ : c ≫ a₁ = 𝟙 Q.Z := IsHom.unique (φ := AlgHom.id o Ω') (ha₁.comp_id hc) Q.isHom_id
  have : IsIso a₁ := ⟨c, h₁, h₂⟩
  refine ⟨a₀, ha₀, ?_⟩
  exact hpb.of_iso (asIso a₁).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp [← e₁]) (by simp [← e₂]) (by simp) (by simp)

theorem exists_isPullback_of_projChart :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  intro o Ω _ _ _ M Ω' _ _ φ _ N P U₀ b f J _ t hb hf h
  have hbU : (b ≫ U₀.ι) (genericPoint N.Z) ∈ U₀ := by
    rw [Scheme.Hom.comp_apply]
    exact (b _).2
  have hV : ((f ⁻¹ᵁ U₀ : P.Z.Opens) : Set P.Z).Nonempty := ⟨_, hf.apply_genericPoint_mem ⟨_, hbU⟩⟩
  exact @exists_isPullback_of_projChart_of_isPullback o Ω _ _ _ M Ω' _ _ φ N P (P.openPart _ hV) U₀ b f
    (f ⁻¹ᵁ U₀).ι (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ U₀).ι)) (f ∣_ U₀) (P.isHom_openPart _ hV)
    (isPullback_morphismRestrict f U₀).flip J _ t hb hf h

end GlobalTheory.ZH.RatModel
end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullback_of_projChart' : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') [IsNoetherianRing o] (N P : RatModel o Ω') (U₀ : M.Z.Opens) (b : N.Z ⟶ U₀.toScheme) (f : P.Z ⟶ M.Z) (J : Type) [Finite J] (t : J → Ω'), M.IsHom N φ (b ≫ U₀.ι) → M.IsHom P φ f → (∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart N φ (b ≫ U₀.ι) W t ∧ M.ProjChart P φ f W t) → ∃ a₀ : N.Z ⟶ P.Z, P.IsHom N (AlgHom.id o Ω') a₀ ∧ IsPullback a₀ b f U₀.ι := by
  atlas_forward_decl GlobalTheory.ZH.RatModel.exists_isPullback_of_projChart
end

section
section
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH

noncomputable section
namespace GlobalTheory.ZH.RatModel

open GlobalTheory.Points

theorem IsHom.valF_appLE {o Ω Ω' : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Field Ω'] [Algebra o Ω']
    {M : RatModel o Ω} {M' : RatModel o Ω'} {φ : Ω →ₐ[o] Ω'} {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' φ f)
    {U : M.Z.Opens} {V : M'.Z.Opens} (e : V ≤ f ⁻¹ᵁ U) (hV : (V : Set M'.Z).Nonempty) (g : Γ(M.Z, U)) :
    M'.res V hV ((f.appLE U V e).hom g) = φ (valF M.pt U g) := by
  rw [res_apply, ← hf.valF_app ⟨_, e hV.some_mem⟩ g]
  exact (valR_appLE M'.pt f e (M'.top_le_preimage_pt hV) g).trans (valR_comp M'.pt f U g)

theorem crd_mulVec_of_hasVal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  intro o Ω _ _ _ M Ω' _ _ φ N N' a q W H d J _ st σ t u c ha hq hW ht hu htu R _ x w hx
  obtain ⟨k, e, hk, hw⟩ := hx
  have ea : (H.pull a).U k ≤ a ⁻¹ᵁ H.U (k PUnit.unit) := LB.wchart_le H _ k PUnit.unit
  have eq : (H.pull a).U k ≤ q ⁻¹ᵁ W := fun z _ => hW z
  refine ⟨k PUnit.unit, e, le_preimage_comp x a ea hk, fun i => ?_⟩
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  obtain ⟨y⟩ : Nonempty (PrimeSpectrum R) := inferInstance
  have hC : (((H.pull a).U k : N'.Z.Opens) : Set N'.Z).Nonempty := ⟨x y, hk (x := y) trivial⟩
  have key : (a.appLE _ _ ea).hom ((st i).f (k PUnit.unit)) =
      ∑ j, (q.appLE _ _ eq).hom (c i j) * (σ j).f k := by
    apply N'.res_injective _ hC
    rw [map_sum, ha.valF_appLE ea hC, ht i _ ⟨_, ea hC.some_mem⟩, htu]
    simp only [map_mul, hq.valF_appLE eq hC, AlgHom.id_apply, Matrix.mulVec, dotProduct, Matrix.map_apply,
      Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [res_apply, hu j k hC, mul_div_assoc]
  rw [← valR_appLE x a ea hk, key, valR_eq x _ hk, map_sum, Finset.mul_sum]
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, ← valR_eq x _ hk, ← valR_eq x _ hk, valR_appLE x q eq hk, hw j, mul_left_comm]

end GlobalTheory.ZH.RatModel
end
end

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homogeneousCoordinates_mulVec_of_genericValue : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (Ω' : Type) [Field Ω'] [Algebra o Ω'] (φ : Ω →ₐ[o] Ω') (N N' : RatModel o Ω') (a : N'.Z ⟶ N.Z) (q : N'.Z ⟶ M.Z) (W : M.Z.Opens) (H : LB N.Z) (d : H.ι → Ω') (J : Type) [Fintype J] (st : J → H.Sec) (σ : J → (H.pull a).Sec) (t u : J → Ω') (c : Matrix J J Γ(M.Z, W)), N.IsHom N' (AlgHom.id o Ω') a → M.IsHom N' φ q → (∀ z, q z ∈ W) → (∀ j, N.HasVal d (st j) (t j)) → (∀ j, N'.HasVal (H := H.pull a) (fun k => d (k PUnit.unit)) (σ j) (u j)) → t = (c.map fun g => φ (valF M.pt W g)).mulVec u → ∀ (R : Type) [CommRing R] (x : Sp R ⟶ N'.Z) (w : J → R), Crd (H.pull a) σ x w → Crd H st (x ≫ a) ((c.map (valR (x ≫ q) W)).mulVec w) := by
  atlas_forward_decl GlobalTheory.ZH.RatModel.crd_mulVec_of_hasVal
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH
open GlobalTheory.Points
namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
  {Ω' : Type} [Field Ω'] [Algebra o Ω'] {φ : Ω →ₐ[o] Ω'}

theorem ProjChart.closure_eq_top {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) {J : Type} {t : J → Ω'} (h : M.ProjChart N φ q W t) :
    (∃ j, t j ≠ 0) ∧ Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = t j / t i}) = ⊤ := by
  have hg : q (genericPoint N.Z) ∈ W := by
    have h1 : ⊤ ≤ (N.pt ≫ q) ⁻¹ᵁ W := by
      rw [hq]
      exact le_preimage_comp _ _ (M.top_le_preimage_pt hW) (le_preimage_top _)
    rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
    exact h1 (x := IsLocalRing.closedPoint Ω') trivial
  obtain ⟨i, hi⟩ := h.1 _ hg
  obtain ⟨U, hU, hD, hR⟩ := h.2 i hi.1
  have hne : (U : Set N.Z).Nonempty := ⟨genericPoint N.Z, hD ▸ ⟨hg, hi⟩⟩
  refine ⟨⟨i, hi.1⟩, top_unique fun x _ => ?_⟩
  have key : ∀ a : Γ(N.Z, U), valF N.pt U a ∈ Subfield.closure (Set.range φ ∪ {x | ∃ i j, x = t j / t i}) := by
    intro a
    have ha : valF N.pt U a ∈ N.ringOn U := (mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩
    rw [hR] at ha
    generalize valF N.pt U a = y at ha
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨y, -, rfl⟩ | ⟨j, rfl⟩
      · exact Subfield.subset_closure (Or.inl ⟨y, rfl⟩)
      · exact Subfield.subset_closure (Or.inr ⟨i, j, rfl⟩)
    | algebraMap r => exact Subfield.subset_closure (Or.inl ⟨_, φ.commutes r⟩)
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  obtain ⟨a, b, -, rfl⟩ := exists_eq_div hU hne x
  exact div_mem (key a) (key b)

theorem IsHom.genericPoint_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {W : M.Z.Opens}
    (hW : (W : Set M.Z).Nonempty) : q (genericPoint N.Z) ∈ W := by
  have h1 : ⊤ ≤ (N.pt ≫ q) ⁻¹ᵁ W := by
    rw [hq]
    exact le_preimage_comp _ _ (M.top_le_preimage_pt hW) (le_preimage_top _)
  rw [← N.pt_apply (IsLocalRing.closedPoint Ω')]
  exact h1 (x := IsLocalRing.closedPoint Ω') trivial

theorem IsHom.mulVec_div_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) {J : Type} [Fintype J]
    {u : J → Ω'} {i : J} {z : N.Z} (h : N.Div u i z) {m : Matrix J J Ω} (hm : ∀ j k, m j k ∈ M.O (q z)) (j : J) :
    (m.map φ).mulVec u j / u i ∈ N.O z := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_div, mul_div_assoc, Matrix.map_apply]
  exact Subalgebra.sum_mem _ fun k _ => mul_mem (hq.map_mem_O (hm j k)) (h.2 k)

structure Lat.Frame {J : Type} [Fintype J] (EE : M.Lat J) where
  W : M.Z.Opens
  aff : IsAffineOpen W
  ne : (W : Set M.Z).Nonempty
  B : Matrix J J Ω
  basis : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range B)
  c : Matrix J J Γ(M.Z, W)
  c_inv : c.map (valF M.pt W) * B = 1

theorem Lat.exists_frame {J : Type} [Fintype J] (EE : M.Lat J) (hm : ∀ z i, Pi.single i (1 : Ω) ∈ EE.E z)
    (z : M.Z) : ∃ l : EE.Frame, z ∈ l.W := by
  obtain ⟨U, b, hz, hb, h⟩ := EE.loc z
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hz
  have hu : IsUnit b.det := hb.isUnit
  obtain ⟨c, hc⟩ := M.exists_matrix_map_valF (U := W) ⟨z, hzW⟩ b⁻¹ fun w hw i j => by
    have := mul_inv_apply_mem_of_span_le (M.O w) (b := 1) (B := b) (c := b⁻¹) (Submodule.span_le.2 (by
      rintro _ ⟨i, rfl⟩
      rw [← h w (hle hw)]
      have e : (1 : Matrix J J Ω) i = Pi.single i 1 := by
        ext j
        simp [Matrix.one_apply, Pi.single_apply, eq_comm]
      rw [e]
      exact hm w i)) (Matrix.mul_nonsing_inv b hu) i j
    rwa [Matrix.one_mul] at this
  refine ⟨⟨W, hW, ⟨z, hzW⟩, b, fun w hw => h w (hle hw), c, ?_⟩, hzW⟩
  rw [← Matrix.nonsing_inv_mul b hu, ← hc]
  congr 1
  ext i j
  exact (M.res_apply W ⟨z, hzW⟩ (c i j)).symm

def Lat.stdFrame {J : Type} [Fintype J] (EE : M.Lat J) {W : M.Z.Opens} (hW : IsAffineOpen W)
    (hne : (W : Set M.Z).Nonempty)
    (h : ∀ z ∈ W, EE.E z = Submodule.span (M.O z) (Set.range fun i => Pi.single i (1 : Ω))) : EE.Frame where
  W := W
  aff := hW
  ne := hne
  B := 1
  basis z hz := by
    rw [h z hz]
    congr 2
    ext i j
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  c := 1
  c_inv := by
    rw [Matrix.mul_one]
    exact Matrix.map_one _ (valR_zero _ _ (M.top_le_preimage_pt hne)) (valR_one _ _ (M.top_le_preimage_pt hne))

namespace Lat.Frame
variable {J : Type} [Fintype J] {EE : M.Lat J}

abbrev co (l : EE.Frame) (φ : Ω →ₐ[o] Ω') (t : J → Ω') : J → Ω' := (l.B.map φ).mulVec t

theorem eq_mulVec (l : EE.Frame) (t : J → Ω') :
    t = ((l.c.map (valF M.pt l.W)).map φ).mulVec (l.co φ t) := by
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul (f := φ), l.c_inv, Matrix.map_one _ (map_zero φ) (map_one φ),
    Matrix.one_mulVec]

theorem div_mem {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) (l l' : EE.Frame) {t : J → Ω'}
    {i : J} {z : N.Z} (hz : q z ∈ l.W) (hz' : q z ∈ l'.W) (h : N.Div (l.co φ t) i z) (j : J) :
    l'.co φ t j / l.co φ t i ∈ N.O z := by
  have e : l'.co φ t = ((l'.B * l.c.map (valF M.pt l.W)).map φ).mulVec (l.co φ t) := by
    rw [Matrix.map_mul (f := φ), ← Matrix.mulVec_mulVec, ← l.eq_mulVec t]
  rw [e]
  exact hq.mulVec_div_mem h (mul_inv_apply_mem_of_span_le _ ((l'.basis _ hz').symm.trans (l.basis _ hz)).le
    (mul_eq_one_comm.1 l.c_inv)) j

theorem div_mem' {N : RatModel o Ω'} {q : N.Z ⟶ M.Z} (hq : M.IsHom N φ q) (l : EE.Frame) {t : J → Ω'}
    {i : J} {z : N.Z} (hz : q z ∈ l.W) (h : N.Div (l.co φ t) i z) (j : J) :
    t j / l.co φ t i ∈ N.O z := by
  have := hq.mulVec_div_mem h (m := l.c.map (valF M.pt l.W)) (fun j k => valF_mem_O hz _) j
  rwa [← l.eq_mulVec t] at this

end Lat.Frame
end RatModel

theorem nonempty_clos : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → Nonempty (Clos ρ M U₀ EE) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB
  have := ArithBase.ded (o := o) (Ω := Ω)
  have hne := hB.ov.ne
  obtain ⟨u₀, hu₀⟩ := GlobalTheory.T.exists_hom_spec_of_le_ringOn' o Ω M U₀ S.R hne hB.ov.le
  have himm := ThetaSys.Real.immBy_basis hL o Ω S ρ
  have hH : (LPow ρ.P.A ρ.P.L S.N (baseOver (Sp S.R))).IsLB := LB.isLB_linComb ρ.P.isLB _ _

  have := ρ.P.isAb.smooth
  have := ρ.P.isAb.proper
  have := ρ.P.isAb.geomConnected
  have : GeometricallyIntegral ρ.P.A.hom := grpObj_geometricallyIntegral_of_smooth _ _
  have := M.isLocallyNoetherian
  have := M.sep
  have := M.lft
  have := M.qc
  have : IsIntegral U₀.toScheme := (M.openPart U₀ hne).integral
  have : IsIntegral (pullback ρ.P.A.hom u₀) :=
    GeometricallyIntegral.isIntegral_of_isLocallyNoetherian (pullback.snd ρ.P.A.hom u₀)
  have : IsDominant U₀.ι := by
    have : IsDominant (M.ptOpen U₀ hne ≫ U₀.ι) := by rw [M.ptOpen_ι]; infer_instance
    exact IsDominant.of_comp (M.ptOpen U₀ hne) U₀.ι
  have : IsDominant (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) := inferInstance
  obtain ⟨Ω', _, _, φ, pt, hgen, honto, hpt⟩ := GlobalTheory.T.exists_functionField_of_isDominant' o Ω M _ (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι)
  let N : RatModel o Ω' :=
    { Z := pullback ρ.P.A.hom u₀
      s := (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) ≫ M.s
      sep := inferInstance
      lft := inferInstance
      qc := inferInstance
      pt := pt
      pt_s := by
        rw [← Category.assoc, hpt, Category.assoc, M.pt_s, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
        congr 2
        exact φ.comp_algebraMap
      gen := hgen
      onto := honto }
  have hN : M.IsHom N φ (pullback.snd ρ.P.A.hom u₀ ≫ U₀.ι) := hpt
  have hsq : IsPullback (snd (baseOver (Sp S.R)) ρ.P.A).left (baseOver (Sp S.R) ⊗ ρ.P.A).hom ρ.P.A.hom (𝟙 _) := by
    have e : (baseOver (Sp S.R) ⊗ ρ.P.A).hom = (fst (baseOver (Sp S.R)) ρ.P.A).left :=
      (Over.w (fst (baseOver (Sp S.R)) ρ.P.A)).symm.trans (Category.comp_id _)
    rw [e]
    exact (IsPullback.of_hasPullback _ ρ.P.A.hom).flip
  let a : N.Z ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left :=
    hsq.lift (pullback.fst ρ.P.A.hom u₀) (pullback.snd ρ.P.A.hom u₀ ≫ u₀)
      (pullback.condition.trans (Category.comp_id _).symm)
  have ha₁ : a ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = pullback.fst ρ.P.A.hom u₀ := hsq.lift_fst _ _ _
  have ha₂ : a ≫ (baseOver (Sp S.R) ⊗ ρ.P.A).hom = pullback.snd ρ.P.A.hom u₀ ≫ u₀ := hsq.lift_snd _ _ _
  have hpb : IsPullback a (pullback.snd ρ.P.A.hom u₀) (baseOver (Sp S.R) ⊗ ρ.P.A).hom u₀ := by
    refine IsPullback.of_right ?_ ha₂ hsq
    rw [ha₁, Category.comp_id]
    exact IsPullback.of_hasPullback _ _
  obtain ⟨t, ht⟩ := CrdCalc.crd_exists hH ρ.s (N.pt ≫ a)
  obtain ⟨hdiv, hval⟩ := GlobalTheory.T.div_iff_mem_nonzeroLocus_and_crd_ratio o Ω' N _ a _ _ ρ.s t hH (by simpa using himm.1) ht
  have hchN := GlobalTheory.T.closedImmersionBaseChange_projChart o Ω M Ω' φ N U₀ _ _ _ u₀ a _ _ _ ρ.s t hpb hN himm ht hdiv
  obtain ⟨W₀, hW₀, hz₀, hle₀⟩ := exists_isAffineOpen_mem_and_subset (U := U₀) hne.some_mem
  obtain ⟨ht0, htop⟩ := (hchN W₀ hle₀ hW₀ ⟨_, hz₀⟩).closure_eq_top hN ⟨_, hz₀⟩

  obtain ⟨P, f, hf, hproj, hP⟩ := GlobalTheory.T.exists_projBundle_closure_alt o Ω M Ω' φ S.J EE t hB.ov.proj ht0 htop
  have hch : ∀ l : EE.Frame, M.ProjChart P φ f l.W (l.co φ t) := fun l => hP l.W l.B l.aff l.ne l.basis
  have hstd : ∀ (W : M.Z.Opens) (hW : IsAffineOpen W) (hWne : (W : Set M.Z).Nonempty) (h : _),
      (EE.stdFrame hW hWne h).co φ t = t := fun W hW hWne h => by
    show ((1 : Matrix S.J S.J Ω).map φ).mulVec t = t
    rw [Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.one_mulVec]
  have hchP : ∀ W : M.Z.Opens, W ≤ U₀ → IsAffineOpen W → (W : Set M.Z).Nonempty → M.ProjChart P φ f W t :=
    fun W hle hW hWne => by
      have := hch (EE.stdFrame hW hWne fun z hz => hB.ee.1 z (hle hz))
      rwa [hstd] at this
  obtain ⟨a₀, ha₀, hcart⟩ := GlobalTheory.T.exists_isPullback_of_projChart' o Ω M Ω' φ N P U₀ _ f S.J t hN hf
    fun W hle hW hWne => ⟨hchN W hle hW hWne, hchP W hle hW hWne⟩

  let I : Type := {k : EE.Frame × S.J // k.1.co φ t k.2 ≠ 0}
  let d : I → Ω' := fun k => k.1.1.co φ t k.1.2
  let U : I → P.Z.Opens := fun k => f ⁻¹ᵁ k.1.1.W ⊓ ⟨_, P.isOpen_setOf_div (k.1.1.co φ t) k.1.2⟩
  have hUcov : ⨆ k, U k = ⊤ := top_unique fun z _ => by
    obtain ⟨l, hl⟩ := EE.exists_frame hB.mem (f z)
    obtain ⟨i, hi⟩ := (hch l).1 z hl
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(l, i), hi.1⟩, hl, hi⟩
  obtain ⟨g, hLB, hG⟩ := GlobalTheory.T.exists_isLB_genTriv_of_ratios' o Ω' P I U d hUcov (fun k => k.2)
    fun k k' z hz => RatModel.Lat.Frame.div_mem hf k.1.1 k'.1.1 hz.1.1 hz.2.1 hz.1.2 k'.1.2
  let O1 : LB P.Z := ⟨I, U, g⟩
  obtain ⟨hsec, hpull⟩ := GlobalTheory.T.genericTrivialisation_section_and_pullback o Ω' P O1 d hG
  choose st hst using fun j => hsec (t j) fun k z hz => RatModel.Lat.Frame.div_mem' hf k.1.1 hz.1 hz.2 j
  have hV : ∀ l : EE.Frame, ((f ⁻¹ᵁ l.W : P.Z.Opens) : Set P.Z).Nonempty := fun l => ⟨_, hf.genericPoint_mem l.ne⟩
  let Q : EE.Frame → RatModel o Ω' := fun l => P.openPart _ (hV l)
  have hQ : ∀ l, P.IsHom (Q l) (AlgHom.id o Ω') (f ⁻¹ᵁ l.W).ι := fun l => P.isHom_openPart _ _
  have hQf : ∀ l, M.IsHom (Q l) φ ((f ⁻¹ᵁ l.W).ι ≫ f) := fun l => by
    have := hf.comp (hQ l)
    rwa [AlgHom.id_comp] at this
  have hGQ : ∀ l, (Q l).GenTriv (O1.pull (f ⁻¹ᵁ l.W).ι) fun k => d (k PUnit.unit) :=
    fun l => hpull Ω' (AlgHom.id o Ω') (Q l) _ (hQ l)
  have hmem : ∀ (l : EE.Frame) (k : (O1.pull (f ⁻¹ᵁ l.W).ι).ι) (z : (f ⁻¹ᵁ l.W).toScheme),
      z ∈ (O1.pull (f ⁻¹ᵁ l.W).ι).U k → (f ⁻¹ᵁ l.W).ι z ∈ U (k PUnit.unit) :=
    fun l k z hz => LB.wchart_le O1 (fun _ => (f ⁻¹ᵁ l.W).ι) k PUnit.unit hz
  have hO : ∀ (l : EE.Frame) (z : (f ⁻¹ᵁ l.W).toScheme), (Q l).O z = P.O ((f ⁻¹ᵁ l.W).ι z) :=
    fun l z => @RatModel.IsHom.O_eq _ _ _ _ _ _ _ _ (hQ l) (inferInstanceAs (IsOpenImmersion (f ⁻¹ᵁ l.W).ι)) z
  have hD : ∀ (l : EE.Frame) (z : (f ⁻¹ᵁ l.W).toScheme) (u : S.J → Ω') (i : S.J),
      (Q l).Div u i z ↔ P.Div u i ((f ⁻¹ᵁ l.W).ι z) := fun l z u i => by
    simp only [RatModel.Div, hO]
  choose σ hσ using fun (l : EE.Frame) (j : S.J) => (GlobalTheory.T.genericTrivialisation_section_and_pullback o Ω' (Q l) _ _ (hGQ l)).1 (l.co φ t j)
    fun k z hz => (hO l z).ge (RatModel.Lat.Frame.div_mem hf _ l (hmem l k z hz).1 z.2 (hmem l k z hz).2 j)
  have : IsProper (f ≫ M.s) := by
    rw [hf.inducedModelMorphism_comp_structureMap]
    exact projProper _ _ _ hproj
  refine ⟨{
    u₀ := u₀
    u₀_pt := hu₀
    P := Over.mk f
    intP := P.integral
    proper := IsProper.of_comp f M.s
    proj := by
      show IsProjOver (f ≫ M.s)
      rw [hf.inducedModelMorphism_comp_structureMap]
      exact hproj
    a₀ := a₀
    cart := hcart
    O1 := O1
    isLB := hLB
    st := st
    crd := ?_
    Λ := EE.Frame
    W := fun l => l.W
    aff := fun l => l.aff
    ne := fun l => l.ne
    cover := top_unique fun z _ => TopologicalSpace.Opens.mem_iSup.2 (EE.exists_frame hB.mem z)
    B := fun l => l.B
    basis := fun l => l.basis
    c := fun l => l.c
    c_inv := fun l => l.c_inv
    σ := σ
    rel := fun l R _ _ x w hw => GlobalTheory.T.homogeneousCoordinates_mulVec_of_genericValue o Ω M Ω' φ P (Q l) _ _ l.W O1 d S.J st (σ l) t (l.co φ t) l.c (hQ l) (hQf l)
      (fun z => z.2) hst (hσ l) (l.eq_mulVec t) R x w hw
    imm := fun l => ?_ }⟩
  · rintro K _ x v ⟨a', ha', hv⟩
    have : IsIso (snd (baseOver (Sp S.R)) ρ.P.A).left := hsq.isIso_fst_of_isIso
    obtain rfl : a' = x ≫ a := by
      rw [← cancel_mono (snd (baseOver (Sp S.R)) ρ.P.A).left, ha', Category.assoc, ha₁]
    have hzU : f (a₀ (x (IsLocalRing.closedPoint K))) ∈ U₀ := by
      rw [← Scheme.Hom.comp_apply, hcart.w, Scheme.Hom.comp_apply]
      exact (pullback.snd ρ.P.A.hom u₀ (x (IsLocalRing.closedPoint K))).2
    obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset hzU
    obtain ⟨i, hi⟩ := (hchP W hle hW ⟨_, hzW⟩).1 _ hzW
    obtain ⟨hv0, hvj⟩ := hval K x v i hv (ha₀.div hi)
    let l := EE.stdFrame hW ⟨_, hzW⟩ fun z hz => hB.ee.1 z (hle hz)
    have hl : l.co φ t = t := hstd _ _ _ _
    let k : I := ⟨(l, i), by rw [hl]; exact hi.1⟩
    have hk : a₀ (x (IsLocalRing.closedPoint K)) ∈ U k := ⟨hzW, by
      show P.Div (l.co φ t) i _
      rw [hl]
      exact hi⟩
    have hk' : ⊤ ≤ (x ≫ a₀) ⁻¹ᵁ U k := (le_preimage_iff _ _).2 hk
    refine ⟨k, Units.mk0 (v i) hv0, hk', fun j => ?_⟩
    have e1 : valF P.pt (U k) ((st j).f k) = t j / t i := (hst j k ⟨_, hk⟩).trans (congrArg (t j / · i) hl)
    have e2 := RatModel.val_eq ((top_le_preimage_iff _ _).1 hk') e1
    have e3 := ha₀.val_comp x (IsLocalRing.closedPoint K) (hi.2 j)
    rw [hvj j, mul_comm]
    exact congrArg (v i * ·) (e3.symm.trans e2)
  · refine GlobalTheory.T.isClosedImmersion_of_coordinate_divisibility o Ω' (Q l) _ _ S.J (σ l) (l.co φ t) _ _ (φ.toRingHom.comp (M.res l.W l.ne))
      (LB.isLB_pull hLB _) (hGQ l) (hσ l) (fun k z hz => ?_) ?_ fun i hi => ?_
    · obtain ⟨i, hi⟩ := (hch l).1 ((f ⁻¹ᵁ l.W).ι z) z.2
      exact ⟨i, hi.1, (hO l z).ge (RatModel.Lat.Frame.div_mem hf l _ z.2 (hmem l k z hz).1 hi _)⟩
    · rw [← cancel_mono l.aff.fromSpec]
      have e : ((f ∣_ l.W) ≫ l.aff.isoSpec.hom) ≫ l.aff.fromSpec = (f ⁻¹ᵁ l.W).ι ≫ f := by
        rw [Category.assoc, l.aff.isoSpec_hom_fromSpec, morphismRestrict_ι]
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans ((hQf l).trans ?_))
      conv_lhs => rw [← specMap_valMap_fromSpec l.aff M.pt (M.top_le_preimage_pt l.ne)]
      rw [← Spec.map_comp_assoc]
      rfl
    · obtain ⟨V, hVa, hVe, hVr⟩ := (hch l).2 i hi
      have hle : V ≤ f ⁻¹ᵁ l.W := fun z hz => by
        have : z ∈ (V : Set P.Z) := hz
        rw [hVe] at this
        exact this.1
      have hVa' : IsAffineOpen ((f ⁻¹ᵁ l.W).ι ⁻¹ᵁ V) := hVa.preimage_of_isOpenImmersion _ (by simpa using hle)
      refine ⟨(f ⁻¹ᵁ l.W).ι ⁻¹ᵁ V, hVa', ?_, fun x hx => ?_⟩
      · ext z
        show (f ⁻¹ᵁ l.W).ι z ∈ (V : Set P.Z) ↔ (Q l).Div _ i z
        rw [hVe]
        exact ⟨fun h => (hD l z _ i).2 h.2, fun h => ⟨z.2, (hD l z _ i).1 h⟩⟩
      · have hx' : x ∈ P.ringOn V := RatModel.mem_ringOn.2 fun z hz =>
          (hO l ⟨z, hle hz⟩).le (RatModel.mem_ringOn.1 hx ⟨z, hle hz⟩ hz)
        rw [hVr] at hx'
        clear hx
        induction hx' using Algebra.adjoin_induction with
        | mem y hy =>
          rcases hy with ⟨y, hy, rfl⟩ | hy
          · obtain ⟨r, rfl⟩ := (RatModel.mem_ringOn_iff_exists l.ne).1 hy
            exact Subring.subset_closure (Or.inl ⟨r, congrArg φ (M.res_apply _ _ r)⟩)
          · exact Subring.subset_closure (Or.inr hy)
        | algebraMap r =>
          exact Subring.subset_closure (Or.inl ⟨constFn M.s l.W r,
            (congrArg φ ((M.res_apply _ _ _).trans (M.valF_constFn l.ne r))).trans (φ.commutes r)⟩)
        | add _ _ _ _ h1 h2 => exact add_mem h1 h2
        | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2

end GlobalTheory.ZH
end
end
