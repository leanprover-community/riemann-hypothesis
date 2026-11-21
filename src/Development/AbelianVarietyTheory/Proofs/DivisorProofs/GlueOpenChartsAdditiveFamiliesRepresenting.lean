import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WhiskerLeftEqLift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullLiftOneEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigidifiedPicardClassZeroOfLocallyZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InverseBundleGeneratorPointOfChartUnitsSections
import BuildAid.ForwardExisting

section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem AddCls.pull_unit_eq_zero {S : Scheme.{0}} {A T Z : Over S} [GrpObj A] {c : Pic (A ⊗ T).left}
    (h : AddCls A c) (t : Z ⟶ T) : CechPic.pull (lift (1 : Z ⟶ A) t).left c = 0 := by
  have h1 := h Z 1 1 t
  rw [_root_.mul_one] at h1
  exact left_eq_add.1 h1

theorem addF_separated : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → (∀ (T : Over S) (y y' : (addF A).obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ (addF A).map z.op y = (addF A).map z.op y') → y = y') := by
  intro S A _ hA T y y' h
  refine Subtype.ext (sub_eq_zero.1 (GlobalTheory.T.rigidified_picard_class_zero_of_locally_zero S A T hA (y.1 - y'.1) ?_ fun p ↦ ?_))
  · rw [map_sub, y.2.pull_unit_eq_zero, y'.2.pull_unit_eq_zero, sub_zero]
  · obtain ⟨Z, z, hz, hp, e⟩ := h p
    refine ⟨Z, z, hz, hp, ?_⟩
    rw [map_sub, sub_eq_zero]
    exact congrArg Subtype.val e

end GlobalTheory.PicGlue
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isSheaf_of_local_glue : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → Presieve.IsSheaf Scheme.zariskiTopology F := by
  intro F hext hglue
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  rintro Y P hP
  obtain ⟨(𝒰 : Scheme.OpenCover Y), rfl⟩ := Scheme.exists_cover_of_mem_pretopology hP
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  choose jj q hq using 𝒰.exists_eq
  refine existsUnique_of_exists_of_unique ?_ ?_
  · obtain ⟨y₀, hy₀⟩ := hglue Y Y (fun p => 𝒰.X (jj p)) (fun p => 𝒰.f (jj p)) (fun p => x (jj p))
      (fun p => inferInstance) (fun p => ⟨p, q p, hq p⟩)
      (fun i k Z a b h => hx (jj i) (jj k) Z a b h)
    refine ⟨y₀, fun i => hext _ _ _ fun r => ?_⟩
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := 𝒰.f i)
      (g := 𝒰.f (jj (𝒰.f i r))) r (q (𝒰.f i r)) (hq _).symm
    refine ⟨_, pullback.fst (𝒰.f i) (𝒰.f (jj (𝒰.f i r))), inferInstance, ⟨w, hw⟩, ?_⟩
    rw [← FunctorToTypes.map_comp_apply, ← op_comp, pullback.condition, op_comp,
      FunctorToTypes.map_comp_apply, hy₀]
    exact (hx _ _ _ _ _ pullback.condition).symm
  · intro y y' h h'
    refine hext Y y y' fun p => ?_
    exact ⟨𝒰.X (jj p), 𝒰.f (jj p), inferInstance, ⟨q p, hq p⟩, (h _).trans (h' _).symm⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSheaf_of_open_immersion_local_glue : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → Presieve.IsSheaf Scheme.zariskiTopology F := by
  atlas_forward_decl GlobalTheory.isSheaf_of_local_glue
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_universal_of_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) := by
  intro F hsep hglue Ix U x inj hW cov
  have hF : Presieve.IsSheaf Scheme.zariskiTopology F := GlobalTheory.T.isSheaf_of_open_immersion_local_glue F hsep hglue
  let W : ∀ (_ : Ix) (Z : Scheme.{0}), F.obj (op Z) → Z.Opens :=
    fun i Z y => Classical.choose (hW i Z y)
  have hWs : ∀ i (Z : Scheme.{0}) (y : F.obj (op Z)) (Y : Scheme.{0}) (a : Y ⟶ Z),
      (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W i Z y :=
    fun i Z y => Classical.choose_spec (hW i Z y)
  have hrep : F.IsRepresentable := by
    refine GeneratorFunctor.isRepresentable_of_charts F hF U x W ?_ ?_ ?_
    · intro j Z y Z' a
      rw [Set.range_subset_iff]
      refine ((hWs j Z y Z' a).symm.trans ?_)
      exact ⟨fun ⟨u, hu⟩ => ⟨u, hu.symm⟩, fun ⟨u, hu⟩ => ⟨u, hu.symm⟩⟩
    · intro j Z g g' h
      exact inj j Z g g' h
    · intro Z y z
      obtain ⟨i, Y, a, u, ⟨q, rfl⟩, h⟩ := cov Z y z
      exact ⟨i, (hWs i Z y Y a).1 ⟨u, h⟩ q⟩
  refine ⟨F.reprX, F.reprx, fun T y => ?_⟩
  refine ⟨F.representableBy.homEquiv.symm y, ?_, ?_⟩
  · have := F.representableBy.homEquiv_eq (F.representableBy.homEquiv.symm y)
    rw [Equiv.apply_symm_apply] at this
    exact this.symm
  · intro g hg
    apply F.representableBy.homEquiv.injective
    rw [Equiv.apply_symm_apply, F.representableBy.homEquiv_eq, ← hg]
    rfl

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_universal_of_zariskiSheaf_openCharts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) := by
  atlas_forward_decl GlobalTheory.exists_universal_of_charts
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem small_of_separated_of_open_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ T : Scheme.{0}ᵒᵖ, Small.{0} (F.obj T) := by
  intro F hsep Ix U x hchart hcov T
  let S : F.obj T → Set (Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) :=
    fun y => {q | F.map q.2.1.ι.op y = F.map q.2.2.op (x q.1)}
  refine small_of_injective (f := S) ?_
  intro y y' h
  apply hsep T.unop y y'
  intro p
  obtain ⟨i, Y, a, u, hp, ha⟩ := hcov T.unop y p
  obtain ⟨W, hW⟩ := hchart i T.unop y
  have hpW : p ∈ W := by
    obtain ⟨q, rfl⟩ := hp
    exact (hW Y a).1 ⟨u, ha⟩ q
  obtain ⟨u', hu'⟩ := (hW W.toScheme W.ι).2 (fun q => by
    have hq : W.ι q ∈ Set.range W.ι := Set.mem_range_self q
    rwa [W.range_ι] at hq)
  have hmem : (⟨i, W, u'⟩ : Σ (i : Ix) (V : T.unop.Opens), (V.toScheme ⟶ U i)) ∈ S y := hu'
  rw [h] at hmem
  refine ⟨W.toScheme, W.ι, inferInstance, ?_, ?_⟩
  · rw [W.range_ι]; exact hpW
  · exact hu'.trans hmem.symm

end GlobalTheory.PicGlue
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_of_separated_presheaf_open_charts : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ T : Scheme.{0}ᵒᵖ, Small.{0} (F.obj T) := by
  atlas_forward_decl GlobalTheory.PicGlue.small_of_separated_of_open_charts
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem charts_represented_open_cover : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1) (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) → ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F Ix U x hinj hW hcov B x₀ hrep
  have uniq : ∀ (T : Scheme.{0}) (g g' : T ⟶ B), F.map g.op x₀ = F.map g'.op x₀ → g = g' :=
    fun T g g' h => (hrep T (F.map g'.op x₀)).unique h rfl
  choose j hj using fun i => (hrep (U i) (x i)).exists
  refine ⟨j, fun i => ?_, fun p => ?_, hj⟩
  · obtain ⟨W, hWi⟩ := hW i B x₀

    have hjW : Set.range (j i) ⊆ Set.range W.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨q, rfl⟩
      exact ((hWi (U i) (j i)).1 ⟨𝟙 _, by rw [hj i]; simp⟩) q
    obtain ⟨u, hu⟩ := (hWi W.toScheme W.ι).2 (fun q => by
      have : W.ι q ∈ Set.range W.ι := ⟨q, rfl⟩
      rwa [Scheme.Opens.range_ι] at this)
    set l := IsOpenImmersion.lift W.ι (j i) hjW with hldef
    have hl : l ≫ W.ι = j i := IsOpenImmersion.lift_fac _ _ _
    have huj : u ≫ j i = W.ι := by
      apply uniq
      rw [op_comp, FunctorToTypes.map_comp_apply, hj i, hu]
    have hlu : l ≫ u = 𝟙 _ := by
      apply hinj i
      rw [op_comp, FunctorToTypes.map_comp_apply, ← hu, ← FunctorToTypes.map_comp_apply, ← op_comp, hl, hj i]
      simp
    have hul : u ≫ l = 𝟙 _ := by
      rw [← cancel_mono W.ι, Category.assoc, hl, huj, Category.id_comp]
    haveI : IsIso l := ⟨⟨u, hlu, hul⟩⟩
    rw [← hl]
    infer_instance
  · obtain ⟨i, Y, a, u, ⟨q, rfl⟩, ha⟩ := hcov B x₀ p
    refine ⟨i, u q, ?_⟩
    have : a = u ≫ j i := by
      apply uniq
      rw [ha, op_comp, FunctorToTypes.map_comp_apply, hj i]
    rw [this]
    rfl

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.charts_representedFunctor_openCover : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1) (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∀ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) → ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  atlas_forward_decl GlobalTheory.charts_represented_open_cover
end

section
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem exists_represent_of_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro F hsep hglue Ix U x hinj hopen hcov
  haveI hs : FunctorToTypes.Small.{0} F := GlobalTheory.T.small_of_separated_presheaf_open_charts F hsep Ix U x hopen hcov
  let G : Scheme.{0}ᵒᵖ ⥤ Type := FunctorToTypes.shrink.{0} F
  let e : ∀ T : Scheme.{0}, F.obj (op T) ≃ G.obj (op T) := fun T => equivShrink.{0} (F.obj (op T))
  have he : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : G.obj (op T)),
      G.map a.op y = e Y (F.map a.op ((e T).symm y)) := fun a y => rfl
  have he' : ∀ {Y T : Scheme.{0}} (a : Y ⟶ T) (y : F.obj (op T)),
      G.map a.op (e T y) = e Y (F.map a.op y) := fun a y => by
    rw [he, Equiv.symm_apply_apply]
  have key := GlobalTheory.T.exists_universal_of_zariskiSheaf_openCharts G ?_ ?_ Ix U (fun i => e _ (x i)) ?_ ?_ ?_
  · obtain ⟨B, x₀, hx⟩ := key
    obtain ⟨x₁, rfl⟩ := (e B).surjective x₀
    have hx' : ∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₁ = y := by
      intro T y
      have h := hx T (e T y)
      simpa only [he', Equiv.apply_eq_iff_eq] using h
    exact ⟨B, x₁, hx', GlobalTheory.T.charts_representedFunctor_openCover F Ix U x hinj hopen hcov B x₁ hx'⟩
  · intro T y y' h
    obtain ⟨y, rfl⟩ := (e T).surjective y
    obtain ⟨y', rfl⟩ := (e T).surjective y'
    simp only [he', Equiv.apply_eq_iff_eq] at h
    rw [hsep T y y' h]
  · intro T J Z z y hz hc h
    obtain ⟨y₀, hy₀⟩ := hglue T J Z z (fun i => (e _).symm (y i)) hz hc (fun i k Y a b hab => by
      have h1 := h i k Y a b hab
      rw [he, he] at h1
      exact (e Y).injective h1)
    refine ⟨e T y₀, fun i => ?_⟩
    rw [he', hy₀, Equiv.apply_symm_apply]
  · intro i Y u u' h
    rw [he', he'] at h
    exact hinj i Y u u' ((e Y).injective h)
  · intro i T y
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hopen i T y
  · intro T y p
    obtain ⟨y, rfl⟩ := (e T).surjective y
    simp only [he', Equiv.apply_eq_iff_eq]
    exact hcov T y p

end GlobalTheory.PicGlue
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large : ∀ (F : Scheme.{0}ᵒᵖ ⥤ Type 1), (∀ (T : Scheme.{0}) (y y' : F.obj (op T)), (∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Scheme.{0}) (J : Type) (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i)) → (∀ p : T, ∃ i, p ∈ Set.range (z i)) → (∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Scheme.{0}) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Scheme.{0}) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Scheme.{0}) (y : F.obj (op T)), ∃ W : T.Opens, ∀ (Y : Scheme.{0}) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a q ∈ W) → (∀ (T : Scheme.{0}) (y : F.obj (op T)) (p : T), ∃ (i : Ix) (Y : Scheme.{0}) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Scheme.{0}) (x₀ : F.obj (op B)), (∀ (T : Scheme.{0}) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i)) ∧ (∀ p : B, ∃ i, p ∈ Set.range (j i)) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  atlas_forward_decl GlobalTheory.PicGlue.exists_represent_of_charts_large
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.RepOver

noncomputable def coverOf {T : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i)) : T.OpenCover :=
  Scheme.Cover.mkOfCovers J Z z (fun p => hc p) hz

theorem hom_eq_of_local {T S : Scheme.{0}} (t t' : T ⟶ S)
    (h : ∀ p : T, ∃ (Z : Scheme.{0}) (z : Z ⟶ T), IsOpenImmersion z ∧ p ∈ Set.range z ∧
      z ≫ t = z ≫ t') : t = t' := by
  choose Z z hz hp he using h
  exact Scheme.Cover.hom_ext (coverOf Z z hz (fun p => ⟨p, hp p⟩)) t t' he

theorem exists_glue {T S : Scheme.{0}} {J : Type} (Z : J → Scheme.{0}) (z : ∀ i, Z i ⟶ T)
    (hz : ∀ i, IsOpenImmersion (z i)) (hc : ∀ p : T, ∃ i, p ∈ Set.range (z i))
    (t : ∀ i, Z i ⟶ S)
    (ht : ∀ (i k : J) (Y : Scheme.{0}) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k →
      a ≫ t i = b ≫ t k) : ∃ t₀ : T ⟶ S, ∀ i, z i ≫ t₀ = t i :=
  ⟨Scheme.Cover.glueMorphisms (coverOf Z z hz hc) t
      (fun i k => ht i k _ _ _ pullback.condition),
    fun i => Scheme.Cover.ι_glueMorphisms (coverOf Z z hz hc) t _ i⟩

variable {S : Scheme.{0}} (F : (Over S)ᵒᵖ ⥤ Type 1)

theorem map_map {X Y Z : Over S} (a : X ⟶ Y) (b : Y ⟶ Z) (c : X ⟶ Z) (h : a.left ≫ b.left = c.left)
    (d : F.obj (op Z)) : F.map a.op (F.map b.op d) = F.map c.op d := by
  have : c = a ≫ b := Over.OverMorphism.ext (by simpa using h.symm)
  subst this
  simp

theorem sig_eq {Y : Scheme.{0}} (r r' : Y ⟶ S) (h : r = r') (e : F.obj (op (Over.mk r)))
    (e' : F.obj (op (Over.mk r'))) (c : Over.mk r ⟶ Over.mk r') (hc : c.left = 𝟙 Y)
    (he : F.map c.op e' = e) :
    (⟨r, e⟩ : Σ t : Y ⟶ S, F.obj (op (Over.mk t))) = ⟨r', e'⟩ := by
  subst h
  have : c = 𝟙 _ := Over.OverMorphism.ext hc
  subst this
  subst he
  simp

noncomputable def tot : Scheme.{0}ᵒᵖ ⥤ Type 1 where
  obj X := Σ t : X.unop ⟶ S, F.obj (op (Over.mk t))
  map {X Y} f := TypeCat.ofHom fun y =>
    ⟨f.unop ≫ y.1, F.map (Over.homMk f.unop rfl : Over.mk (f.unop ≫ y.1) ⟶ Over.mk y.1).op y.2⟩
  map_id X := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    exact sig_eq F _ _ (Category.id_comp _) _ _ _ rfl rfl
  map_comp f g := by
    refine ConcreteCategory.hom_ext _ _ fun y => ?_
    refine sig_eq F _ _ (Category.assoc _ _ _) _ _ (Over.homMk (𝟙 _) (by simp)) rfl ?_
    refine (map_map F _ _ (Over.homMk g.unop (Category.assoc _ _ _).symm) (by simp) _).trans ?_
    exact map_map F _ _ _ (by simp) _

def el {V : Over S} (v : F.obj (op V)) : (tot F).obj (op V.left) := ⟨V.hom, v⟩

theorem el_inj {V : Over S} {v v' : F.obj (op V)} (h : el F v = el F v') : v = v' :=
  eq_of_heq (Sigma.mk.inj h).2

theorem map_el {Y V : Over S} (a : Y ⟶ V) (v : F.obj (op V)) :
    (tot F).map a.left.op (el F v) = el F (F.map a.op v) :=
  sig_eq F (a.left ≫ V.hom) Y.hom (Over.w a) _ _ (Over.homMk (𝟙 _) (by simp)) rfl
    (map_map F _ _ _ (by simp) _)

theorem w_of_map_el {Y V : Over S} {a : Y.left ⟶ V.left} {v : F.obj (op V)} {y : F.obj (op Y)}
    (h : (tot F).map a.op (el F v) = el F y) : a ≫ V.hom = Y.hom :=
  congrArg Sigma.fst h

theorem w_of_map_eq {Y : Scheme.{0}} {V V' : Over S} {a : Y ⟶ V.left} {b : Y ⟶ V'.left}
    {v : F.obj (op V)} {v' : F.obj (op V')}
    (h : (tot F).map a.op (el F v) = (tot F).map b.op (el F v')) : a ≫ V.hom = b ≫ V'.hom :=
  congrArg Sigma.fst h

theorem map_eq_iff {Y V V' : Over S} (a : Y ⟶ V) (b : Y ⟶ V')
    (v : F.obj (op V)) (v' : F.obj (op V')) :
    (tot F).map a.left.op (el F v) = (tot F).map b.left.op (el F v') ↔
      F.map a.op v = F.map b.op v' := by
  rw [map_el, map_el]
  exact ⟨el_inj F, fun h => by rw [h]⟩

end GlobalTheory.RepOver

open GlobalTheory.RepOver in

theorem GlobalTheory.RepOver.representable_over : ∀ (S : Scheme.{0}) (F : (Over S)ᵒᵖ ⥤ Type 1), (∀ (T : Over S) (y y' : F.obj (op T)), (∀ p : T.left, ∃ (Z : Over S) (z : Z ⟶ T), IsOpenImmersion z.left ∧ p ∈ Set.range z.left ∧ F.map z.op y = F.map z.op y') → y = y') → (∀ (T : Over S) (J : Type) (Z : J → Over S) (z : ∀ i, Z i ⟶ T) (y : ∀ i, F.obj (op (Z i))), (∀ i, IsOpenImmersion (z i).left) → (∀ p : T.left, ∃ i, p ∈ Set.range (z i).left) → (∀ (i k : J) (Y : Over S) (a : Y ⟶ Z i) (b : Y ⟶ Z k), a ≫ z i = b ≫ z k → F.map a.op (y i) = F.map b.op (y k)) → ∃ y₀ : F.obj (op T), ∀ i, F.map (z i).op y₀ = y i) → ∀ (Ix : Type) (U : Ix → Over S) (x : ∀ i, F.obj (op (U i))), (∀ (i : Ix) (Y : Over S) (u u' : Y ⟶ U i), F.map u.op (x i) = F.map u'.op (x i) → u = u') → (∀ (i : Ix) (T : Over S) (y : F.obj (op T)), ∃ W : T.left.Opens, ∀ (Y : Over S) (a : Y ⟶ T), (∃ u : Y ⟶ U i, F.map a.op y = F.map u.op (x i)) ↔ ∀ q, a.left q ∈ W) → (∀ (T : Over S) (y : F.obj (op T)) (p : T.left), ∃ (i : Ix) (Y : Over S) (a : Y ⟶ T) (u : Y ⟶ U i), p ∈ Set.range a.left ∧ F.map a.op y = F.map u.op (x i)) → ∃ (B : Over S) (x₀ : F.obj (op B)), (∀ (T : Over S) (y : F.obj (op T)), ∃! g : T ⟶ B, F.map g.op x₀ = y) ∧ ∃ j : ∀ i, U i ⟶ B, (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, F.map (j i).op x₀ = x i := by
  intro S F hsep hglue Ix U x hmono hopen hcov
  refine Exists.elim (GlobalTheory.T.representable_of_zariski_sheaf_open_charts_large (tot F) ?_ ?_ Ix (fun i => (U i).left)
    (fun i => el F (x i)) ?_ ?_ ?_) ?_
  rotate_right
  · rintro B ⟨⟨tB, dB⟩, huniv, j, hj, hc, hx⟩
    refine ⟨Over.mk tB, dB, fun T y => ?_, fun i => Over.homMk (j i)
      (w_of_map_el F (V := Over.mk tB) (hx i)), hj, hc, fun i => ?_⟩
    · obtain ⟨g, hg, hu⟩ := huniv T.left (el F y)
      refine ⟨Over.homMk g (w_of_map_el F (V := Over.mk tB) hg), ?_, fun g' hg' => ?_⟩
      · exact el_inj F ((map_el F _ dB).symm.trans hg)
      · exact Over.OverMorphism.ext (hu g'.left ((map_el F g' dB).trans (congrArg (el F) hg')))
    · exact el_inj F ((map_el F _ dB).symm.trans (hx i))
  · rintro T ⟨t, d⟩ ⟨t', d'⟩ h
    obtain rfl : t = t' := hom_eq_of_local t t' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Z, z, hz, hp, congrArg Sigma.fst he⟩
    obtain rfl : d = d' := hsep (Over.mk t) d d' fun p => by
      obtain ⟨Z, z, hz, hp, he⟩ := h p
      exact ⟨Over.mk (z ≫ t), Over.homMk z rfl, hz, hp, (map_eq_iff F _ _ d d').1 he⟩
    rfl
  · intro T J Z z y hz hc hy
    obtain ⟨t, ht⟩ := exists_glue Z z hz hc (fun i => (y i).1)
      (fun i k Y a b hab => congrArg Sigma.fst (hy i k Y a b hab))
    obtain ⟨d, hd⟩ := hglue (Over.mk t) J (fun i => Over.mk (y i).1)
      (fun i => Over.homMk (z i) (ht i)) (fun i => (y i).2) hz hc
      (fun i k Y a b hab => (map_eq_iff F a b _ _).1
        (hy i k Y.left a.left b.left (congrArg (fun c => c.left) hab)))
    exact ⟨⟨t, d⟩, fun i => (map_el F (Y := Over.mk (y i).1) (V := Over.mk t)
      (Over.homMk (z i) (ht i)) d).trans (congrArg (el F) (hd i))⟩
  · intro i Y u u' h
    have := hmono i (Over.mk (u ≫ (U i).hom)) (Over.homMk u rfl)
      (Over.homMk u' (w_of_map_eq F h).symm) ((map_eq_iff F _ _ _ _).1 h)
    exact congrArg (fun c => c.left) this
  · rintro i T ⟨t, d⟩
    obtain ⟨W, hW⟩ := hopen i (Over.mk t) d
    refine ⟨W, fun Y a => Iff.trans ?_ (hW (Over.mk (a ≫ t)) (Over.homMk a rfl))⟩
    constructor
    · rintro ⟨u, hu⟩
      exact ⟨Over.homMk u (w_of_map_eq F (V := Over.mk t) hu).symm, (map_eq_iff F _ _ _ _).1 hu⟩
    · rintro ⟨u, hu⟩
      exact ⟨u.left, (map_eq_iff F _ _ _ _).2 hu⟩
  · rintro T ⟨t, d⟩ p
    obtain ⟨i, Y, a, u, hp, h⟩ := hcov (Over.mk t) d p
    exact ⟨i, Y.left, a.left, u.left, hp, (map_eq_iff F _ _ _ _).2 h⟩
end

section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_geomPoint_through : ∀ (T : Scheme.{0}) (p : T), ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (s : Sp K ⟶ T), p ∈ Set.range s := by
  intro T p
  refine ⟨AlgebraicClosure (T.residueField p), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (T.residueField p) (AlgebraicClosure (T.residueField p)))) ≫ T.fromSpecResidueField p, ?_⟩
  obtain ⟨x⟩ : Nonempty (Sp (AlgebraicClosure (T.residueField p))) := inferInstance
  refine ⟨x, ?_⟩
  show (T.fromSpecResidueField p).base _ = p
  exact Scheme.fromSpecResidueField_apply p _

end GlobalTheory
end

section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PicGlue

theorem same_id_map {S : Scheme.{0}} {A T U : Over S} [GrpObj A] {N : LB (A ⊗ T).left} {M : LB (A ⊗ U).left}
    (hN : Fam A N) (hM : Fam A M) (u : T ⟶ U) :
    Same A N M (𝟙 T) u ↔ (addF A).map u.op (famCls hM) = famCls hN := by
  rw [same_iff_map hN hM, op_id, CategoryTheory.Functor.map_id]
  exact eq_comm

theorem glue : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  intro S A _ hA Ix U M hM hcov
  obtain ⟨B, x, hu, j, ho, hc, hj⟩ := GlobalTheory.RepOver.representable_over S (addF A) (GlobalTheory.PicGlue.addF_separated S A hA) (GlobalTheory.PicGlue.addF_glue S A hA) Ix U
    (fun i ↦ famCls (hM i).fam)
    (fun i Y u u' h ↦ (hM i).inj Y u u' ((same_iff_map (hM i).fam (hM i).fam u u').2 h))
    (fun i T y ↦ by
      obtain ⟨N, hN, rfl⟩ := famCls_surj y
      obtain ⟨W, hW⟩ := (hM i).chart T N hN
      exact ⟨W, fun Y a ↦ (exists_congr fun u ↦ (same_iff_map hN (hM i).fam a u).symm).trans (hW Y a)⟩)
    (fun T y p ↦ by
      obtain ⟨K, _, _, s, hs⟩ := GlobalTheory.exists_geomPoint_through T.left p
      let a : Over.mk (s ≫ T.hom) ⟶ T := Over.homMk s rfl
      obtain ⟨N, hN, e⟩ := famCls_surj ((addF A).map a.op y)
      obtain ⟨i, u, h⟩ := hcov K (s ≫ T.hom) N hN
      exact ⟨i, _, a, u, hs, e.symm.trans ((same_id_map hN (hM i).fam u).1 h).symm⟩)
  obtain ⟨P, hP, rfl⟩ := famCls_surj x
  refine ⟨B, P, j, ⟨hP, fun T t N hN ↦ ?_⟩, ho, hc, fun i ↦ (same_id_map (hM i).fam hP _).2 (hj i)⟩
  obtain ⟨g, hg, hg'⟩ := hu T (famCls hN)
  have k : ∀ g : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ g)) ↔ (addF A).map g.op (famCls hP) = famCls hN :=
    fun g ↦ (same_id_iff hN.isLB hP.isLB g).symm.trans (same_id_map hN hP g)
  exact ⟨g, ⟨toUnit_unique _ _, (k g).2 hg⟩, fun g' h ↦ hg' g' ((k g').1 h.2)⟩

end GlobalTheory.PicGlue
end
end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.glue_openCharts_additiveFamilies_representing : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (Ix : Type) (U : Ix → Over S) (M : ∀ i, LB (A ⊗ U i).left), (∀ i, IsChart A (M i)) → (∀ (K : Type) [Field K] [IsAlgClosed K] (s : Sp K ⟶ S) (N : LB (A ⊗ Over.mk s).left), Fam A N → ∃ (i : Ix) (u : Over.mk s ⟶ U i), Same A N (M i) (𝟙 _) u) → ∃ (B : Over S) (P : LB (A ⊗ B).left) (j : ∀ i, U i ⟶ B), Rep A (toUnit B) P ∧ (∀ i, IsOpenImmersion (j i).left) ∧ (∀ p : B.left, ∃ i, p ∈ Set.range (j i).left) ∧ ∀ i, Same A (M i) P (𝟙 _) (j i) := by
  atlas_forward_decl GlobalTheory.PicGlue.glue
end
