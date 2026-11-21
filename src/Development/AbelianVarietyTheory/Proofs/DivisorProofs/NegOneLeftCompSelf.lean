import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyExistsAmpleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyAmpleClassCechPicardClassIffAmpleStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_exists_ampleClass : ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c := by
  first | exact @GlobalTheory.AV.exists_isAmpleCls | exact GlobalTheory.AV.exists_isAmpleCls | (intros; apply GlobalTheory.AV.exists_isAmpleCls <;> assumption)
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV

theorem isAmpleCls_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left),
    IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  intro K _ A c d hc hd
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨M, hM, rfl⟩ := cls_surj d
  have hA : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A L hL).1 hc
  have hB : IsAmpleLB M := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A M hM).1 hd
  have hN : (tens L M).IsLB := isLB_tens hL hM
  have hT : IsAmpleLB (tens L M) := by
    refine hA.tensor hB hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hM)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hM, cls_div hN hL, cls_tens hL hM]
    abel
  rw [← cls_tens hL hM hN]
  exact (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (tens L M) hN).2 hT

end GlobalTheory.AV
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_add : ∀ (K : Type) [Field K] (A : AbVar K) (c d : Pic A.X.left), IsAmpleCls c → IsAmpleCls d → IsAmpleCls (c + d) := by
  atlas_forward_decl GlobalTheory.AV.isAmpleCls_add
end

section
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem isAmpleCls_pull_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left),
    IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  intro K _ A B f d hf hd
  obtain ⟨L, hL, hrel, rfl⟩ := hd
  have hB : IsAmpleLB L := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K B L hL).1 ⟨L, hL, hrel, rfl⟩
  have hA : IsAmpleLB (L.pull f.hom.left) := hB.pull_of_isAffineHom f.hom.left
  have h := (GlobalTheory.T.abelianVarietyAmpleClass_cechPicardClass_iff_ample K A (L.pull f.hom.left) hA.isLB).2 hA
  rwa [cls_pull hL f.hom.left hA.isLB] at h

end GlobalTheory.AV.AbVar
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (d : Pic B.X.left), IsFinite f.hom.left → IsAmpleCls d → IsAmpleCls (CechPic.pull f.hom.left d) := by
  atlas_forward_decl GlobalTheory.AV.AbVar.isAmpleCls_pull_of_isFinite
end

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem neg_one_left_comp_self {K : Type} [Field K] (A : AbVar K) :
    (Hom.hom (-(𝟙 A))).left ≫ (Hom.hom (-(𝟙 A))).left = 𝟙 A.X.left := by
  have h : (-(𝟙 A)) ≫ (-(𝟙 A)) = 𝟙 A := by
    rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg, Category.id_comp]
  have h2 := congrArg (fun g : A ⟶ A => (Hom.hom g).left) h
  simpa only [comp_hom, Over.comp_left, id_hom, Over.id_left] using h2

theorem exists_symm_ample :
    ∀ (K : Type) [Field K] (A : AbVar K), ∃ c : Pic A.X.left, IsAmpleCls c ∧ CechPic.pull (Hom.hom (-(𝟙 A))).left c = c := by
  intro K _ A
  obtain ⟨c₀, hc₀⟩ := GlobalTheory.T.abelianVariety_exists_ampleClass K A
  set f : A.X.left ⟶ A.X.left := (Hom.hom (-(𝟙 A))).left with hf
  have hff : f ≫ f = 𝟙 A.X.left := neg_one_left_comp_self A
  have hiso : IsIso f := ⟨⟨f, hff, hff⟩⟩
  have hfin : IsFinite (Hom.hom (-(𝟙 A))).left := by
    rw [← hf]; infer_instance
  refine ⟨c₀ + CechPic.pull f c₀, GlobalTheory.T.isAbelianVarietyAmpleClass_add K A _ _ hc₀ (GlobalTheory.T.isAbelianVarietyAmpleClass_pullback_of_isFinite K A A (-(𝟙 A)) c₀ hfin hc₀), ?_⟩
  rw [map_add, ← CechPic.pull_comp, hff, CechPic.pull_id, add_comm]

end GlobalTheory.AV.AbVar
end
