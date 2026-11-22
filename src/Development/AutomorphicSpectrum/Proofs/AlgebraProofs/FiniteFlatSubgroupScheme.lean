module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub

@[expose] public section

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GR.SubGrp

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.GR

section Abstract

universe v u
variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]

def ptSub {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1)
    (T : C) : Subgroup (T ⟶ A) where
  carrier := {f | ∃ a : T ⟶ X, a ≫ h = f}
  mul_mem' := by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨lift a b ≫ m, ?_⟩
    rw [Category.assoc, hm, MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  one_mem' := ⟨toUnit T ≫ e, by rw [Category.assoc, he, MonObj.comp_one]⟩
  inv_mem' := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a ≫ i, ?_⟩
    rw [eq_inv_iff_mul_eq_one, Category.assoc, ← MonObj.comp_mul, hi, MonObj.comp_one]

def ptFunctor {A X : C} [GrpObj A] (h : X ⟶ A) (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    Cᵒᵖ ⥤ GrpCat.{v} where
  obj T := GrpCat.of (ptSub h m e i hm he hi (unop T))
  map {T T'} f := GrpCat.ofHom
    { toFun := fun x => ⟨f.unop ≫ x.1, by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨f.unop ≫ a, by rw [Category.assoc, ha]⟩⟩
      map_one' := Subtype.ext (MonObj.comp_one _)
      map_mul' := fun x y => Subtype.ext (MonObj.comp_mul _ _ _) }
  map_id T := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.id_comp x.1))
  map_comp f g := GrpCat.hom_ext (MonoidHom.ext fun x => Subtype.ext (Category.assoc _ _ x.1))

def ptRep {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X) (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    (ptFunctor h m e i hm he hi ⋙ forget _).RepresentableBy X where
  homEquiv {T} := Equiv.ofBijective
    (fun a => (⟨a ≫ h, a, rfl⟩ : ptSub h m e i hm he hi T))
    ⟨fun a b hab => (cancel_mono h).1 (congrArg Subtype.val hab),
      fun x => by
        obtain ⟨a, ha⟩ := x.2
        exact ⟨a, Subtype.ext ha⟩⟩
  homEquiv_comp f g := Subtype.ext (Category.assoc _ _ _)

theorem exists_grpObj_of_mono {A X : C} [GrpObj A] (h : X ⟶ A) [Mono h] (m : X ⊗ X ⟶ X)
    (e : 𝟙_ C ⟶ X) (i : X ⟶ X)
    (hm : m ≫ h = (fst X X ≫ h) * (snd X X ≫ h)) (he : e ≫ h = 1) (hi : (i ≫ h) * h = 1) :
    ∃ _ : GrpObj X, IsMonHom h := by
  let α := ptRep h m e i hm he hi
  letI G : GrpObj X := GrpObj.ofRepresentableBy X _ α
  have key : ∀ {T : C} (a b : T ⟶ X), (a * b) ≫ h = (a ≫ h) * (b ≫ h) := fun {T} a b =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_mul a b)
  have key1 : ∀ {T : C}, (1 : T ⟶ X) ≫ h = 1 := fun {T} =>
    congrArg Subtype.val
      (((yonedaGrpObjIsoOfRepresentableBy X _ α).hom.app (op T)).hom.map_one)
  refine ⟨G, ⟨?_, ?_⟩⟩
  · have := key1 (T := 𝟙_ C)
    simpa [Hom.one_def, toUnit_unique (toUnit (𝟙_ C)) (𝟙 _)] using this
  · have := key (fst X X) (snd X X)
    rw [Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this, Hom.mul_def]
    congr 1
    ext <;> simp

end Abstract

section Scheme

variable {R : Type} [CommRing R]

theorem exists_eq_spMap {S B : Type} [CommRing S] [Algebra R S] [CommRing B] [Algebra R B]
    (x : sp (R₀ := R) S ⟶ sp (R₀ := R) B) : ∃ g : B →ₐ[R] S, x = spMap g := by
  obtain ⟨g, hg⟩ := Spec.map_surjective x.left
  have h : Spec.map g ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) := hg ▸ Over.w x
  rw [← Spec.map_comp] at h
  exact ⟨⟨g.hom, RingHom.congr_fun (congrArg (·.hom) (Spec.map_injective h))⟩,
    Over.OverMorphism.ext hg.symm⟩

theorem exists_sp_iso (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra R S) (j : sp (R₀ := R) S ⟶ T), IsIso j := by
  have hU := isAffineOpen_top T.left
  obtain ⟨ρ, hρ⟩ := Spec.map_surjective (hU.fromSpec ≫ T.hom)
  letI : Algebra R Γ(T.left, ⊤) := ρ.hom.toAlgebra
  let j : sp (R₀ := R) Γ(T.left, ⊤) ⟶ T := Over.homMk hU.fromSpec hρ.symm
  have : IsIso j.left := by
    change IsIso hU.fromSpec
    rw [IsAffineOpen.fromSpec_top]
    infer_instance
  have hj : IsIso ((Over.forget _).map j) := ‹IsIso j.left›
  exact ⟨Γ(T.left, ⊤), inferInstance, inferInstance, j, isIso_of_reflects_iso j (Over.forget _)⟩

variable {A : Over (Spec (CommRingCat.of R))} [GrpObj A] {B : Type} [CommRing B] [Algebra R B]
  {h : sp (R₀ := R) B ⟶ A}

end Scheme

end GlobalTheory.CompanionTheory.Ar.GR.SubGrp
