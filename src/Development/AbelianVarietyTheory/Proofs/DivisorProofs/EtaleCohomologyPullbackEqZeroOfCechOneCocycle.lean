module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

def cechDiag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (arrows := fun _ : Fin (n.unop.len + 1) => yoneda.map f) (yoneda.map f)
    (fun _ => 𝟙 (yoneda.obj Y)) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
      rfl
    · simp only [cech, Arrow.cechNerve]
      erw [Category.assoc, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]
      rfl

theorem cechDiag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : cechDiag f ≫ cechAug f = sch.map f := by
  ext n : 1
  simp only [cechDiag, cechAug]
  erw [NatTrans.comp_app, Arrow.augmentedCechNerve_hom_app, WidePullback.lift_base]
  rfl

theorem cechDiag_δ {Y X : Scheme.{0}} (f : Y ⟶ X) (i : Fin 3) :
    (cechDiag f).app (op ⦋2⦌) ≫ SimplicialObject.δ (cech f) i = (cechDiag f).app (op ⦋1⦌) := by
  rw [SimplicialObject.δ, ← NatTrans.naturality]
  simp [sch, disc]

end GlobalTheory.CechOne

end
