module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafBasicPropertiStatement

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

noncomputable section
namespace GlobalTheory.EtC.LerayOne

def diag {Y X : Scheme.{0}} (f : Y ⟶ X) : sch.obj Y ⟶ cech f where
  app n := WidePullback.lift (yoneda.map f) (fun _ => 𝟙 _) (fun _ => Category.id_comp _)
  naturality m n g := by
    apply WidePullback.hom_ext
    · intro j
      dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_π, WidePullback.lift_π, WidePullback.lift_π]
    · dsimp [sch, cech, Arrow.cechNerve]
      erw [Category.id_comp, Category.assoc, WidePullback.lift_base, WidePullback.lift_base, WidePullback.lift_base]

theorem diag_aug {Y X : Scheme.{0}} (f : Y ⟶ X) : diag f ≫ cechAug f = sch.map f := by
  ext n : 1
  rw [NatTrans.comp_app]
  dsimp [diag, cechAug, sch, Arrow.augmentedCechNerve]
  erw [WidePullback.lift_base]

theorem diag_zero {Y X : Scheme.{0}} (f : Y ⟶ X) :
    WidePullback.π (fun _ : Fin 1 => yoneda.map f) (0 : Fin 1) ≫ (diag f).app (op ⦋0⦌) = 𝟙 ((cech f).obj (op ⦋0⦌)) := by
  apply WidePullback.hom_ext
  · intro j
    have hj : j = 0 := Fin.fin_one_eq_zero j
    subst hj
    dsimp [diag]
    erw [Category.assoc, WidePullback.lift_π, Category.comp_id]
  · dsimp [diag]
    erw [Category.assoc, WidePullback.lift_base, Category.id_comp, WidePullback.π_arrow]

end GlobalTheory.EtC.LerayOne

noncomputable section
namespace GlobalTheory.EtC.LerayOne

end GlobalTheory.EtC.LerayOne
