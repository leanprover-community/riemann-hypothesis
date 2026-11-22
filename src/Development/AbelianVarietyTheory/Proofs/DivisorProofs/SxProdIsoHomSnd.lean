module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBundleFormulaOfUnitOnEtalePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotDComp
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroChains

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

def sxProdIso (A B : Spc) (p : ℕ) :
    (A ⨯ B).obj (op (SimplexCategory.mk p)) ≅ FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p))) :=
  PreservesLimitPair.iso ((evaluation _ _).obj (op (SimplexCategory.mk p))) A B ≪≫ FunctorToTypes.binaryProductIso _ _

theorem sxProdIso_hom_fst (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).hom ≫ FunctorToTypes.prod.fst = (prod.fst : A ⨯ B ⟶ A).app (op (SimplexCategory.mk p)) := by
  rw [sxProdIso, Iso.trans_hom, Category.assoc]
  erw [FunctorToTypes.binaryProductIso_hom_comp_fst]
  rw [PreservesLimitPair.iso_hom]
  erw [prodComparison_fst]
  rfl

theorem sxProdIso_hom_snd (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).hom ≫ FunctorToTypes.prod.snd = (prod.snd : A ⨯ B ⟶ B).app (op (SimplexCategory.mk p)) := by
  rw [sxProdIso, Iso.trans_hom, Category.assoc]
  erw [FunctorToTypes.binaryProductIso_hom_comp_snd]
  rw [PreservesLimitPair.iso_hom]
  erw [prodComparison_snd]
  rfl

theorem sxProdIso_inv_fst (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).inv ≫ (prod.fst : A ⨯ B ⟶ A).app (op (SimplexCategory.mk p)) = FunctorToTypes.prod.fst := by
  rw [Iso.inv_comp_eq, sxProdIso_hom_fst]

theorem sxProdIso_inv_snd (A B : Spc) (p : ℕ) :
    (sxProdIso A B p).inv ≫ (prod.snd : A ⨯ B ⟶ B).app (op (SimplexCategory.mk p)) = FunctorToTypes.prod.snd := by
  rw [Iso.inv_comp_eq, sxProdIso_hom_snd]

def sxPair {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) : Sx (A ⨯ B) p V :=
  ((sxProdIso A B p).inv.app (op V)) (show (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V) from (a, b))

@[simp] theorem sxPair_fst {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map prod.fst = a := by
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso_inv_fst A B p) (op V)) (((a, b) : Sx A p V × Sx B p V) : (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V))

@[simp] theorem sxPair_snd {A B : Spc} {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map prod.snd = b := by
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso_inv_snd A B p) (op V)) (((a, b) : Sx A p V × Sx B p V) : (FunctorToTypes.prod (A.obj (op (SimplexCategory.mk p))) (B.obj (op (SimplexCategory.mk p)))).obj (op V))

theorem sxPair_eta {A B : Spc} {p : ℕ} {V : Scheme.{0}} (y : Sx (A ⨯ B) p V) :
    sxPair (y.map prod.fst) (y.map prod.snd) = y := by
  have h1 := ConcreteCategory.congr_hom (congr_app (sxProdIso_hom_fst A B p) (op V)) y
  have h2 := ConcreteCategory.congr_hom (congr_app (sxProdIso_hom_snd A B p) (op V)) y
  have : ((sxProdIso A B p).hom.app (op V)) y = (y.map prod.fst, y.map prod.snd) := Prod.ext h1 h2
  rw [sxPair, ← this]
  exact ConcreteCategory.congr_hom (congr_app (sxProdIso A B p).hom_inv_id (op V)) y

theorem sx_prod_ext {A B : Spc} {p : ℕ} {V : Scheme.{0}} {y y' : Sx (A ⨯ B) p V}
    (h1 : y.map prod.fst = y'.map prod.fst) (h2 : y.map prod.snd = y'.map prod.snd) : y = y' := by
  rw [← sxPair_eta y, ← sxPair_eta y', h1, h2]

theorem sxMap_res {E E' : Spc} (f : E ⟶ E') {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E p U) :
    (x.res g).map f = (x.map f).res g :=
  ConcreteCategory.congr_hom ((f.app (op (SimplexCategory.mk p))).naturality g.op) x

theorem sxMap_comp {E E' E'' : Spc} (f : E ⟶ E') (f' : E' ⟶ E'') {p : ℕ} {U : Scheme.{0}} (x : Sx E p U) :
    x.map (f ≫ f') = (x.map f).map f' := rfl

theorem sxPair_res {A B : Spc} {p : ℕ} {V U : Scheme.{0}} (g : V ⟶ U) (a : Sx A p U) (b : Sx B p U) :
    (sxPair a b).res g = sxPair (a.res g) (b.res g) :=
  sx_prod_ext (by rw [sxMap_res, sxPair_fst, sxPair_fst]) (by rw [sxMap_res, sxPair_snd, sxPair_snd])

theorem sxPair_map {A B A' B' : Spc} (f : A ⟶ A') (f' : B ⟶ B') {p : ℕ} {V : Scheme.{0}} (a : Sx A p V) (b : Sx B p V) :
    (sxPair a b).map (prod.map f f') = sxPair (a.map f) (b.map f') :=
  sx_prod_ext (by rw [← sxMap_comp, prod.map_fst, sxMap_comp, sxPair_fst, sxPair_fst])
    (by rw [← sxMap_comp, prod.map_snd, sxMap_comp, sxPair_snd, sxPair_snd])

variable {R : Type} [CommRing R]

theorem secRes_res {F : Shv R} {U V W : Scheme.{0}} (g : V ⟶ U) (g' : W ⟶ V) (b : Sec F U) :
    Sec.res g' (Sec.res g b) = Sec.res (g' ≫ g) b := by
  rw [Sec.res, Sec.res, Sec.res, op_comp, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

def schSx {V W : Scheme.{0}} (v : W ⟶ V) (p : ℕ) : Sx (sch.obj V) p W := v

theorem schSx_map {V V' W : Scheme.{0}} (v : W ⟶ V) (u : V ⟶ V') (p : ℕ) :
    (schSx v p).map (sch.map u) = schSx (v ≫ u) p := rfl

end GlobalTheory.EtC

end
