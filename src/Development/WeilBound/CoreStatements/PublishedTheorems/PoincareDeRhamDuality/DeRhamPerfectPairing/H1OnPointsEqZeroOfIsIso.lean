module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineClassMemHodgeFiltrationOfCechRepZero

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace CrystallinePoints.Pd

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] {X X' X'' : Scheme.{0}}

instance ptCat (s : X ⟶ Sp R) : Category.{0} (Pt s) where
  Hom := Pt.Hom
  id := Pt.Hom.id
  comp := Pt.Hom.comp
  id_comp _ := hom_ext' fun _ ↦ rfl
  comp_id _ := hom_ext' fun _ ↦ rfl
  assoc _ _ _ := hom_ext' fun _ ↦ rfl

@[reducible] def FP (s : X ⟶ Sp R) : Pt s ⥤ CommAlgCat.{0} R where
  obj P := CommAlgCat.of R P.B
  map φ := CommAlgCat.ofHom φ.ρ

def toPC (s : X ⟶ Sp R) : CoefMap (RingHom.id R) (O (dp0 R) s) (FP s) where
  G := { obj := fun P ↦ P.triv
         map := fun φ ↦ Pt.Hom.triv φ
         map_id := fun _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl)
         map_comp := fun _ _ ↦ Thick.Hom.ext' (AlgHom.ext fun _ ↦ rfl) }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul _ _ _ := rfl

abbrev H1OnPoints (s : X ⟶ Sp R) : Type 1 := GlobalTheory.CatCoh.H1 (FP s)

def toP (s : X ⟶ Sp R) : FirstDeRham s →ₗ[R] H1OnPoints s := (toPC s).pull1

variable {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {s'' : X'' ⟶ Sp R''} {σ : R →+* R'} {φ : X' ⟶ X}

@[reducible] def pushPt (h : φ ≫ s = s' ≫ spMap σ) (P : Pt s') : Pt s where
  B := P.B
  alg := ((algebraMap R' P.B).comp σ).toAlgebra
  x := P.x ≫ φ
  w := by rw [Category.assoc, h, ← Category.assoc, P.w, ← GlobalTheory.Cris.spMap_comp]

def pushHom (h : φ ≫ s = s' ≫ spMap σ) {P Q : Pt s'} (f : P ⟶ Q) : pushPt h P ⟶ pushPt h Q where
  ρ := { (f.ρ : P.B →+* Q.B) with commutes' := fun r ↦ f.ρ.commutes (σ r) }
  pt := by
    change spMap (f.ρ : P.B →+* Q.B) ≫ P.x ≫ φ = Q.x ≫ φ
    rw [← Category.assoc, f.pt]

def pushC (h : φ ≫ s = s' ≫ spMap σ) : CoefMap σ (FP s) (FP s') where
  G := { obj := pushPt h
         map := pushHom h
         map_id := fun _ ↦ hom_ext' fun _ ↦ rfl
         map_comp := fun _ _ ↦ hom_ext' fun _ ↦ rfl }
  α P := RingHom.id P.B
  naturality _ _ := rfl
  smul T r b := (Algebra.smul_def (A := T.B) (σ r) b).symm

def pullP (h : φ ≫ s = s' ≫ spMap σ) : H1OnPoints s →ₛₗ[σ] H1OnPoints s' := (pushC h).pull1

def SurjAll : Prop :=
  ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → Function.Surjective (toP (A.hom ≫ 𝟙 _))

end CrystallinePoints.Pd
