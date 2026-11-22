module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
public import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwZ
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImageCochainExists
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneralLinearGroupDetMapFinOne

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.EtC.KumPic

def liftSec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec C U :=
  Function.surjInv (hb U (hE U ⟨x.face 0⟩)).2 (unitSec (lineUnit L x))

theorem liftSec_spec {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 1 U) : Sec.map qb (liftSec qb L hE hb U x) = unitSec (lineUnit L x) :=
  Function.surjInv_eq _ _

theorem liftSec_res {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    {V U : Scheme.{0}} (g : V ⟶ U) (x : Sx E 1 U) :
    Sec.res g (liftSec qb L hE hb U x) = liftSec qb L hE hb V (x.res g) := by
  apply (hb V (hE V ⟨(x.res g).face 0⟩)).1
  rw [← CupSpec.map_res, liftSec_spec, liftSec_spec, PicSpec.unitSec_res, PicSpec.lineUnit_res]

theorem liftSec_face {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (U : Scheme.{0}) (x : Sx E 2 U) :
    liftSec qb L hE hb U (x.face 1) = liftSec qb L hE hb U (x.face 0) + liftSec qb L hE hb U (x.face 2) := by
  apply (hb U (hE U ⟨(x.face 0).face 0⟩)).1
  rw [PicSpec.sec_map_add, liftSec_spec, liftSec_spec, liftSec_spec, PicSpec.lineUnit_face, PicSpec.unitSec_mul]

def liftFam {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U))) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 1 = s → ∀ U : Scheme.{0}, Sx E p U → Sec ((sgl C).X s) U
  | 1, s, h, U, x => Sec.map ((sgl C).XIsoOfEq (show (0 : ℤ) = s by omega)).hom
      (Sec.map (sglι C) (liftSec qb L hE hb U x))
  | _, _, _, _, _ => 0

theorem liftFam_nat {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + 1 = s) (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U) :
    Sec.res g (liftFam qb L hE hb p s h U x) = liftFam qb L hE hb p s h V (x.res g) := by
  match p with
  | 0 => exact map_zero _
  | 1 =>
    simp only [liftFam]
    rw [CupSpec.map_res, CupSpec.map_res, liftSec_res]
  | p + 2 => exact map_zero _

end GlobalTheory.EtC.KumPic

namespace GlobalTheory.EtC.KumPic

theorem liftFam_one {q : ℕ} {C : Shv ℤ} (qb : C ⟶ Gm) {E : Spc} (L : E ⟶ ofCat (glCat 1)) (hE : GlobalTheory.EtC.Inv q E)
    (hb : ∀ U : Scheme.{0}, IsUnit (q : Γ(U, ⊤)) → Function.Bijective (Sec.map qb (U := U)))
    (h : -((1 : ℕ) : ℤ) + 1 = 0) (U : Scheme.{0}) (x : Sx E 1 U) :
    liftFam qb L hE hb 1 0 h U x = Sec.map (sglι C) (liftSec qb L hE hb U x) := by
  simp [liftFam, Sec.map]

end GlobalTheory.EtC.KumPic
