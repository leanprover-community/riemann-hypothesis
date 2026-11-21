import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

open CategoryTheory Limits

noncomputable section

namespace GlobalTheory.IndEtaleUnion

variable (A S : Type) [CommRing A] [CommRing S] [Algebra A S]

abbrev EtaleSub : Type := {T : Subalgebra A S // Algebra.Etale A T}

def diagram : EtaleSub A S ⥤ CommRingCat.{0} where
  obj T := CommRingCat.of T.1
  map {T U} h := CommRingCat.ofHom (Subalgebra.inclusion (show T.1 ≤ U.1 from leOfHom h)).toRingHom
  map_id _ := rfl
  map_comp _ _ := rfl

def fromBase : (Functor.const (EtaleSub A S)).obj (CommRingCat.of A) ⟶ diagram A S where
  app T := CommRingCat.ofHom (algebraMap A T.1)
  naturality _ _ _ := rfl

def toTop : diagram A S ⟶ (Functor.const (EtaleSub A S)).obj (CommRingCat.of S) where
  app T := CommRingCat.ofHom T.1.val.toRingHom
  naturality _ _ _ := rfl

variable {A S}




end GlobalTheory.IndEtaleUnion
