import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH

universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatCohProd

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}

def tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) : Cn (piF F) n :=
  fun s i => g i s


theorem cochain_ext (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) {a b : Cn (piF F) n}
    (h : ∀ i, (piProj F i).pullC n a = (piProj F i).pullC n b) : a = b :=
  funext fun s => funext fun i => congrFun (h i) s

theorem pull_d (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (a : Cn (piF F) n) (i : ι) :
    (piProj F i).pullC (n + 1) (d (piF F) n a) = d (F i) n ((piProj F i).pullC n a) :=
  ((piProj F i).d_pullC n a).symm


end GlobalTheory.CompanionTheory.CatCohProd
