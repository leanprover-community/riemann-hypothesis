import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
import Development.AbelianVarietyTheory.Definitions.Divisors.Uniformised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver

section
noncomputable section

namespace GlobalTheory.KS.Leray

open AlgebraicGeometry CategoryTheory Limits

def fibMap {X Y T : Scheme.{0}} (f : Y ⟶ X) (x : T ⟶ X) (u : Y ⟶ Y) (hu : u ≫ f = f) : pullback f x ⟶ pullback f x :=
  pullback.map f x f x u (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hu]) (by simp)

variable {S B B' : Scheme.{0}}

def ksProj (A : Over S) (m : ℕ) (p : S ⟶ B) (b : B' ⟶ B) : ksBC A m p b ⟶ pullback p b :=
  pullback.map _ _ _ _ (pow A m).hom (𝟙 _) (𝟙 _) (by simp) (by simp)

end GlobalTheory.KS.Leray
end
end

section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.KS.Leray

theorem isProper_pow_hom {S : Scheme.{0}} (A : Over S) (hA : IsProper A.hom) (m : ℕ) :
    IsProper (GlobalTheory.KS.pow A m).hom :=
  GlobalTheory.FibrePowerProper.isProper_fan_pt m (fun _ => A) (fun _ => hA) (limit.cone _) (limit.isLimit _)

end GlobalTheory.KS.Leray
end
