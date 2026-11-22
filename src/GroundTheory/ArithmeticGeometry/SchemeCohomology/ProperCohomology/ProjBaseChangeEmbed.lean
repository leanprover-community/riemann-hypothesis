module

public import Mathlib
public import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProperCohomology.ProjBaseChangeTwist

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Arith.SchemeCoh

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory

universe u

noncomputable section

namespace ProjSpace

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] {n : ℕ} {Y : Scheme.{u}}

instance (ι : Y ⟶ pullback (toSpecBase A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    [IsClosedImmersion ι] : IsClosedImmersion (toBaseChange ι) := by
  rw [toBaseChange]
  infer_instance

variable (A) in
def twistingSheafBaseChangeIso (g : Y ⟶ projectiveSpace B n) (k : ℤ) :
    ProjScheme.twistingSheaf (g ≫ baseChangeMap A B n) k ≅ ProjScheme.twistingSheaf g k :=
  ((Scheme.Modules.pullbackComp g (baseChangeMap A B n)).app _).symm ≪≫
    (Scheme.Modules.pullback g).mapIso (pullbackTwistingSheafIso A B n k)

variable (A) in
def twistBaseChangeIso (g : Y ⟶ projectiveSpace B n) (F : Y.Modules) (k : ℤ) :
    ProjScheme.twist (g ≫ baseChangeMap A B n) F k ≅ ProjScheme.twist g F k :=
  whiskerLeftIso F (twistingSheafBaseChangeIso A g k)

end ProjSpace

end

end GroundTheory.Arith.SchemeCoh
