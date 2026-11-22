module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsDPMorphismBot
public import Development.AbelianVarietyTheory.Definitions.Divisors.CrystallineConnectionFormCoboundaryZero
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.LogCris

variable {O : Type} [CommRing O]

abbrev PtOver (X : Scheme.{0}) (q : X ⟶ Spec (CommRingCat.of O)) {k : Type} [CommRing k] (κ : O →+* k) (B : Type)
    [CommRing B] : Type :=
  {z : (k →+* B) × (Spec (CommRingCat.of B) ⟶ X) // z.2 ≫ q = Spec.map (CommRingCat.ofHom (z.1.comp κ))}

end GlobalTheory.LogCris
