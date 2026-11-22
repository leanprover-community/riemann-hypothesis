module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt

@[expose] public section

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite MonoidalCategory Enriched.FunctorCategory
open scoped MonoidalClosed

namespace GlobalTheory.Et

section Site

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

variable [HasSheafify J (ModuleCat.{1} S)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

end Site

section Lin

variable {C : Type 1} [Category.{0} C] (J : GrothendieckTopology C) (S : Type 1) [CommRing S]

variable [HasSheafify J (ModuleCat.{1} S)]

attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory

end Lin

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

attribute [instance] FlatCoef.preservesFiniteLimits_tensorRight

section Cup

variable [FlatCoef R]

end Cup

section Natural

variable [FlatCoef R]

end Natural

section DegreeZero

variable [FlatCoef R]

end DegreeZero

section One

variable [FlatCoef R]

end One

section Examples

variable (X : Scheme.{0})

end Examples

end GlobalTheory.Et
