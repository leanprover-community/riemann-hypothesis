module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.TorusPointForms

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

variable {D F}

variable {P : PolAV (Spec (CommRingCat.of (FractionRing R)))}

variable (D F)

variable (P)

end GlobalTheory.IndefiniteRowSideFullHecke.TranslatedLineGenerators
