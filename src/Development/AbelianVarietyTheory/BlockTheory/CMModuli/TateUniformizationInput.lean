module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps

section Points

variable {R : Type} [CommRing R] [IsDomain R] {P : DegPre R}
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

section Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

variable {R : Type} [CommRing R] [IsDomain R]

end Lie

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Levels

variable {R : Type} [CommRing R] [IsDomain R]

end Levels

section Base

variable {l : Level H} (c : Coeff l)

variable {c}

end Base

attribute [instance] ArcInput.mod

namespace ArcInput

variable {D : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {O' : Type} [CommRing O'] [IsDomain O'] {b : O →+* O'}

end ArcInput

end GlobalTheory.IndefiniteRowSideFullHecke.TateUniformizationInput
