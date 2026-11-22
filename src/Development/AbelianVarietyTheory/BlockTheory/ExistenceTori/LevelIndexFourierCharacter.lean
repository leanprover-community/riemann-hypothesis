module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThProps
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

variable (D : Datum H) (l : Level H)

variable {l}

variable {D}

end GlobalTheory.IndefiniteRowSideFullHecke.LevelSpanSeparation
