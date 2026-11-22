module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.BetaAtAddLeftAndDiagEqTwoOrder
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsGoodIntegral

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocM.Bdy

section Algebra

variable (R : Type) [CommRing R] [IsDomain R]

variable {R}

end Algebra

section Coord

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

variable (Dg : DegData R (maximalIdeal R))

variable {Dg}

end Coord

end GlobalTheory.LocM.Bdy
