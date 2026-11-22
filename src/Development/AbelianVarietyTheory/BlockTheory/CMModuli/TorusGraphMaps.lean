module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtPtBridgeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

section Prim

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]

end Prim

variable {R : Type} [CommRing R] [IsDomain R]

section Data

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]

end Data

section Points

variable {O : Type} [Ring O] [StarRing O] {D : DegPre R} [Module O D.X]
variable {F : Type} [Field F] [Algebra (FractionRing R) F]

variable {F' : Type} [Field F'] [Algebra (FractionRing R) F']

end Points

section Host

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Host

end GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
