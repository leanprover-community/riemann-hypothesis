module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullGen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullExp

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

section Scale

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

end Scale

section BackK

variable {G : Over (Spec (CommRingCat.of V))}

end BackK

section Integral

variable (D : DegData V (maximalIdeal V)) {O : Type} [CommRing O] [StarRing O] [Module O D.toPre.X]

end Integral

end ReciprocityTheory.ChartRestriction.G.DVR
