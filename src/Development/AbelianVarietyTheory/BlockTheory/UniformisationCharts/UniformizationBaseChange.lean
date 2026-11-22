module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.RigidPullbackIdentification

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.IndefiniteRowSideFullHecke.RigidPullbackIdentification

section Carries

variable {X X' Y : Scheme.{0}} (L : LB X) (L' : LB X') (F : X' ⟶ X) {K : Type} [Fintype K]

end Carries

section Pull

open scoped CategoryTheory.Obj

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

variable {I : Ideal R} {I' : Ideal R'}

end Pull

section Basic₂

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

end Basic₂

end GlobalTheory.IndefiniteRowSideFullHecke.UniformizationBaseChange
