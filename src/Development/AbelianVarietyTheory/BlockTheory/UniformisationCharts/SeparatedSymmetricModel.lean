module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
public import Development.AbelianVarietyTheory.BlockTheory.UniformisationCharts.CanonicalRigidImages

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel

section BaseChange

variable {S S' : Scheme.{0}} (p : S' ⟶ S)

variable {G : Over S} [GrpObj G] [IsCommMonObj G]

instance isComm_baseChange : IsCommMonObj ((Over.pullback p).obj G) :=
  Functor.isCommMonObj_obj

variable {H : Over S'} [GrpObj H] [IsCommMonObj H]

end BaseChange

section Sym

variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

variable {G} {S' : Scheme.{0}} {H : Over S'} [GrpObj H]

end Sym

section IsoPull

variable {X X' Y Y' : Scheme.{0}} (L : LB X) (M : LB X')

end IsoPull

section Generic

variable (R : Type) [CommRing R] [IsDomain R]

end Generic

section Levels

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

end Levels

end GlobalTheory.IndefiniteRowSideFullHecke.SeparatedSymmetricModel
