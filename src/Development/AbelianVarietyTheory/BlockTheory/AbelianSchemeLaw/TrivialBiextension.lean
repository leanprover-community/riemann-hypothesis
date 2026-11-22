module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubeSymmetricSwapFirst

@[expose] public section

namespace GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi

universe u

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Scheme.{u}} (G : Over S) [GrpObj G]

section
variable {X Y Z : Scheme.{u}} (L : LB X) {K K' : Type u} [Fintype K] [Fintype K']

end

end

end GlobalTheory.IndefiniteRowSideFullHecke.TrivialBiextension
