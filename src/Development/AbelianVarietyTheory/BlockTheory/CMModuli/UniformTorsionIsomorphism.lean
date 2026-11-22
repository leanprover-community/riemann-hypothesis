module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegOUnif
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.TorusGraphMaps

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj NumberField

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.IndefiniteRowSideFullHecke.TorusGraphMaps
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
variable {R : Type} [CommRing R] [IsDomain R]

attribute [instance] OData.mod

variable {H : Host E} {I : Ideal R}

section Points

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

end Points

namespace OUnif

variable {t : SAB H (Spec (CommRingCat.of R))} {Δ : OData H I} (u : OUnif t Δ)
variable (F : Type) [Field F] [Algebra (FractionRing R) F]

end OUnif

end GlobalTheory.IndefiniteRowSideFullHecke.UniformTorsionIsomorphism
