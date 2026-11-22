module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaPt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.QSurjective

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out

attribute [local instance] SplitExt.free SplitExt.finite

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

namespace GtPt

variable {D F}

end GtPt

namespace Qk

variable {D F} {k : ℕ}

end Qk

end GlobalTheory.IndefiniteRowSideFullHecke.TorusPointForms
