module

public import Formalism.LocalToGlobal.ProjectiveLattices.EtArch
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtData
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtPf

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Torus

open ReciprocityTheory.ChartRestriction.G.I2

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

end Torus

variable {D : D7} {T : Top D} (h : LawsP T)

end Formalism.L2.Pj
