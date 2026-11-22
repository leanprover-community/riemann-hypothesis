module

public import Formalism.LocalToGlobal.Columns.TiedXp
public import Formalism.LocalToGlobal.Columns.TiedVal
public import Formalism.LocalToGlobal.Columns.TiedValRat
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.BaseLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Col
