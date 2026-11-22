module

public import Formalism.LocalToGlobal.Columns.TiedCH
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Col.CF

end
