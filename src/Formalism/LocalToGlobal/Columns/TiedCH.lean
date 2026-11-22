module

public import Formalism.LocalToGlobal.Columns.TiedRec
public import Formalism.LocalToGlobal.HermitianColumns.ColsHerm

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CH

open Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abbr

variable (D : ColRec) (u : D.what₂.Word)

end Abbr

end Formalism.L2.Col.CH

end
