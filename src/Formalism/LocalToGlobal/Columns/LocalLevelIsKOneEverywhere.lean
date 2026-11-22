module

public import Formalism.LocalToGlobal.Columns.ExistsPlaceOverFirstPrime
public import Formalism.LocalToGlobal.Columns.TiedGlPl

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

end Formalism.L2.Col
