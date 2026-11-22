module

public import Formalism.LocalToGlobal.Columns.HxMemMap

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec} {u : D.what₂.Word} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

end Formalism.L2.Col
