module

public import Formalism.LocalToGlobal.Columns.TiedCH
public import Formalism.LocalToGlobal.Columns.TiedCB

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : ColRec}

variable (u : D.what₂.Word)

variable {u} (A : CF.AtTTied u) (P : ∀ i hi, CF.LvTied u A i hi)

end Formalism.L2.Col
