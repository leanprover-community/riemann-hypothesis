module

public import Formalism.LocalToGlobal.Columns.TiedXpV
public import Formalism.LocalToGlobal.Columns.TiedAtT
public import Formalism.LocalToGlobal.Columns.RowFormsGood

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

end Gen

section Rec

variable {d : ColDat} (a : ColArgs d)

end Rec

end Formalism.L2.Col
