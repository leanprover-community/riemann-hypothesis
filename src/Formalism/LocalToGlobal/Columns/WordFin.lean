module

public import Formalism.LocalToGlobal.Columns.TiedRec
public import Formalism.LocalToGlobal.Columns.Record
public import Formalism.LocalToGlobal.Columns.RecLevelStep
public import Formalism.LocalToGlobal.Columns.RowFormsLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar

attribute [instance] ColBase.wordFin ColBase.nfLL ColBase.starLL

namespace ColBase

variable (B : ColBase)

end ColBase

namespace ColDat

variable (d : ColDat) (a : ColArgs d)

end ColDat

end Formalism.L2.Col
