module

public import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
public import Formalism.LocalToGlobal.Columns.TiedLv

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word)

end Gen

variable {d : ColDat} (a : ColArgs d)

end Formalism.L2.Col
