module

public import Formalism.LocalToGlobal.Columns.ValuationPosIffMemSeen
public import Formalism.LocalToGlobal.Columns.LocalLevelIsKOneEverywhere
public import Formalism.LocalToGlobal.Columns.RecLevelLocK
public import Formalism.LocalToGlobal.Columns.RecLevelLocT

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {d : ColDat} (a : ColArgs d)

section Asm

variable (hS : SpStd d.toColBase) (hH : HostHyp d) (hP : PtSurj d) (hK : LocalLevelIsKOneEverywhere d) (S : GSplit (Pr := d.Pr) d.sp.cm) (hI : IwAll d S)
  (O : AtTOwed a hS hH)

end Asm

end Formalism.L2.Col
