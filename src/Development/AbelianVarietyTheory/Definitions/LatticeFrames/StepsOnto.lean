module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

@[expose] public section

set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct

namespace GlobalTheory.Core.Rk

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace Tower

variable {D : D7} (W : Tower D)

end Tower

end GlobalTheory.Core.Rk

end
