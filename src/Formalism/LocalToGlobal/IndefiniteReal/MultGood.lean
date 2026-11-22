module

public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.HeckeThetaElements.DefsWt

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.NTheta

namespace Formalism.IndefR.Mult

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.IndefR.Mult
