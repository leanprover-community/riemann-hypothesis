module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

end
