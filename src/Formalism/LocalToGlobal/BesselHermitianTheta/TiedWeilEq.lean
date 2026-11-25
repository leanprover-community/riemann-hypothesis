module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open scoped TensorProduct ContDiff

namespace Formalism.L2.Theta

variable {D : D7}

structure WeilCompatibleEquivariance {X : ThetaX D} {T : ThetaTied D X} (Wl : WeilTied D X T) : Prop where

end Formalism.L2.Theta

end
