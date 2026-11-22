module

public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory
open scoped TensorProduct

namespace Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Theta

end
