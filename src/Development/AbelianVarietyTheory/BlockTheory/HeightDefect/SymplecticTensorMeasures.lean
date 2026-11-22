module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedKfin
public import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

namespace ConjIsom

variable {V : HSp D} (s : ConjIsom V)

end ConjIsom

variable {X : ThetaX D} {T : ThetaTied D X} {Wl : WeilTied D X T}

end GlobalTheory.IndefiniteRowSideFullHecke.SymplecticTensorMeasures

end
