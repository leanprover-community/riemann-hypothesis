module

public import Formalism.LocalToGlobal.NumberFieldFamilies.ThetaCP
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.BesselHermitianTheta.BesselUnipotentSubgroup

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff

namespace Formalism.L2.Fam.ThC

open Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.MainNotions.Inhab

variable {D : D7}

attribute [instance] Free.fjAdd Free.fjMod

variable {ψ : AddChar (AF D.host.F) ℂ}

section Ties

variable (G : FormGaps D) (P : PerGaps ψ) (hE : ExpU D) (Om : WeilC ψ) (c : ChrIn D) (f : Free Om)

end Ties

end Formalism.L2.Fam.ThC

end
