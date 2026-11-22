module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepsOnto

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate

namespace GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section OfTower

variable (W : GlobalTheory.Core.Rk.Tower D)

end OfTower

end GlobalTheory.ChainOnto

end
