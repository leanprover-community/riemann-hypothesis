module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.L2.DIV
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end GlobalTheory.IndefiniteRowSideFullHecke.LinearCoefficientData

end
