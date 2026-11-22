module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.MeasureEqRelIndexMul
public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IwasawaMeasureExistence.LeviSizesMeasurable

@[expose] public section

noncomputable section

namespace PI.IwaMeasEx.MFI

open MeasureTheory Measure NumberField
open scoped ENNReal NNReal TensorProduct
open Formalism.MainNotions.S Formalism.L2.S.S7.GLOne PI.IwaMeasEx.Nrm

section

variable (I : AutInst)

attribute [local instance] AfT.tAf Nrm.topRing Nrm.t2 Nrm.mAf Nrm.borel_mAf

attribute [local instance] locallyCompact_AEf

end

end PI.IwaMeasEx.MFI

end
