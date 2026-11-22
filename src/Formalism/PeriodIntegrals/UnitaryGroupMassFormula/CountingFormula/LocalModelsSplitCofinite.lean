module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DensMultOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.DensExact

@[expose] public section

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula

open NumberField Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.CntLocal IsDedekindDomain
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end PI.UnitaryGroupMassFormula.CntFormula
