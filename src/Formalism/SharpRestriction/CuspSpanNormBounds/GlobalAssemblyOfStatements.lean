module

public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.ParConsts

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusGlobal

export Formalism.MainNotions.S.UnitaryVolumeMass (DefiniteComplementRank Lem1 Lem2 LatticeSpanEquality ThmA HyperplaneEquality ThmB)

open NumberField Formalism.BasicNotions Formalism.MainNotions.S.Lat Module

def adm1 (D : D7) : Prop :=
  S.UnitaryVolumeMass.stGlue D

section Fam
variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.VanishingOnXAndXPlusGlobal

end
