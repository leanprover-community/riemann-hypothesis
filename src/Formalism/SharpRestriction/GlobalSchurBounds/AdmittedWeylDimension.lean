module

public import Formalism.SharpRestriction.GlobalSchurBounds.TheoremThreeOfExplicitAndCompact
public import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
public import Formalism.SharpRestriction.ParamsHeightRankConstant

@[expose] public section

noncomputable section

namespace Formalism.MainNotions.StandardLattice

open NumberField Formalism.BasicNotions Finset Formalism.MainNotions.S
open scoped TensorProduct

attribute [instance] ColRep.nacg ColRep.ips

section Fam

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

end Fam

end Formalism.MainNotions.StandardLattice
