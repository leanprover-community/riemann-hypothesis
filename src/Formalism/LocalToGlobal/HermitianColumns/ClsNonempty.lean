module

public import Formalism.LocalToGlobal.HermitianColumns.CoordinateLatticeSelfDual
public import Formalism.LocalToGlobal.HermitianColumns.CocycleZeroMemInvariants

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Herm

end
