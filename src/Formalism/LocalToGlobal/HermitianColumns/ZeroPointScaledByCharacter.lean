module

public import Formalism.LocalToGlobal.HermitianColumns.ClsNonempty
public import Formalism.LocalToGlobal.HermitianColumns.Lev0Tied

@[expose] public section

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Herm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def StdTied (D : D7) : Prop :=
  (∀ i, i ≤ D.R.m → IsStd (D.sp.X i)) ∧ IsStd D.sp.X'

def PositiveVolumeCompatible (D : D7) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → D.sp.Vneg j = false

end Formalism.L2.Herm

end
