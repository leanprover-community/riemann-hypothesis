module

public import Formalism.LocalToGlobal.Columns.HermOwed
public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.Columns.TiedXp
public import Formalism.LocalToGlobal.Columns.TiedGlPl
public import Formalism.LocalToGlobal.Columns.TiedGlMat
public import Formalism.LocalToGlobal.Columns.RecLevelDiv
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.HermitianForms.DefsChi

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

end Formalism.L2.Col
