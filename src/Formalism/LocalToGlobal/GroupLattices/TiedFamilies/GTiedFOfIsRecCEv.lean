module

public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.FullTiedCBase
public import Formalism.LocalToGlobal.GroupLattices.LinkGConcreteNoKer
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.IntSplitOf
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.RecThm
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.TieIwLevTieOf
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.CmpHyp0P
public import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.SelfDualAtColLevel

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G NumberField IsDedekindDomain Formalism.UG Formalism.L2.Forms

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

end Formalism.L2.G
