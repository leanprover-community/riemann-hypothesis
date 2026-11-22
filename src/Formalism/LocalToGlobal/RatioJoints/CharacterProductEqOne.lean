module

public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Formalism.LocalToGlobal.RatioJoints.IsRatioAt
public import Formalism.LocalToGlobal.UnitaryNorms.CharDiv
public import Formalism.LocalToGlobal.JointCharacters.SameChr

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.UG
open scoped TensorProduct

namespace Formalism.L2

open Formalism.L2.Joints

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

namespace JointsS

variable {ex : Extra D L hT Gi Gl K Y cX} {T : LinkedFamilyData ex}

end JointsS

section

end

end Formalism.L2

end
