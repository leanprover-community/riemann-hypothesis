module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.SpectralTiesReal
public import Formalism.LocalToGlobal.HilbertRowConditions.RowPin
public import Formalism.LocalToGlobal.RatioJoints.CharacterProductEqOne
public import Formalism.LocalToGlobal.UnitaryNorms.DatumS
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeilEq
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InstExists

@[expose] public section

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting

namespace Formalism.L2.SG.SpectralTiesReal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl K Yd cX}

end Formalism.L2.SG.SpectralTiesReal
