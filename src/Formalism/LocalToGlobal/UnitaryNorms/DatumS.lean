module

public import Formalism.LocalToGlobal.UnitaryNorms.CharGal
public import Formalism.LocalToGlobal.JointCharacters.SameChr
public import Formalism.LocalToGlobal.HilbertRowConditions.KaTiedIffKapDef
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TwoPowS0EqTwoPartModulus
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.HeckeStdTwOfStd
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingSpecSidedEmbeddingFixedField
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.ValLeOneOfIsIntegral
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Choice
public import Formalism.LocalToGlobal.LocalInduction.BridgeInd
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP
public import Formalism.SharpRestriction.PageFix
public import Formalism.SharpRestriction.Divisibility.SmallFirstModulusBelowScale
public import Formalism.SharpRestriction.LevelLetterCocycles.AlignN
public import Formalism.LocalToGlobal.UnitaryNorms.DefsDatum

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions

namespace Formalism.L2

namespace Host

local instance nfOfFinHD (L : Fld) [FiniteDimensional ℚ L] : NumberField L := {}

def UnramOverE {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : Fld) [hL : FiniteDimensional ℚ L] : Prop :=
  (NumberField.discr L).natAbs = (NumberField.discr H.E).natAbs ^ (Module.finrank ℚ L / Module.finrank ℚ H.E)

def IsHilbertCFE {R : Ranks} (H : Formalism.BasicNotions.Host R) (L : Fld) [hL : FiniteDimensional ℚ L] : Prop :=
  Rows.AbelOver (H.EQ) L ∧ UnramOverE H L ∧
    ∀ (L' : Fld) [FiniteDimensional ℚ L'], Rows.AbelOver (H.EQ) L' → UnramOverE H L' → L' ≤ L

end Host

section

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : MainNotions.G.Inst D L} {Gl : MainNotions.G.LatInst D} {K : MainNotions.G.Consts} {Y : DivX D}
  {cX : ExtraC}

end

end Formalism.L2
