module

public import Mathlib
public import Formalism.LocalToGlobal.HermitianForms.ExtraSym
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSym
public import Formalism.LocalToGlobal.HermitianForms.TiedBr
public import Formalism.LocalToGlobal.GroupLattices.StdSubAtOfRing
public import Formalism.LocalToGlobal.GroupLattices.Joint0
public import Formalism.LocalToGlobal.HilbertRowConditions.TiedEMt
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
public import Formalism.LocalToGlobal.KernelLattices.KerChTie
public import Formalism.LocalToGlobal.KernelLattices.KerMemPin
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.AdaptedEnt
public import Formalism.LocalToGlobal.UnitaryNorms.CharTied
public import Formalism.LocalToGlobal.UnitaryNorms.CharTransport
public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil
public import Formalism.LocalToGlobal.GlobalTheory.LinkTiesOm
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ReferenceCharactersFactorTame
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

@[expose] public section

noncomputable section

namespace GlobalTheory.Core.Cls

open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 NumberField IsDedekindDomain Matrix Formalism.UG

def RootsG (D : D7) : Prop :=
  ∀ i, (∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i)) ∧ ∃ ζ : D.what₂.LL, IsPrimitiveRoot ζ (D.host.g i - 1)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {K : G.Consts} {Y : DivX D} {cX : ExtraC}

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {ex : Extra D L hT Gi Gl K Y cX}

end GlobalTheory.Core.Cls

end
