module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LocWSOf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.VolPin
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacobianCoordinates
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MemConfTOfDetNeZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniquePlace
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension

@[expose] public section

noncomputable section
open scoped Classical ENNReal
open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace GlobalTheory.CovDom

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D)

end GlobalTheory.CovDom
