module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasWeil
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.OmegaUpDownForms
public import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.StarPurelyImaginaryEqNeg
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct

namespace GlobalTheory.WeilTieCompare

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

end GlobalTheory.WeilTieCompare

end
