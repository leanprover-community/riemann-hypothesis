module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
public import Formalism.LocalToGlobal.ProjectiveLattices.LiftLaSpec
public import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
public import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

attribute [local instance 2000] Submodule.module

end GlobalTheory.IndefiniteRowSideFullHecke.LevelGroupLifts
