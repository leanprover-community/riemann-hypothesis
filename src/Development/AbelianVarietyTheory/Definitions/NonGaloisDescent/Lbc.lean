module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsOrbitProd
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsLevelProjLevelProj

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.LocGL

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.FunExt

end GlobalTheory.FunExt

end
