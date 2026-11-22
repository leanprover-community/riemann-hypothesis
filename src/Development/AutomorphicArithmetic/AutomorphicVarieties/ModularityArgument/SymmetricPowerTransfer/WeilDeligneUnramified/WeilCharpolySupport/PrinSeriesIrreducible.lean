module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnlFull
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars

@[expose] public section

noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.W

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end Loc

end UpperTheory.V.Z.Sym.W
