module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.HkEqUOp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Link
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqTheta
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SphericalRepGLExistsSatakeParameters
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantOrbit

@[expose] public section

open NumberField IsDedekindDomain ValuativeRel Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]

variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]

end General

attribute [local instance] val_nontrivial

section Lev

open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

end Lev

