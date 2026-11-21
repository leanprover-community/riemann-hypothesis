import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.UnitaryTwoForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.HkEqUOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Link
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwThetaEx

open NumberField IsDedekindDomain ValuativeRel Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL Formalism.BasicNotions
open UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict

section General

variable {G V : Type} [CommGroup G] [AddCommGroup V] [Module ℂ V]




variable [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace.SeparableSpace G]


end General


private theorem val_nontrivial {k : Type} [Field k] [ValuativeRel k] : Nontrivial (ValueGroupWithZero k) :=
  GroupWithZero.toNontrivial

attribute [local instance] val_nontrivial

section Lev

open GlobalTheory.IwahoriInj GlobalTheory.IwahoriTraceProof

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}










end Lev

