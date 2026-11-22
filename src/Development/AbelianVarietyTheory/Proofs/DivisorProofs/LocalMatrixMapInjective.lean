module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.DblScal
open scoped Matrix

noncomputable section

namespace GlobalTheory.DblScal

open Matrix

end GlobalTheory.DblScal

end
