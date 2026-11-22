module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapInjectiveStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMapSurjectiveStatement

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblScalDet

open GlobalTheory.DblScal
open scoped Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.DblScalDet

