module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SchurCharV

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

end GlobalTheory.SchurCharV

