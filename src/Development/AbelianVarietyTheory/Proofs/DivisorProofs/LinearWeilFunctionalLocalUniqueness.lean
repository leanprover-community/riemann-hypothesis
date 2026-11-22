module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedProjectionPreservesSchwartzAdmStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartialEvaluationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxProductDiagonalFunctionalNeZeroStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctionalStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnitStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValueStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalNormUnramifiedFactorizationStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.LatVac
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.MixedForm

section Abstract

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Abstract

section Proj

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

end Proj

section Mixed

variable {R : Type} [CommRing R] [Invertible (2 : R)] {E : Type} [CommRing E] [Algebra R E] {c : E →ₐ[R] E}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Mixed

section Place

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}

variable {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Place

section Linear

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

end Linear

end GlobalTheory.MixedForm

end
