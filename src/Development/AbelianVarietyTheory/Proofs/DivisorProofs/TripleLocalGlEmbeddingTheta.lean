module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroComplementaryAdelicSchwartzFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentConjugationSignStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalWeylElementDoubledStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelLocalGoodPlaceStatement

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.DblSwap

section Groups

variable {R E : Type} [CommRing R] [CommRing E] [Algebra R E] (c : E →ₐ[R] E) {β : Type} [Fintype β] [DecidableEq β]
  {J : Matrix β β E}

end Groups

section Local

variable {F : Type} [Field F] [NumberField F]

end Local

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open GlobalTheory.SplitWeil GlobalTheory.SplitFlip

end GlobalTheory.DblSwap

namespace GlobalTheory.DblSwap
open Matrix

end GlobalTheory.DblSwap
