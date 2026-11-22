module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
public import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasurableThetaSumOfSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzMemL2
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun MeasureTheory Topology
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

open Filter
open scoped ENNReal NNReal

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

section Meas

variable (v : Pl (F := F)) (r : (κ → AF F) → ℂ)
  (hr : ∀ x z, At (evFin F v) z → r (x + z) = r x)
  (hS : ∀ ψ ∈ SB (κ → Fv F v), tens (evFin F v) ψ r ∈ schA F κ)

end Meas

end GlobalTheory.LocalUnitaryL2

namespace GlobalTheory.LocalUnitaryL2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

end GlobalTheory.LocalUnitaryL2

