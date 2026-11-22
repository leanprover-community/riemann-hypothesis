module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksSubOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.KSplit
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open scoped Matrix Kronecker

noncomputable section

namespace GlobalTheory.DblSiegelScal

open Matrix MeasureTheory

section Algebra

variable {K : Type} [CommRing K] {β : Type} [Fintype β] [DecidableEq β]

end Algebra

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

end Local

section Adelic

open GlobalTheory.SplitGLLift GlobalTheory.SplitIdele GlobalTheory.DblScal
open GlobalTheory.Div.CoordOpp (piW_cA incM_map_piW)
open scoped GlobalTheory.VacAny

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl (F := F)}

end Adelic

open GlobalTheory.DblScal GlobalTheory.SplitIdele
open scoped GlobalTheory.VacAny

end GlobalTheory.DblSiegelScal

end
