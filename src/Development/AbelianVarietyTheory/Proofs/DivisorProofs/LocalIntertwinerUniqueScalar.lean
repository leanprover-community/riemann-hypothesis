module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingTrRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdditiveHomogeneousOperatorLinear
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergInnerPreserving
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLinearOperatorL2Isometry

@[expose] public section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeilTr MeasureTheory
open scoped Matrix ENNReal

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CompactOpenLattice

open Filter Topology GlobalTheory.SchurLin ComplexConjugate

section Lat

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {κ : Type} [Fintype κ]

end Lat

section Gen

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

variable (Q : (V → ℂ) → (V → ℂ) → ℂ)

end Gen

section Loc

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Invertible (2 : K)] {κ : Type} [Fintype κ]

end Loc

section Main

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Invertible (2 : K)] {κ : Type} [Fintype κ]

end Main

end GlobalTheory.CompactOpenLattice

