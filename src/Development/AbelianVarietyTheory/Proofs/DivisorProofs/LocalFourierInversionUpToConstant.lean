module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementHasRationalWeilOperatorAdelicFourier
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierBijOnSchwartzBruhatFinitePlace

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section
namespace GlobalTheory.FourierLocInv

section General
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

end General

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end GlobalTheory.FourierLocInv
