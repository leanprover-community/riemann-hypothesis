module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCharacterOfTrivialNearOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts

@[expose] public section

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Filter Topology
