module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectors
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies GlobalTheory.CentralOps
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing
