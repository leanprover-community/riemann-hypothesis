module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamilyStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectorsStatement
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunctionStatement

@[expose] public section

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

end GlobalTheory.CentralOps
