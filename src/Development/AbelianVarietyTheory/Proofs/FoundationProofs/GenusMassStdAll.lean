module

public import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdOfLandherrHasse
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LandherrHasse

@[expose] public section

open Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory

theorem genusMassStd_all : ∀ D : D7, GenusMassStd D :=
  genusMassStd_of_landherrHasse DefiniteOrthonormal.landherrHasse

end GlobalTheory
