module

public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.ModDepthGE
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe

@[expose] public section

namespace ReciprocityTheory.CA

theorem isCM_of_isRegularLocalRing (R : Type*) [CommRing R] [IsRegularLocalRing R] : IsCM R :=
  GlobalTheory.isCM_of_isRegularLocalRing R

end ReciprocityTheory.CA
