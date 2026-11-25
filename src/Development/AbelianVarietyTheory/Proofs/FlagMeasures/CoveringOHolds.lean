module

public import Formalism.FlagUnipotentLattices.CardSubmodulesAndLinearEquivBounds
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransferenceCoverHolds
public import Formalism.FlagUnipotentLattices.CardSubgroupsOfIndexLe

@[expose] public section

namespace GlobalTheory

theorem coveringO_holds : Formalism.HermitianLatticeCounting.LatticeSumBounds.CoveringO := by
  apply _root_.Formalism.HermitianLatticeCounting.P.coveringO_of_transference
  intro E _ _ _ Λ _ _ lam hlam hdual x
  exact transferenceCover_holds E Λ lam hlam hdual x

end GlobalTheory
