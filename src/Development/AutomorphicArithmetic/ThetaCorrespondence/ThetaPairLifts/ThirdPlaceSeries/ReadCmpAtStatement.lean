import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlaceStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ReadCmpAt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.BigOn.Exp.SerBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readCmpAt_of_serBase : _root_.GlobalTheory.BigOn.Exp.SerBase.ReadComparisonAt := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.SerBase.readCmpAt_alt
end
