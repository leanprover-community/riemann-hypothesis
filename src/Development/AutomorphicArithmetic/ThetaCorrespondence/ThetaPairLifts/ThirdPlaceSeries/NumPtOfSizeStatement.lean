import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NumericalPointOfSizeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NumPtOfSize

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.numerical_point_statement_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.NumPtAlt := by
  atlas_forward_decl _root_.GlobalTheory.RefSum.NumSizes.numPt_of_size'
end
