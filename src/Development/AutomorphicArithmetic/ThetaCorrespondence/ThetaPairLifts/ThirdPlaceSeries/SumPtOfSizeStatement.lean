import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPointOfSizeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SumPtOfSize

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.RefSum GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_pt_of_size : _root_.GlobalTheory.CovTop.SizeCondition → _root_.GlobalTheory.RefSum.SumPtAlt := by
  atlas_forward_decl _root_.GlobalTheory.RefSum.sumPt_of_size_alt
end
