import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeAtHoldsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SizeAtAltAlt

set_option synthInstance.maxHeartbeats 200000

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.size_at' : _root_.GlobalTheory.BigTop.Fun.SizeAtAlt := by
  atlas_forward_decl _root_.GlobalTheory.BigTop.Fun.SizeProof.sizeAt_alt
end
