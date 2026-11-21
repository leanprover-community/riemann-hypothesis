import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LatSmallGenAltAlt

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.latSmallGen' : _root_.GlobalTheory.BigOn.Exp.LatticeHasSmallGenerators := by
  atlas_forward_decl _root_.GlobalTheory.BigOn.Exp.latSmallGen_alt
end
