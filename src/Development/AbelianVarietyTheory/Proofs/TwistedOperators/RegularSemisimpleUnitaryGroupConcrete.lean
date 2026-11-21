import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleOf

section
namespace GlobalTheory.RegSSObj

theorem regularSemisimple : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple :=
  GlobalTheory.RegSS.regularSemisimple

end GlobalTheory.RegSSObj
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularSemisimple_unitaryGroup_concrete : GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.RegularSemisimple := by
  atlas_forward_decl GlobalTheory.RegSSObj.regularSemisimple
