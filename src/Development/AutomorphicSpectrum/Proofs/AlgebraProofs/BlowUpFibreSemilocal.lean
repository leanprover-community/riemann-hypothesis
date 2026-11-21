import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSBlowupfibre
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} :=
  PositivityTheory.Xgn.t_s_blowupfibre

end GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.blow_up_fibre_semilocal : GroundTheory.Heights₂.Heights.NumbersDVR.BlowUpFibreSemilocal.Statement.{0} := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.BlowUpFibre.main
