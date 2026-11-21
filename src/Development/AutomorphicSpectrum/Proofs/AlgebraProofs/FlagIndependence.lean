import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSFlagindep

section
namespace GlobalTheory.CompanionTheory.CommAlg.FlagIndependence

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement :=
  PositivityTheory.Xgn.A_s_flagindep.of_items GlobalTheory.CompanionTheory.CommAlg.VerticalDivisors.verticalDivisorsCommute
    GlobalTheory.T.pair_number_pullback GlobalTheory.T.exists_heckeCorrespondence_on_integral_shimuraModel

end GlobalTheory.CompanionTheory.CommAlg.FlagIndependence
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_independence : GroundTheory.Heights₂.Heights.NumbersDVR.FlagIndependence.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.FlagIndependence.main
