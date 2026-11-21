import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSJoinright

section
namespace GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement :=
  PositivityTheory.Xgn.A_s_joinright.of_pullback GlobalTheory.T.pair_number_pullback

end GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_model_join_right : GroundTheory.Heights₂.Heights.NumbersDVR.FlagModelJoinRightAlt.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.FlagModelJoinRight.main
