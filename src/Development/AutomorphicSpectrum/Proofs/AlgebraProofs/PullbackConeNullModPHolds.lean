import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PPullConeNullModP
import BuildAid.ForwardExisting

section
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem pullConeNullModP : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement :=
  GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.proof

end GlobalTheory.CompanionTheory.Ar.Giv
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_cone_null_mod_p_holds : GroundTheory.Heights₂.Heights.HilbertSamuel.PullConeNullModP.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Giv.pullConeNullModP
