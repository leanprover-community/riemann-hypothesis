import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FieldExtensionIntersectionInvariance
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.XSPullback

section
namespace GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback

theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement :=
  PositivityTheory.Xgn.t_s_pullback

end GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_number_pullback : GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberPullback.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.Ar.Num.PairNumberPullback.main
