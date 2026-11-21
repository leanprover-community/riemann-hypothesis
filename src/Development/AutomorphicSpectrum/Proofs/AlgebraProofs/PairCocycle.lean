import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PPairCocycle
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.OfSteps
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.VerticalDivisorsCommuteStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependence

section
namespace GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed

open GroundTheory.Heights₂.Heights.NumbersDVR

theorem pairCocycle : PairCocycle.Statement :=
  PairCocycle.proof GlobalTheory.T.flag_independence GlobalTheory.T.vertical_divisors_commute IntNumAddFirst.full

end GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed
end

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pair_cocycle : GroundTheory.Heights₂.Heights.NumbersDVR.PairCocycle.Statement := by
  atlas_forward_decl GlobalTheory.CompanionTheory.CommAlg.PairCocycleClosed.pairCocycle
