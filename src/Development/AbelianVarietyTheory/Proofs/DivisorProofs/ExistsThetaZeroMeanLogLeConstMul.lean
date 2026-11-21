import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SignedLogMeans
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaZeroMeanLogNormConjugatesOfWeber
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatticePeriodEtaObj
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ThetaWeberStatement

section
open Formalism.BasicNotions

namespace GlobalTheory.Theta0MeanLeC

theorem theta0MeanLeC : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D :=
  (GlobalTheory.T.thetaZero_mean_log_norm_conjugates_of_weber GlobalTheory.LatticePeriodEtaObj.latticePeriodEta_obj GlobalTheory.ThetaWeberObj.thetaWeberStatement).1.2.2

end GlobalTheory.Theta0MeanLeC
end

open Formalism.BasicNotions
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaZeroMeanLogLeConstMul : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : Formalism.BasicNotions.D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D := by
  atlas_forward_decl GlobalTheory.Theta0MeanLeC.theta0MeanLeC
