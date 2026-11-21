import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RestrictionInclusions.RHofIncl

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
namespace RestrictedLevelComparison


end RestrictedLevelComparison

variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

namespace RestrictedLevelComparison


end RestrictedLevelComparison


end CrystallineSemistableComparison.Pb.Kap
