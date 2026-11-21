import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PLiftGraphFactor
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSectionNormSqExtension
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviLogFlat
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviHolPerturb
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviCompHol
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PLeviFSInvariant

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

theorem SectionNormSqExtension.closed : SectionNormSqExtension.Statement :=
  SectionNormSqExtension.proof LeviLogFlat.proof LeviHolPerturb.proof LeviCompHol.proof LeviFSInvariant.proof

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

theorem LiftGraphFactor.closed : LiftGraphFactor.Statement :=
  LiftGraphFactor.proof GroundTheory.Heights₂.Heights.HilbertSamuel.SectionNormSqExtension.closed

end GroundTheory.Heights₂.Heights.Targets
end
