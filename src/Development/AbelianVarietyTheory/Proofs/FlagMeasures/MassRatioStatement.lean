import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelMassRatioUnimodularDefinite

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_massRatio_unimodular_definite : Formalism.HermitianLatticesTheory.SiegelMassRatio := by
  first | exact @GlobalTheory.Mass.siegelMassRatio_holds | exact GlobalTheory.Mass.siegelMassRatio_holds | (intros; apply GlobalTheory.Mass.siegelMassRatio_holds <;> assumption)
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory.MassAtRecord

theorem massRatio_at_record : ∀ D : D7, UnitaryVolumeMass.stMassRatio D := fun D => by
  letI := D.host.cmStar
  exact fun j hj V V' _ _ _ _ _ _ _ _ f f' L L' hs hs' ho ho' =>
    GlobalTheory.T.siegel_massRatio_unimodular_definite D.host.E D.sp.cm.cmUnram j hj V V' f f' L L' hs hs' ho ho'

end GlobalTheory.MassAtRecord
end
