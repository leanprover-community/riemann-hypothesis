module

public import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.InVolumesAtOfSWS
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SiegelWeilVolumes
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CovolumeFrames.StepSize

@[expose] public section

namespace GlobalTheory.St

theorem swxs_of_siegelWeil :
    HeckeCharacterZeroLocus.SiegelWeilU.SiegelWeilUnitaryConvergent → PI.VolStabS.MassDataS.SWXS :=
  fun h _ X => GlobalTheory.St.siegelWeil_volumes h _ _ _ (MassDataVolumesW.stepCM X) _ _ (MassDataVolumesW.stepHerm X)

end GlobalTheory.St
